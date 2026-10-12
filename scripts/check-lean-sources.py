#!/usr/bin/env python3
"""Check source requirements before builds; full Palomar verification is still required.

Scanner functions follow PalomarSubmission/scripts/source_requirements.py.
"""
import json
import os
import re
from pathlib import Path

COMMENT_MARKER = re.compile(r"/-|-/")
# Lean 4 Init/Meta/Defs.lean identifier characters; Python Unicode classes
# are broader. A qualified identifier also continues across a dot.
ID_LETTER_LIKE = (
    r"\u03b1-\u03ba\u03bc-\u03c9\u0391-\u039f\u03a1-\u03a2\u03a4-\u03a9"
    r"\u03ca-\u03fb\u1f00-\u1ffe\u2100-\u214f\U0001d49c-\U0001d59f"
    r"\u00c0-\u00d6\u00d8-\u00f6\u00f8-\u017f"
)
ID_FIRST = rf"A-Za-z_{ID_LETTER_LIKE}"
ID_REST = rf"{ID_FIRST}0-9'!?\u2080-\u2089\u2090-\u209c\u1d62-\u1d6a\u2c7c"
IDENTIFIER_CONTINUATION = re.compile(rf"[{ID_REST}]|\.[{ID_FIRST}\u00ab]")


def has_module_header(text: str) -> bool:
    """Recognize the initial marker, without confusing comments with headers.

    Documentation comments are commands, not header whitespace. Do not strip a
    BOM or arbitrary Unicode whitespace: Lean's header parser does not either.
    This cheap check precedes installation; execute confirms with --deps-json.
    """
    index = 0
    while index < len(text):
        if text[index] in " \r\n":
            index += 1
        elif text.startswith("--", index):
            end = text.find("\n", index + 2)
            index = len(text) if end < 0 else end + 1
        elif text.startswith("/-", index) and not text.startswith(("/--", "/-!"), index):
            # Lean consumes the character after the plain opener before
            # scanning its body (unlike nested openers). Match its parser.
            index += 3
            depth = 1
            while depth:
                marker = COMMENT_MARKER.search(text, index)
                if marker is None:
                    break
                depth += 1 if marker.group() == "/-" else -1
                index = marker.end()
            if depth:
                return False
        else:
            return text.startswith("module", index) and (
                IDENTIFIER_CONTINUATION.match(text, index + 6) is None
            )
    return False


def physical_lines(text: str) -> int:
    """LF/CRLF lines; an unterminated final line counts, a final LF adds none."""
    return text.count("\n") + int(bool(text) and not text.endswith("\n"))


def lean_source_files(root: Path) -> list[Path]:
    """Lean source paths, including contained projects and symlinks to reject.

    Lake configuration shares the line cap, but is exempt from module headers.
    Never traverse symlinks or Git internals.
    """
    files = []
    for directory, subdirectories, names in os.walk(root, followlinks=False):
        subdirectories[:] = sorted(
            name for name in subdirectories
            if name not in {".git", ".lake"} and not (Path(directory) / name).is_symlink()
        )
        for name in sorted(names):
            path = Path(directory) / name
            if name.endswith(".lean") and (path.is_symlink() or path.is_file()):
                files.append(path)
    return files


def strip_comments_and_strings(text: str) -> str:
    """Blank comment and string contents (kept as spaces) so a lexical scan sees
    only real code. Offsets and line breaks are preserved.

    Strips `--` line comments, `/- -/` block comments (all variants, nesting
    matches Lean's lexer), and `"..."` string literals (backslash escapes).
    """
    out = list(text)
    n = len(text)
    i = 0

    def blank(start: int, end: int) -> None:
        for m in range(start, end):
            if out[m] != "\n":
                out[m] = " "

    while i < n:
        c = text[i]
        nxt = text[i + 1] if i + 1 < n else ""
        if c == "-" and nxt == "-":                      # line comment
            start = i
            while i < n and text[i] != "\n":
                i += 1
            blank(start, i)
            continue
        if c == "/" and nxt == "-":                      # block comment /- /-! /--
            start = i
            i += 2
            depth = 1
            while i < n and depth:
                if text[i] == "/" and i + 1 < n and text[i + 1] == "-":
                    depth += 1
                    i += 2
                elif text[i] == "-" and i + 1 < n and text[i + 1] == "/":
                    depth -= 1
                    i += 2
                else:
                    i += 1
            blank(start, i)
            continue
        if c == '"':                                     # string literal
            start = i
            i += 1
            while i < n and text[i] != '"':
                if text[i] == "\\" and i + 1 < n:
                    i += 2
                else:
                    i += 1
            if i < n:
                i += 1                                   # consume closing quote
            blank(start, i)
            continue
        i += 1
    return "".join(out)


AXIOM_DECL = re.compile(r"\baxiom\b")


def axiom_declaration_lines(text: str) -> list[int]:
    """1-indexed lines containing an `axiom` declaration in real code.

    `axiom` is a Lean command keyword. The word boundary excludes the print
    command `axioms` and identifiers such as `myAxiom`/`AxiomOfChoice`.
    """
    stripped = strip_comments_and_strings(text)
    return [stripped.count("\n", 0, m.start()) + 1 for m in AXIOM_DECL.finditer(stripped)]


def check_permitted_axioms(root: Path) -> bool:
    """comparator.json must pin a non-empty `permitted_axioms` whitelist.

    The comparator's axiom check is only as strong as the whitelist it is given;
    an empty or missing whitelist would let an `axiom` slide through silently.
    """
    cfg = root / "comparator.json"
    if not cfg.is_file():
        print("comparator.json: missing — the comparator config (with permitted_axioms) is required")
        return False
    try:
        data = json.loads(cfg.read_text(encoding="utf-8"))
    except (json.JSONDecodeError, OSError) as exc:
        print(f"comparator.json: unreadable ({exc})")
        return False
    whitelist = data.get("permitted_axioms")
    if not isinstance(whitelist, list) or not whitelist:
        print("comparator.json: `permitted_axioms` must be a non-empty whitelist of standard axioms")
        return False
    return True


def main() -> int:
    root = Path(__file__).resolve().parents[1]
    failed = False
    for path in lean_source_files(root):
        relative = path.relative_to(root)
        if path.is_symlink():
            print(f"{relative}: must be a regular Lean file, not a symbolic link")
            failed = True
            continue
        try:
            text = path.read_bytes().decode("utf-8")
        except UnicodeDecodeError:
            print(f"{relative}: source is not valid UTF-8")
            failed = True
            continue
        if path.name != "lakefile.lean" and not has_module_header(text):
            print(f"{relative}: must use the module header keyword")
            failed = True
        if physical_lines(text) > 10_000:
            print(f"{relative}: exceeds 10,000 lines; split into smaller modules")
            failed = True
        for line_no in axiom_declaration_lines(text):
            print(
                f"{relative}:{line_no}: declares an `axiom`; the result must rest on "
                "standard axioms only (comparator.json `permitted_axioms`). Prove the "
                "claim, or add the axiom to the whitelist and re-run the comparator."
            )
            failed = True
    if not check_permitted_axioms(root):
        failed = True
    return int(failed)


if __name__ == "__main__":
    raise SystemExit(main())
