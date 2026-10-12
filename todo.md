# todo.md

## [2026-10-12] [TODO] Enforce permitted_axioms as a local CI gate
- `check-lean-sources.py`: detect any `axiom` declaration in tracked `.lean`
  (comment/string-aware) and require `comparator.json` to pin a non-empty
  `permitted_axioms` whitelist. Fails fast on push/PR before a 60-min build or
  a submission attempt is wasted. Does NOT touch the registered math artifact
  (pinned at 30436bf).
- Verify: script exits 0 on the current tree (zero axioms, whitelist present);
  detector catches a synthetic `axiom` and ignores `--`/`/- -/`/`"..."` mentions.
