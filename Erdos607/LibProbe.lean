module

import Mathlib

open Set Finset

namespace LP

noncomputable def mk (n : ℕ) : Finset ℕ := Finset.range n

theorem mkthm (n : ℕ) : (mk n).card = n := by simp [mk]

end LP
