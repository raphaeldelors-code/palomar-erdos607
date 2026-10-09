module

public import Mathlib.Data.Nat.Basic

namespace Erdos607

theorem sanity_check (n : ℕ) : n + n = 2 * n := by
  exact (Nat.two_mul n).symm

end Erdos607
