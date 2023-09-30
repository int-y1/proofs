-- https://en.wikipedia.org/wiki/Cannonball_problem
-- reference is doi:10.2307/2323911
-- this is an in-progress attempt at formalizing the proof

import Mathlib.NumberTheory.PellMatiyasevic

def u (n : ℕ) : ℤ := Pell.xz (by decide : 1 < 2) n
def v (n : ℕ) : ℤ := Pell.yz (by decide : 1 < 2) n

variable {m n : ℕ}

theorem uv_pell_eq : u m ^ 2 - 3 * v m ^ 2 = 1 := by
  rw [u, v, pow_two, pow_two, ← mul_assoc, ← Pell.pell_eqz (by decide : 1 < 2) m]; rfl

/-- Lemma 4a. -/
theorem u_add : u (m + n) = u m * u n + 3 * v m * v n := by
  dsimp only [u, v, Pell.xz, Pell.yz]; norm_cast; exact Pell.xn_add (by decide) m n

/-- Lemma 4b. -/
theorem v_add : v (m + n) = u m * v n + u n * v m := by
  dsimp only [u, v, Pell.xz, Pell.yz]; norm_cast; rw [Pell.yn_add (by decide) m n]; ring

/-- Lemma 4c. -/
theorem u_sub (h : n ≤ m) : u (m - n) = u m * u n - 3 * v m * v n := by
  dsimp only [u, v]; exact Pell.xz_sub (by decide) h

/-- Lemma 4d. -/
theorem v_sub (h : n ≤ m) : v (m - n) = -u m * v n + u n * v m := by
  dsimp only [u, v]; rw [Pell.yz_sub (by decide) h]; ring

/-- Lemma 5a. -/
theorem u_add_two : u (m + 2) = 2 * u 1 * u (m + 1) - u m := by
  rw [u_add, u_add]; change u m * 7 + 3 * v m * 4 = 2 * 2 * (u m * 2 + 3 * v m * 1) - u m; ring

/-- Lemma 5b. -/
theorem v_add_two : v (m + 2) = 2 * u 1 * v (m + 1) - v m := by
  rw [v_add, v_add]; change u m * 4 + 7 * v m = 2 * 2 * (u m * 1 + 2 * v m) - v m; ring

/-- Lemma 6a. -/
theorem u_two_mul : u (2 * m) = 2 * u m ^ 2 - 1 ∧ u (2 * m) = 6 * v m ^ 2 + 1 := by
  rw [two_mul, u_add, ← uv_pell_eq (m := m)]; constructor <;> ring

/-- Lemma 6b. -/
theorem v_two_mul : v (2 * m) = 2 * u m * v m := by
  rw [two_mul, v_add]; ring






