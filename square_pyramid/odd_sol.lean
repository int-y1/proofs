-- https://en.wikipedia.org/wiki/Cannonball_problem
-- reference is doi:10.2307/2323911
-- this is an in-progress attempt at formalizing the proof

import Mathlib.Data.Int.ModEq
import Mathlib.NumberTheory.PellMatiyasevic

def u (n : ℕ) : ℤ := Pell.xz (by decide : 1 < 2) n
def v (n : ℕ) : ℤ := Pell.yz (by decide : 1 < 2) n

variable {m n r : ℕ}

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

/-- Lemma 7. I have no idea how to name this lemma. -/
theorem lemma7 (h : n ≤ 2 * r * m) :
    u (2 * r * m - n) ≡ (-1) ^ r * u n [ZMOD u m] ∧
    u (2 * r * m + n) ≡ (-1) ^ r * u n [ZMOD u m] := by
  have hv2m : v (2 * m) ≡ 0 [ZMOD u m] := by
    rw [two_mul, v_add, ← left_distrib, Int.modEq_zero_iff_dvd]; apply dvd_mul_right
  have hu : ∀ r, u ((2 * r + 1) * m) ≡ 0 [ZMOD u m] ∧ v (2 * r * m) ≡ 0 [ZMOD u m] := by
    intro r
    induction' r with r hr
    · rw [Nat.mul_zero, zero_add, one_mul, zero_mul, Int.ModEq, Int.emod_self]; trivial
    constructor
    · rw [Nat.mul_succ, (by ring : (2 * r + 2 + 1) * m = (2 * r + 1) * m + 2 * m), u_add]
      convert (hr.1.mul_right (u (2 * m))).add (hv2m.mul_left (3 * v ((2 * r + 1) * m)))
      simp
    · rw [Nat.mul_succ, right_distrib, v_add]
      exact (hv2m.mul_left (u (2 * r * m))).add (hr.2.mul_left (u (2 * m)))
  have : u (2 * r * m) ≡ (-1) ^ r [ZMOD u m] := by
    have := u_two_mul (m := r * m)
    rcases r.even_or_odd with ⟨r', hr'⟩ | ⟨r', hr'⟩
    · rw [Even.neg_pow ⟨r', hr'⟩, one_pow, mul_assoc, this.2, hr', ← two_mul]
      exact (((hu r').2.pow 2).mul_left 6).add_right 1
    · rw [Odd.neg_pow ⟨r', hr'⟩, one_pow, mul_assoc, this.1, hr']
      exact (((hu r').1.pow 2).mul_left 2).sub_right 1
  constructor
  · rw [u_sub h]
    convert (this.mul_right (u n)).sub (((hu r).2.mul_left 3).mul_right (v n)) using 1
    rw [mul_zero, zero_mul, sub_zero]
  · rw [u_add]
    convert (this.mul_right (u n)).add (((hu r).2.mul_left 3).mul_right (v n)) using 1
    rw [mul_zero, zero_mul, add_zero]





