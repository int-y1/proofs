-- https://en.wikipedia.org/wiki/Cannonball_problem
-- reference is doi:10.2307/2323911
-- this is an in-progress attempt at formalizing the proof

import Mathlib.Data.Int.ModEq
import Mathlib.NumberTheory.PellMatiyasevic
import Mathlib.Data.Int.Parity
import Mathlib.NumberTheory.LegendreSymbol.JacobiSymbol

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
theorem u_add_two : u (m + 2) = 4 * u (m + 1) - u m := by
  rw [u_add, u_add]; change u m * 7 + 3 * v m * 4 = 4 * (u m * 2 + 3 * v m * 1) - u m; ring

/-- Lemma 5b. -/
theorem v_add_two : v (m + 2) = 4 * v (m + 1) - v m := by
  rw [v_add, v_add]; change u m * 4 + 7 * v m = 4 * (u m * 1 + 2 * v m) - v m; ring

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

/-- Lemma 8a. -/
theorem Even.u_odd (h : Even n) : Odd (u n) := by
  have hn : ∀ n, u n ≡ [1, 0][n % 2]'(n.mod_lt zero_lt_two) [ZMOD 2] ∧
      v n ≡ [0, 1][n % 2]'(n.mod_lt zero_lt_two) [ZMOD 2] := by
    intro n
    induction' n using Nat.strongRecOn with n h
    match n with
    | 0 | 1 => decide
    | n + 2 =>
      have ⟨hu₀, hv₀⟩ := h n (lt_add_of_pos_right _ zero_lt_two)
      have ⟨hu₁, hv₁⟩ := h (n + 1) (lt_add_of_pos_right _ zero_lt_one)
      simp_rw [u_add_two, v_add_two, Int.ModEq,
        ((hu₁.mul_left 4).sub hu₀).eq, ((hv₁.mul_left 4).sub hv₀).eq, Nat.add_mod n]
      rcases n.mod_two_eq_zero_or_one with h | h <;> simp [h]
  simp_rw [Int.odd_iff, (hn n).1.eq, Nat.even_iff.1 h]; rfl

theorem Nat.mod_three_eq_zero_or_one_or_two : n % 3 = 0 ∨ n % 3 = 1 ∨ n % 3 = 2 :=
  match n % 3, n.mod_lt zero_lt_three with
  | 0, _ => Or.inl rfl
  | 1, _ => Or.inr (Or.inl rfl)
  | 2, _ => Or.inr (Or.inr rfl)

theorem uv_mod_five : u n ≡ [1, 2, 2][n % 3]'(n.mod_lt zero_lt_three) [ZMOD 5] ∧
    v n ≡ [0, 1, 4][n % 3]'(n.mod_lt zero_lt_three) [ZMOD 5] := by
  induction' n using Nat.strongRecOn with n h
  match n with
  | 0 | 1 => decide
  | n + 2 =>
    have ⟨hu₀, hv₀⟩ := h n (lt_add_of_pos_right _ zero_lt_two)
    have ⟨hu₁, hv₁⟩ := h (n + 1) (lt_add_of_pos_right _ zero_lt_one)
    simp_rw [u_add_two, v_add_two, Int.ModEq,
      ((hu₁.mul_left 4).sub hu₀).eq, ((hv₁.mul_left 4).sub hv₀).eq, Nat.add_mod n]
    rcases n.mod_three_eq_zero_or_one_or_two with h | h | h <;> simp [h]

/-- Lemma 8b. -/
theorem isCoprime_five_u : IsCoprime 5 (u n) := by
  have prime_five : Prime (5 : ℤ) := Nat.prime_iff_prime_int.1 (by norm_num)
  rw [Prime.coprime_iff_not_dvd prime_five, Int.dvd_iff_emod_eq_zero]
  have := (uv_mod_five (n := n)).1
  rcases n.mod_three_eq_zero_or_one_or_two with h | h | h <;>
    simp_rw [h] at this <;> dsimp [Int.ModEq] at this <;> rw [this] <;> decide

/-- Lemma 8c. -/
theorem sq_mod_five_iff_three_dvd : jacobiSym (u n) 5 = 1 ↔ 3 ∣ n := by
  have := (uv_mod_five (n := n)).1
  rcases n.mod_three_eq_zero_or_one_or_two with h | h | h <;> rw [Nat.dvd_iff_mod_eq_zero, h] <;>
    simp_rw [h] at this <;> dsimp [Int.ModEq] at this <;> rw [jacobiSym.mod_left' this] <;> decide




