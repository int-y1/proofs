import Mathlib.NumberTheory.PellMatiyasevic
import Mathlib.NumberTheory.LegendreSymbol.JacobiSymbol
import SquarePyramid.even_sol

/-- The integer sequence `u_n := ((2 + √3)^n + (2 - √3)^n) / 2`. The first few terms (starting at
`n = 0`) are 1, 2, 7, 26, 97, 362. -/
def u (n : ℕ) : ℤ := Pell.xz (by decide : 1 < 2) n

/-- The integer sequence `v_n := ((2 + √3)^n - (2 - √3)^n) / 2√3`. The first few terms (starting at
`n = 0`) are 0, 1, 4, 15, 56, 209. -/
def v (n : ℕ) : ℤ := Pell.yz (by decide : 1 < 2) n

variable {m n r : ℕ}

/-- `(u m, v m)` is a solution to the Pell equation `X^2 - 3Y^2 = 1`. -/
theorem uv_pell_eq : u m ^ 2 - 3 * v m ^ 2 = 1 := by
  rw [u, v, pow_two, pow_two, ← mul_assoc, ← Pell.pell_eqz (by decide : 1 < 2) m]; rfl

/-- Lemma 4a. Expansion of `u (m + n)`. -/
theorem u_add : u (m + n) = u m * u n + 3 * v m * v n := by
  dsimp only [u, v, Pell.xz, Pell.yz]; norm_cast; exact Pell.xn_add (by decide) m n

/-- Lemma 4b. Expansion of `v (m + n)`. -/
theorem v_add : v (m + n) = u m * v n + u n * v m := by
  dsimp only [u, v, Pell.xz, Pell.yz]; norm_cast; rw [Pell.yn_add (by decide) m n]; ring

/-- Lemma 4c. Expansion of `u (m - n)`, given that `n ≤ m`. -/
theorem u_sub (h : n ≤ m) : u (m - n) = u m * u n - 3 * v m * v n := by
  dsimp only [u, v]; exact Pell.xz_sub (by decide) h

/-- Lemma 4d. Expansion of `v (m - n)`, given that `n ≤ m`. -/
theorem v_sub (h : n ≤ m) : v (m - n) = -u m * v n + u n * v m := by
  dsimp only [u, v]; rw [Pell.yz_sub (by decide) h]; ring

/-- Lemma 5a. Expansion of `u (m + 2)`. -/
theorem u_add_two : u (m + 2) = 4 * u (m + 1) - u m := by
  rw [u_add, u_add]; change u m * 7 + 3 * v m * 4 = 4 * (u m * 2 + 3 * v m * 1) - u m; ring

/-- Lemma 5b. Expansion of `v (m + 2)`. -/
theorem v_add_two : v (m + 2) = 4 * v (m + 1) - v m := by
  rw [v_add, v_add]; change u m * 4 + 7 * v m = 4 * (u m * 1 + 2 * v m) - v m; ring

/-- Lemma 6a. Expansion of `u (2 * m)`. -/
theorem u_two_mul : u (2 * m) = 2 * u m ^ 2 - 1 ∧ u (2 * m) = 6 * v m ^ 2 + 1 := by
  rw [two_mul, u_add, ← uv_pell_eq (m := m)]; constructor <;> ring

/-- Lemma 6b. Expansion of `v (2 * m)`. -/
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

/-- Helper for lemma 8. -/
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

theorem Nat.mod_three_eq_or : n % 3 = 0 ∨ n % 3 = 1 ∨ n % 3 = 2 :=
  match n % 3, n.mod_lt zero_lt_three with
  | 0, _ | 1, _ | 2, _ => by trivial

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
    rcases n.mod_three_eq_or with h | h | h <;> simp [h]

/-- Helper for lemma 8. -/
theorem isCoprime_five_u : IsCoprime 5 (u n) := by
  have prime_five : Prime (5 : ℤ) := Nat.prime_iff_prime_int.1 (by norm_num)
  rw [Prime.coprime_iff_not_dvd prime_five, Int.dvd_iff_emod_eq_zero]
  have := (uv_mod_five (n := n)).1
  rcases n.mod_three_eq_or with h | h | h <;>
    simp_rw [h] at this <;> dsimp [Int.ModEq] at this <;> rw [this] <;> decide

/-- Lemma 8. If `n` is even, then `jacobiSym 5 m = -1 ↔ ¬3 ∣ n`.

Note: The original statement is `jacobiSym 5 m = 1 ↔ 3 ∣ n`, but I couldn't use this statement later
in the proof. As a result, I changed the lemma to the negative counterpart.

TODO: find a better way to cast `u n : ℤ` to ℕ, using `u n ≥ 0`. -/
theorem jacobiSym_five_iff_three_dvd (h : Even n) (hm : m = u n) : jacobiSym 5 m = -1 ↔ ¬3 ∣ n := by
  have hm_odd : Odd m := by rw [← Int.odd_coe_nat, hm]; exact h.u_odd
  have hj := jacobiSym.quadratic_reciprocity (by decide : Odd 5) hm_odd
  norm_num at hj
  rw [hj, hm]
  have hu := (uv_mod_five (n := n)).1
  rcases n.mod_three_eq_or with h | h | h <;> rw [Nat.dvd_iff_mod_eq_zero, h] <;>
    simp_rw [h] at hu <;> dsimp [Int.ModEq] at hu <;> rw [jacobiSym.mod_left' hu] <;> decide

/-- `n % 4` is either 0 or 1 or 2 or 3. -/
theorem Nat.mod_four_eq_or : n % 4 = 0 ∨ n % 4 = 1 ∨ n % 4 = 2 ∨ n % 4 = 3 :=
  match n % 4, n.mod_lt zero_lt_four with
  | 0, _ | 1, _ | 2, _ | 3, _ => by trivial

/-- Helper for lemma 9. -/
theorem uv_mod_eight : u n ≡ [1, 2, 7, 2][n % 4]'(n.mod_lt zero_lt_four) [ZMOD 8] ∧
    v n ≡ [0, 1, 4, 7][n % 4]'(n.mod_lt zero_lt_four) [ZMOD 8] := by
  induction' n using Nat.strongRecOn with n h
  match n with
  | 0 | 1 => decide
  | n + 2 =>
    have ⟨hu₀, hv₀⟩ := h n (lt_add_of_pos_right _ zero_lt_two)
    have ⟨hu₁, hv₁⟩ := h (n + 1) (lt_add_of_pos_right _ zero_lt_one)
    simp_rw [u_add_two, v_add_two, Int.ModEq,
      ((hu₁.mul_left 4).sub hu₀).eq, ((hv₁.mul_left 4).sub hv₀).eq, Nat.add_mod n]
    rcases n.mod_four_eq_or with h | h | h | h <;> simp [h]

/-- Lemma 9. If `n` is even, then `jacobiSym (-2) m = 1 ↔ 4 ∣ n`.

TODO: find a better way to cast `u n : ℤ` to ℕ, using `u n ≥ 0`. -/
theorem jacobiSym_neg_two_iff_four_dvd (h : Even n) (hm : m = u n) :
    jacobiSym (-2) m = 1 ↔ 4 ∣ n := by
  rcases n.mod_four_eq_or with hn | hn | hn | hn
  any_goals have := hn ▸ h.mod_even (by decide : Even 4); contradiction
  all_goals
  · have hm_odd : Odd m := by rw [← Int.odd_coe_nat, hm]; exact h.u_odd
    have hu := (uv_mod_eight (n := n)).1
    rw [jacobiSym.at_neg_two hm_odd, ZMod.χ₈'_nat_eq_if_mod_eight, Nat.dvd_iff_mod_eq_zero, hn]
    simp_rw [hn, ← hm] at hu
    dsimp [Int.ModEq] at hu
    norm_cast at hu
    rw [hu, Nat.odd_iff.1 hm_odd]
    simp only [ite_true, ite_false]
    try ring_nf -- todo: this is ugly. find a better tactic.

/-- Given a positive integer `n`, you can write `n = k' * 2^s` where `k'` is odd. -/
theorem Nat.odd_mul_two_pow (n : ℕ) (h : n > 0) : ∃ k' s, Odd k' ∧ n = k' * 2 ^ s := by
  rcases n.even_or_odd.symm with ⟨k, rfl⟩ | ⟨k, hk⟩
  · exists 2 * k + 1, 0
    simp
  rcases k.eq_zero_or_pos with rfl | hk₀
  · rcases hk; contradiction
  have : k < n := hk.symm ▸ add_lt_add_left hk₀ k
  have ⟨k', s, hks⟩ : ∃ k' s, Odd k' ∧ k = k' * 2 ^ s := k.odd_mul_two_pow hk₀
  refine ⟨k', s + 1, hks.1, ?_⟩
  rw [hk, hks.2]
  ring

/-- Lemma 10. -/
theorem lemma10 (h : ∃ M, u n = 4 * M ^ 2 + 3) : u n = 7 := by
  obtain ⟨M, huM⟩ := h
  have hu_mod_eight : u n ≡ 3 [ZMOD 8] ∨ u n ≡ 7 [ZMOD 8] := by
    rcases (M ^ 2).even_or_odd with ⟨k, hk⟩ | ⟨k, hk⟩ <;> rw [huM, hk] <;>
      [left; right] <;> ring_nf <;> rw [mul_comm] <;> exact Int.modEq_add_fac_self
  replace hu_mod_eight : u n ≡ 7 [ZMOD 8] := by
    refine' (or_iff_right fun h ↦ _).1 hu_mod_eight
    have hu := (uv_mod_eight (n := n)).1.eq
    rcases n.mod_four_eq_or with hn | hn | hn | hn <;> simp [h.eq, hn] at hu
  have ⟨k, hnk⟩ : ∃ k, n = 8 * k - 2 ∨ n = 8 * k + 2 := by
    have hn_mod_four : n % 4 = 2 := by
      have hu := (uv_mod_eight (n := n)).1.eq
      rcases n.mod_four_eq_or with h | h | h | h <;> [skip; skip; exact h; skip] <;>
        dsimp [Int.ModEq] at hu_mod_eight <;> simp [hu_mod_eight, h] at hu
    have := hn_mod_four ▸ n.div_add_mod 4
    rcases (n / 4).even_or_odd with ⟨k, hk⟩ | ⟨k, hk⟩
    · exists k; right; rw [← this, hk]; ring
    · exists k + 1; left; rw [left_distrib, Nat.add_sub_assoc (by decide), ← this, hk]; ring
  rcases k.eq_zero_or_pos with rfl | hk₀
  · rcases hnk with rfl | rfl
    · -- `n = 8*0-2 = 0`. This is an unfortunate artifact of subtraction in ℕ.
      -- Luckily, this artifact didn't matter much, because `hu_mod_eight` has a contradiction.
      contradiction
    · rfl -- `n = 8*0+2 = 2`
  have ⟨k', s, hk'_odd, hs2, hn'⟩ :
      ∃ k' s, Odd k' ∧ s ≥ 2 ∧ (n = 2 * k' * 2 ^ s - 2 ∨ n = 2 * k' * 2 ^ s + 2) := by
    obtain ⟨k', s, hk'_odd, rfl⟩ := k.odd_mul_two_pow hk₀
    refine ⟨k', s + 2, hk'_odd, Nat.le_add_left _ _, ?_⟩
    convert hnk using 3 <;> ring_nf
  clear hu_mod_eight k hnk hk₀
  have h_mod_2s : u n ≡ (-1) ^ k' * 7 [ZMOD u (2 ^ s)] := by
    have : 2 ≤ 2 * k' * 2 ^ s := Nat.mul_le_mul (Nat.mul_le_mul_left 2 hk'_odd.pos) s.one_le_two_pow
    have ⟨h₁, h₂⟩ := lemma7 this
    rcases hn' with rfl | rfl <;> [exact h₁; exact h₂]
  replace h_mod_2s : (2 * M) * (2 * M) ≡ -10 [ZMOD u (2 ^ s)] := by
    rw [huM, hk'_odd.neg_one_pow] at h_mod_2s
    convert h_mod_2s.sub_right 3 using 1
    ring
  have ⟨m, hm⟩ : ∃ m : ℕ, m = u (2 ^ s) := ⟨Pell.xn _ _, rfl⟩
  have h2s_even : Even (2 ^ s) := by
    rw [← Nat.sub_add_cancel (le_trans (by decide : 1 ≤ 2) hs2)]; exists 2 ^ (s - 1); ring
  have hj_neg_two : jacobiSym (-2) m = 1 := by
    rw [jacobiSym_neg_two_iff_four_dvd h2s_even hm, ← Nat.sub_add_cancel hs2]
    exists 2 ^ (s - 2); ring
  have hj_five : jacobiSym 5 m = -1 := by
    rw [jacobiSym_five_iff_three_dvd h2s_even hm]
    intro h
    have := Nat.prime_three.dvd_of_dvd_pow h
    contradiction
  have hj_neg_ten : jacobiSym (-10) m = -1 := by
    rw [(by decide : -10 = -2 * 5), jacobiSym.mul_left (-2) 5 m, hj_neg_two, hj_five]; rfl
  -- Note: The paper claims that `jacobiSym (4*M^2) (u 2^s) = 1`, but I don't want to prove it.
  -- Instead, I did this: `jacobiSym (4*M^2) (u 2^s) = (jacobiSym (2*M) (u 2^s))^2 ≥ 0`
  have hj_neg_ten' : jacobiSym (-10) m ≥ 0 := by
    rw [jacobiSym.mod_left' (hm.symm ▸ h_mod_2s.symm), jacobiSym.mul_left, ← pow_two]
    exact sq_nonneg _
  simp only [hj_neg_ten] at hj_neg_ten'

/-- Theorem 11. `x = 1` is the only odd solution to the cannonball problem. -/
theorem cannonball_odd_1 {x y : ℤ} (h : x * (x + 1) * (2 * x + 1) = 6 * y ^ 2) (hx : x > 0)
    (hx_odd : Odd x) : x = 1 := by
  have ⟨vv, hvv⟩ := hx_odd.add_odd odd_one
  have hvv₀ : vv > 0 := by
    refine pos_of_mul_pos_left ?_ (by decide : (0 : ℤ) ≤ 2)
    rw [mul_two, ← hvv]
    positivity
  replace h : x * (vv * (2 * x + 1)) = 3 * y ^ 2 := by
    apply mul_left_cancel₀ (by decide : (2 : ℤ) ≠ 0)
    rw [hvv] at h
    linear_combination h
  have hco12 : IsCoprime x vv := by
    convert (isCoprime_one_left (x := vv)).neg_left.mul_add_right_left 2 using 1
    linear_combination hvv
  have hco13 : IsCoprime x (2 * x + 1) := isCoprime_one_right.mul_add_right_right _
  have hco23 : IsCoprime vv (2 * x + 1) := by
    convert (isCoprime_one_right (x := vv)).neg_right.mul_add_right_right 4 using 1
    linear_combination 2 * hvv
  have hx3 := mul_eq_three_sq (hco12.mul_right hco13) h hx.le
  have hvv3 : vv % 3 ≠ 2 :=
    mul_eq_three_sq (hco12.symm.mul_right hco23) (mul_left_comm x _ _ ▸ h) hvv₀.le
  replace hx3 : x ≡ 1 [ZMOD 3] := by
    mod_cases x % 3
    · absurd hvv3
      change vv ≡ 2 [ZMOD 3]
      apply Int.ModEq.cancel_right_div_gcd (c := 2) zero_lt_three
      rw [mul_two, ← hvv]
      exact H.add_right 1
    · exact H
    · absurd hx3
      exact H
  have ⟨ww, hww⟩ : 3 ∣ 2 * x + 1 := Int.modEq_zero_iff_dvd.1 ((hx3.mul_left 2).add_right 1)
  have hww₀ : ww > 0 := by
    refine pos_of_mul_pos_right ?_ (by decide : (0 : ℤ) ≤ 3)
    rw [← hww]
    positivity
  clear hvv3 hx3
  replace hco13 := (hww ▸ hco13).of_mul_right_right
  replace hco23 := (hww ▸ hco23).of_mul_right_right
  replace h : x * (vv * ww) = y ^ 2 := by
    apply mul_left_cancel₀ (by decide : (3 : ℤ) ≠ 0)
    rw [hww] at h
    linear_combination h
  -- Make squares. `x = u^2`, `x+1 = 2v^2`, `2x+1 = 3w^2`
  have ⟨u, hu⟩ := exists_associated_pow_of_mul_eq_pow' (hco12.mul_right hco13) h
  rcases Int.eq_of_associated_of_nonneg hu (sq_nonneg u) hx.le
  have ⟨v, hv⟩ :=
    exists_associated_pow_of_mul_eq_pow' (hco12.symm.mul_right hco23) (mul_left_comm _ vv _ ▸ h)
  rcases Int.eq_of_associated_of_nonneg hv (sq_nonneg v) hvv₀.le
  have ⟨w, hw⟩ := exists_associated_pow_of_mul_eq_pow' (hco13.mul_left hco23).symm
    (mul_left_comm _ ww _ ▸ mul_comm _ ww ▸ h)
  rcases Int.eq_of_associated_of_nonneg hw (sq_nonneg w) hww₀.le
  clear hu hv hw
  -- Get ready to use lemma 10.
  have h₁ : 6 * w ^ 2 + 1 = 4 * u ^ 2 + 3 := by linear_combination -2 * hww
  have h₂ : (6 * w ^ 2 + 1) ^ 2 - 3 * (4 * v * w) ^ 2 = 1 := by
    calc
    _ = 1 + (4 - 8 * (v ^ 2 + v ^ 2)) * (3 * w ^ 2) + 4 * (3 * w ^ 2) ^ 2 := by ring
    _ = _ := by rw [← hvv, ← hww]; ring
  have ⟨x, hx⟩ : ∃ x : ℕ, x = 6 * w ^ 2 + 1 := by
    exists (6 * w ^ 2 + 1).natAbs
    rw [Int.coe_natAbs, abs_eq_self]
    positivity
  replace h₂ : x * x - 3 * (4 * v * w).natAbs * (4 * v * w).natAbs = 1 := by
    rw [← pow_two, mul_assoc, ← pow_two, ← Int.cast_eq_cast_iff_Nat, Nat.cast_sub]
    · norm_num [hx]
      exact h₂
    · rw [← Nat.cast_le (α := ℤ)]
      norm_num [hx]
      rw [sub_eq_iff_eq_add.1 h₂, le_add_iff_nonneg_left]
      decide
  have ⟨n, hxn, hyn⟩ := Pell.eq_pell (by decide : 1 < 2) h₂
  have hM : ∃ M, _root_.u n = 4 * M ^ 2 + 3 := by
    exists u
    rw [← h₁, ← hx, hxn]; rfl
  -- Solve for `u^2`
  rw [hxn, h₁] at hx
  change _root_.u n = 4 * u ^ 2 + 3 at hx
  rw [lemma10 hM] at hx
  exact mul_left_cancel₀ (by decide : (4 : ℤ) ≠ 0) (by linear_combination -hx)
