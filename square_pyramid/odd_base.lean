-- https://en.wikipedia.org/wiki/Cannonball_problem
-- reference is doi:10.2307/2323911
-- this is a failed attempt at formalizing the proof

import Mathlib.Data.Int.Basic
import Mathlib.Data.Int.Lemmas
import Mathlib.Data.Int.Parity
import Mathlib.Data.Int.Order.Basic
import Mathlib.NumberTheory.PythagoreanTriples

theorem pythagorean_triangle_area_not_square {x y w : ℤ} (hx₀ : x > 0) (hy₀ : y > 0)
    (hxy : ∃ z, PythagoreanTriple x y z) (hxyw : x * y = 2 * w * w) : False := by
  -- Suppose `|w|` is minimal
  have hw_min {x y w' : ℤ} (hx : x > 0) (hy : y > 0) (hxy : ∃ z, PythagoreanTriple x y z)
      (hxyw' : x * y = 2 * w' * w') (h : w'.natAbs < w.natAbs) : False :=
    pythagorean_triangle_area_not_square hx hy hxy hxyw'
  -- Suppose `x` and `y` are coprime
  cases' (le_or_gt (Int.gcd x y) 1).symm with h h
  · have ⟨z, hxyz⟩ := hxy
    rcases hxyz.gcd_dvd with ⟨z', rfl⟩
    have ⟨x', hx'⟩ := x.gcd_dvd_left y
    have ⟨y', hy'⟩ := x.gcd_dvd_right y
    -- The proof skipped this important fact: `w / gcd(x, y)` is an integer.
    obtain ⟨w', rfl⟩ : (Int.gcd x y : ℤ) ∣ w := by
      have := hxyw ▸ mul_dvd_mul (x.gcd_dvd_left y) (x.gcd_dvd_right y)
      -- Somehow prove that `a*a ∣ 2*b*b → a ∣ b`
      sorry
    nth_rw 1 [hy', hx'] at hxyz hxyw
    have h₀ : (Int.gcd x y : ℤ) ≠ 0 := by simp [(lt_trans zero_lt_one h).ne.symm]
    rw [PythagoreanTriple.mul_iff _ h₀] at hxyz
    simp_rw [mul_left_comm, mul_assoc, ← mul_assoc (2 : ℤ)] at hxyw
    have hxyw := mul_left_cancel₀ h₀ (mul_left_cancel₀ h₀ hxyw)
    have hx'₀ : x' > 0 := pos_of_mul_pos_right (hx' ▸ hx₀) (Nat.cast_nonneg _)
    have hy'₀ : y' > 0 := pos_of_mul_pos_right (hy' ▸ hy₀) (Nat.cast_nonneg _)
    apply hw_min hx'₀ hy'₀ ⟨z', hxyz⟩ hxyw
    rw [Int.natAbs_mul, Int.natAbs_ofNat]
    refine lt_mul_left (Nat.zero_lt_of_ne_zero ?_) h
    rw [ne_eq, Int.natAbs_eq_zero]
    rintro rfl
    simp_rw [mul_zero] at hxyw
    rcases zero_eq_mul.1 hxyw.symm with rfl | rfl <;> contradiction
  cases' (Nat.le_and_le_add_one_iff.1 ⟨Nat.zero_le _, h⟩) with h hxy_co
  · have ⟨hx, hy⟩ := Int.gcd_eq_zero_iff.1 h
    exact hx₀.ne.symm hx
  -- WLOG, take `x = r^2-s^2` and `y = 2rs` where `gcd(r, s) = 1`.
  have ⟨z, hxyz⟩ := hxy
  clear h hxy
  have ⟨r, s, hxyrs', hzrs, hrs_co, hrs_01⟩ :=
    PythagoreanTriple.coprime_classification.1 ⟨hxyz, hxy_co⟩
  clear hzrs
  wlog hxyrs : x = r ^ 2 - s ^ 2 ∧ y = 2 * r * s
  · have hxyrs := and_comm.1 (or_iff_not_imp_left.1 hxyrs' hxyrs)
    refine this hy₀ hx₀ (mul_comm x y ▸ hxyw) hw_min (Int.gcd_comm x y ▸ hxy_co) z
      (pythagoreanTriple_comm.1 hxyz) r s (Or.inl hxyrs) hrs_co hrs_01 hxyrs
  clear hxyrs'
  simp_rw [pow_two] at hxyrs; revert hxyrs; rintro ⟨rfl, rfl⟩
  -- Simplify `hxyw`
  simp_rw [← pow_two, sq_sub_sq, mul_assoc, mul_left_comm _ (2 : ℤ)] at hxyw
  have hxyw := mul_left_cancel₀ (by decide) hxyw
  simp_rw [← mul_assoc] at hxyw
  have hrs_add_odd : Odd (r + s) := by
    simp_rw [← Int.even_iff, ← Int.odd_iff] at hrs_01
    rcases hrs_01 with ⟨hr, hs⟩ | ⟨hr, hs⟩
    · simp only [Int.odd_add', hr, hs]
    · simp only [Int.odd_add, hr, hs]
  have hrs_sub_add_co : Int.gcd (r - s) (r + s) = 1 := by
    rw [← Int.isCoprime_iff_gcd_eq_one, ← IsCoprime.add_mul_left_left_iff (z := 1), mul_one,
      sub_add_add_cancel, ← two_mul, IsCoprime.mul_left_iff]
    -- Use `hrs_add_odd` and `hrs_co`, respectively
    constructor
    · rw [Int.odd_iff_not_even, Int.even_iff, ← Int.dvd_iff_emod_eq_zero] at hrs_add_odd
      cases dvd_or_coprime 2 (r + s) Int.prime_two.irreducible <;> [contradiction; assumption]
    · nth_rw 2 [← mul_one r]
      exact IsCoprime.mul_add_left_right (Int.isCoprime_iff_gcd_eq_one.2 hrs_co) 1
  have ⟨⟨a, ha⟩, ⟨b, hb⟩, ⟨c, hc⟩, ⟨d, hd⟩⟩ :
      (∃ a, r = a * a) ∧ (∃ b, s = b * b) ∧ (∃ c, r - s = c * c) ∧ (∃ d, r + s = d * d) := by
    -- This should be provable from `hxyw`, and the fact that `r+s`, `r-s`, `r`, `s` are relatively prime.
    -- Relevant link: https://leanprover.zulipchat.com/#narrow/stream/113489-new-members/topic/squares/near/187825068
    -- Possibly relevant theorem: `Int.sq_of_gcd_eq_one`
    sorry
  have hcd_co : Int.gcd c d = 1 := by
    rw [← Int.isCoprime_iff_gcd_eq_one, ← IsCoprime.pow_iff (by decide : 0 < 2) (by decide : 0 < 2),
      pow_two, pow_two, ← hc, ← hd, Int.isCoprime_iff_gcd_eq_one, hrs_sub_add_co]
  have hc_odd : Odd c := by
    rwa [← and_self (Odd c), ← Int.odd_mul, ← hc, Int.odd_sub, ← Int.odd_add]
  have hd_odd : Odd d := by
    rwa [← and_self (Odd d), ← Int.odd_mul, ← hd]
  have ⟨x, hx⟩ : Even (c + d) := by simp only [Int.even_add', hc_odd, hd_odd]
  have ⟨y, hy⟩ : Even (d - c) := by simp only [Int.even_sub', hc_odd, hd_odd]
  have x2_add_y2_eq_a2 : x * x + y * y = a * a := by
    calc
    _ = (x * x * 4 + y * y * 4) / 4 := by rw [← right_distrib, Int.mul_ediv_cancel _ (by decide)]
    _ = (c * c * 2 + d * d * 2) / 4 := by
      congr 1
      have h₁ : (x + x) * (x + x) = (c + d) * (c + d) := by rw [hx]
      have h₂ : (y + y) * (y + y) = (d - c) * (d - c) := by rw [hy]
      linear_combination h₁+h₂
    _ = r * 4 / 4 := by
      rw [← right_distrib, ← hc, ← hd, sub_add_add_cancel, ← mul_two, mul_assoc]; rfl
    _ = a * a := by rw [Int.mul_ediv_cancel _ (by decide), ha]
  -- Note: The proof used `Int.gcd x y = 1` but this wasn't needed. A simpler approach is to
  -- get the integer equality `2xy = b^2`, then get `2 ∣ b`, then get `xy = 2(b/2)(b/2)`.
  have hxy_b2 : 2 * x * y = b * b := by
    have : 2 * (2 * x * y) = 2 * (b * b) := by
      calc
      _ = (x + x) * (y + y) := by ring
      _ = d * d - c * c := by rw [← hx, ← hy, add_comm, ← sq_sub_sq, pow_two, pow_two]
      _ = _ := by rw [← hd, ← hc, add_sub_sub_cancel, hb, ← two_mul]
    exact mul_left_cancel₀ (by decide) this
  have ⟨w', hw'⟩ : 2 ∣ b := by
    -- This follows from `hxy_b2 : 2xy = b^2`
    apply Int.Prime.dvd_pow' (k := 2) Nat.prime_two
    rw [pow_two, ← hxy_b2, mul_assoc]
    exists x * y
  have hxy_w' : x * y = 2 * w' * w' := by
    apply mul_left_cancel₀ two_ne_zero
    calc
    _ = (2 * w') * (2 * w') := by rw [← mul_assoc, hxy_b2, hw']
    _ = _ := by ring
  suffices x = 0 ∨ y = 0 by
    rcases this with (rfl | rfl)
    · simp at hxy_b2; rcases hxy_b2; simp at hb; rcases hb; simp at *
    · simp at hxy_b2; rcases hxy_b2; simp at hb; rcases hb; simp at *
  refine hw_min ⟨a, x2_add_y2_eq_a2⟩ hxy_w' ?_
  -- ← mul_lt_mul_left (by decide : 0 < 2)
  rw [Int.natAbs_lt_iff_sq_lt, pow_two, pow_two]
  apply lt_of_lt_of_le (b := s)
  · rw [hb, ← hxy_b2, mul_assoc, hxy_w']
  rw [← hxyw]
  sorry










termination_by _ w _ _ _ _ => w.natAbs
