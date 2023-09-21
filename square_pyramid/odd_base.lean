-- https://en.wikipedia.org/wiki/Cannonball_problem
-- reference is doi:10.2307/2323911
-- this is a failed attempt at formalizing the proof

import Mathlib.Data.Int.Basic
import Mathlib.Data.Int.Parity
import Mathlib.Data.Int.Order.Basic
import Mathlib.NumberTheory.PythagoreanTriples

theorem pythagorean_triangle_area_not_square {x y w : ℤ} (hxy : ∃ z, PythagoreanTriple x y z)
    (hxyw : x * y = 2 * w * w) : x = 0 ∨ y = 0 := by
  rw [or_iff_not_and_not]
  intro ⟨hx₀, hy₀⟩
  -- Suppose `|w|` is minimal
  have hw_min {x y w' : ℤ} (hxy : ∃ z, PythagoreanTriple x y z) (hxyw' : x * y = 2 * w' * w')
      (h : w'.natAbs < w.natAbs) : x = 0 ∨ y = 0 :=
    pythagorean_triangle_area_not_square hxy hxyw'
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
    have := hw_min ⟨z', hxyz⟩ hxyw <| by
      rw [Int.natAbs_mul, Int.natAbs_ofNat]
      refine lt_mul_left (Nat.zero_lt_of_ne_zero ?_) h
      rw [ne_eq, Int.natAbs_eq_zero]
      rintro rfl
      rw [mul_zero, mul_eq_zero] at hxyw
      rcases hxyw with (rfl | rfl)
      · apply hx₀; rw [hx', mul_zero]
      · apply hy₀; rw [hy', mul_zero]
    rcases this with (rfl | rfl)
    · apply hx₀; rw [hx', mul_zero]
    · apply hy₀; rw [hy', mul_zero]
  cases' (Nat.le_and_le_add_one_iff.1 ⟨Nat.zero_le _, h⟩) with h hxy_co
  · have ⟨hx, hy⟩ := Int.gcd_eq_zero_iff.1 h
    simp [hx] at hxyw
    trivial
  -- WLOG, take `x = r^2-s^2` and `y = 2rs` where `gcd(r, s) = 1`.
  have ⟨z, hxyz⟩ := hxy
  clear h hxy
  have ⟨r, s, hxyrs', hzrs, hrs_co, hrs_01⟩ :=
    PythagoreanTriple.coprime_classification.1 ⟨hxyz, hxy_co⟩
  clear hzrs
  wlog hxyrs : x = r ^ 2 - s ^ 2 ∧ y = 2 * r * s
  · have hxyrs := and_comm.1 (or_iff_not_imp_left.1 hxyrs' hxyrs)
    refine this (mul_comm x y ▸ hxyw) hy₀ hx₀ hw_min (Int.gcd_comm x y ▸ hxy_co) z
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
  have hxy_co : Int.gcd x y = 1 := by
    sorry
  sorry










termination_by _ w _ _ => w.natAbs
