-- https://en.wikipedia.org/wiki/Cannonball_problem
-- reference is doi:10.2307/2323911
-- this is a failed attempt at formalizing the proof

import Mathlib.Data.Int.Basic
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
      -- This should be provable from just `hxyw : x*y = 2*w*w`. This may require even-odd chasing.
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
  have hrs_sub_add_co : Int.gcd (r - s) (r + s) = 1 := by
    rw [← Int.isCoprime_iff_gcd_eq_one, ← IsCoprime.add_mul_left_left_iff (z := 1), mul_one,
      sub_add_add_cancel, ← two_mul, IsCoprime.mul_left_iff]
    -- Use `hrs_01` and `hrs_co`, respectively
    constructor
    · sorry -- Annoying casework, apparently
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
  sorry










termination_by _ w _ _ => w.natAbs
