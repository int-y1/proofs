-- https://en.wikipedia.org/wiki/Cannonball_problem
-- reference is doi:10.2307/2323911
-- this is an in-progress attempt at formalizing the proof

import Mathlib.Data.Int.Basic
import Mathlib.Data.Int.Lemmas
import Mathlib.Data.Int.Parity
import Mathlib.Data.Int.Order.Basic
import Mathlib.Data.Int.SuccPred
import Mathlib.NumberTheory.PythagoreanTriples
import Mathlib.Tactic.ModCases

theorem pos_sq_of_coprime {a b c : ℤ} (h : IsCoprime a b) (heq : a * b = c ^ 2) (ha : a > 0)
    (hb : b > 0): ∃ x y, x > 0 ∧ y > 0 ∧ a = x ^ 2 ∧ b = y ^ 2 := by
  have ⟨x, hx⟩ := Int.sq_of_coprime h heq
  rcases hx with rfl | rfl
  case inr =>
    rw [gt_iff_lt, neg_pos, ← not_le] at ha
    exact (ha (sq_nonneg x)).elim
  have ⟨y, hy⟩ := Int.sq_of_coprime h.symm (mul_comm _ b ▸ heq)
  rcases hy with rfl | rfl
  case inr =>
    rw [gt_iff_lt, neg_pos, ← not_le] at hb
    exact (hb (sq_nonneg y)).elim
  exists |x|, |y|
  simp [(sq_pos_iff _).1 ha, (sq_pos_iff _).1 hb]

theorem sq_dvd_two_mul_sq {a b : ℤ} (h : a * a ∣ 2 * b * b) : a ∣ b := by
  obtain ⟨k, hk⟩ := h
  rcases k.even_or_odd with ⟨k, rfl⟩ | ⟨k, rfl⟩
  · replace hk : b * b = a * a * k :=
      mul_left_cancel₀ (by decide : (2 : ℤ) ≠ 0) (by linear_combination hk)
    have h : a * a ∣ b * b := ⟨k, hk⟩
    rwa [← pow_two, ← pow_two, Int.pow_dvd_pow_iff (by decide)] at h
  have ⟨a', ha'⟩ : Even a := by
    have := Int.odd_iff_not_even.1 (odd_two_mul_add_one k)
    cases' Int.even_mul.1 (hk ▸ (even_two_mul b).mul_right b) with h h
    · rwa [Int.even_mul, or_self] at h
    · exact (Int.odd_iff_not_even.1 (odd_two_mul_add_one k) h).elim
  have ⟨b', hb'⟩ : Even b := by
    rcases ha'
    replace hk : b * b = a' * a' * (2 * k + 1) + a' * a' * (2 * k + 1) :=
      mul_left_cancel₀ (by decide : (2 : ℤ) ≠ 0) (by linear_combination hk)
    have : Even (b * b) := ⟨_, hk⟩
    rwa [Int.even_mul, or_self] at this
  rcases eq_or_ne a 0 with rfl | ha₀
  · rw [zero_dvd_iff]
    simpa using hk
  -- Infinite descent, use `sq_dvd_two_mul_sq` on `a/2` and `b/2`
  have h' : a' * a' ∣ 2 * b' * b' := by
    exists 2 * k + 1
    rw [ha', hb'] at hk
    exact mul_left_cancel₀ (by decide : (4 : ℤ) ≠ 0) (by linear_combination hk)
  have : a'.natAbs < a.natAbs := by
    simp_rw [ha', ← two_mul, mul_ne_zero_iff, true_and, ← Int.natAbs_pos] at ha₀
    rw [ha', ← two_mul, Int.natAbs_mul, lt_mul_iff_one_lt_left ha₀]; decide
  have ⟨k', hk'⟩ := sq_dvd_two_mul_sq h'
  exists k'
  rw [ha', hb']
  linear_combination 2 * hk'
termination_by _ a _ _ => a.natAbs

/-- Lemma 1. -/
theorem pythagoreanTriple_area_ne_sq {x y w : ℤ} (hx₀ : x > 0) (hy₀ : y > 0)
    (hxy : ∃ z, PythagoreanTriple x y z) (hxyw : x * y = 2 * w * w) : False := by
  -- Suppose `|w|` is minimal
  have hw_min {x y w' : ℤ} (hx : x > 0) (hy : y > 0) (hxy : ∃ z, PythagoreanTriple x y z)
      (hxyw' : x * y = 2 * w' * w') (_h : w'.natAbs < w.natAbs) : False :=
    pythagoreanTriple_area_ne_sq hx hy hxy hxyw'
  -- Suppose `x` and `y` are coprime
  cases' (le_or_gt (Int.gcd x y) 1).symm with h h
  · have ⟨z, hxyz⟩ := hxy
    rcases hxyz.gcd_dvd with ⟨z', rfl⟩
    have ⟨x', hx'⟩ := x.gcd_dvd_left y
    have ⟨y', hy'⟩ := x.gcd_dvd_right y
    -- The proof skipped this important fact: `w / gcd(x, y)` is an integer.
    obtain ⟨w', rfl⟩ : (Int.gcd x y : ℤ) ∣ w :=
      sq_dvd_two_mul_sq (hxyw ▸ mul_dvd_mul (x.gcd_dvd_left y) (x.gcd_dvd_right y))
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
  · exact hx₀.ne.symm (Int.gcd_eq_zero_iff.1 h).1
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
  replace hxyw := mul_left_cancel₀ (by decide) hxyw
  simp_rw [← mul_assoc] at hxyw
  have hrs_add_odd : Odd (r + s) := by
    simp_rw [← Int.even_iff, ← Int.odd_iff] at hrs_01
    rcases hrs_01 with ⟨hr, hs⟩ | ⟨hr, hs⟩
    · simp only [Int.odd_add', hr, hs]
    · simp only [Int.odd_add, hr, hs]
  clear hrs_01
  -- `r`, `s`, and `r-s` are positive
  wlog hr₀ : r > 0
  · rw [not_lt, le_iff_lt_or_eq] at hr₀
    rcases hr₀ with hr₀ | rfl
    · apply this hw_min z (-r) (-s)
      rwa [Int.gcd_neg_right, Int.gcd_neg_left]
      convert hx₀ using 1; ring
      convert hy₀ using 1; ring
      convert hxy_co using 1; ring_nf
      convert hxyz using 1 <;> ring_nf
      convert hxyw using 1; ring_nf
      convert hrs_add_odd.neg using 1; ring_nf
      rwa [gt_iff_lt, Left.neg_pos_iff]
    · simp at hy₀
  have hs₀ : s > 0 := pos_of_mul_pos_right hy₀ (mul_pos zero_lt_two hr₀).le
  have hrs₀ : r - s > 0 := by
    rw [← pow_two, ← pow_two, sq_sub_sq] at hx₀
    exact pos_of_mul_pos_right hx₀ (Int.add_lt_add hr₀ hs₀).le
  have hrs_sub_add_co : Int.gcd (r - s) (r + s) = 1 := by
    rw [← Int.isCoprime_iff_gcd_eq_one, ← IsCoprime.add_mul_left_left_iff (z := 1), mul_one,
      sub_add_add_cancel, ← two_mul, IsCoprime.mul_left_iff]
    -- Use `hrs_add_odd` and `hrs_co`, respectively
    constructor
    · rw [Int.odd_iff_not_even, Int.even_iff, ← Int.dvd_iff_emod_eq_zero] at hrs_add_odd
      cases dvd_or_coprime 2 (r + s) Int.prime_two.irreducible <;> [contradiction; assumption]
    · nth_rw 2 [← mul_one r]
      exact (Int.isCoprime_iff_gcd_eq_one.2 hrs_co).mul_add_left_right 1
  have ⟨⟨a, _, ha⟩, ⟨b, hb₀, hb⟩, ⟨c, hc₀, hc⟩, ⟨d, hd₀, hd⟩⟩ :
      (∃ a, a > 0 ∧ r = a * a) ∧ (∃ b, b > 0 ∧ s = b * b) ∧
      (∃ c, c > 0 ∧ r - s = c * c) ∧ (∃ d, d > 0 ∧ r + s = d * d) := by
    -- Use `hxyw`. Also, use the fact that `r+s`, `r-s`, `r`, `s` are positive and pairwise coprime.
    simp_rw [← pow_two] at hxyw ⊢
    rw [Int.gcd_eq_one_iff_coprime] at hrs_co hrs_sub_add_co
    have hpos₁ := add_pos hr₀ hs₀
    have hpos₂ := mul_pos hpos₁ hrs₀
    have hpos₃ := mul_pos hpos₂ hr₀
    have ⟨abc, d, _, hd₀, habc, hd⟩ :
        ∃ x y, x > 0 ∧ y > 0 ∧ (r + s) * (r - s) * r = x ^ 2 ∧ s = y ^ 2 := by
      refine pos_sq_of_coprime ((IsCoprime.mul_left ?_ ?_).mul_left hrs_co) hxyw hpos₃ hs₀
      convert hrs_co.add_mul_left_left 1; rw [mul_one]
      convert hrs_co.add_mul_left_left (-1) using 1; ring
    have ⟨ab, c, _, hc₀, hab, hc⟩ :
        ∃ x y, x > 0 ∧ y > 0 ∧ (r + s) * (r - s) = x ^ 2 ∧ r = y ^ 2 := by
      refine pos_sq_of_coprime (IsCoprime.mul_left ?_ ?_) habc hpos₂ hr₀
      convert hrs_co.symm.mul_add_left_left 1; rw [mul_one]
      convert (hrs_co.symm.add_mul_left_left (-1)).neg_left using 1; ring
    have ⟨a, b, ha₀, hb₀, ha, hb⟩ := pos_sq_of_coprime hrs_sub_add_co.symm hab hpos₁ hrs₀
    exact ⟨⟨c, hc₀, hc⟩, ⟨d, hd₀, hd⟩, ⟨b, hb₀, hb⟩, ⟨a, ha₀, ha⟩⟩
  have hc_odd : Odd c := by
    rwa [← and_self (Odd c), ← Int.odd_mul, ← hc, Int.odd_sub, ← Int.odd_add]
  have hd_odd : Odd d := by rwa [← and_self (Odd d), ← Int.odd_mul, ← hd]
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
  refine hw_min ?_ ?_ ⟨a, x2_add_y2_eq_a2⟩ hxy_w' ?_
  · have := add_pos hc₀ hd₀
    rw [hx, ← two_mul] at this
    exact pos_of_mul_pos_right this (by decide)
  · have : 0 < (c + d) * (d - c) := by
      calc
      _ ≤ b ^ 2 + b ^ 2 := add_pos (sq_pos_of_pos hb₀) (sq_pos_of_pos hb₀)
      _ = (r + s) - (r - s) := by rw [pow_two, ← hb, add_sub_sub_cancel]
      _ = _ := by rw [hd, hc]; ring
    replace := pos_of_mul_pos_right this (add_pos hc₀ hd₀).le
    rw [hy, ← two_mul] at this
    exact pos_of_mul_pos_right this (by decide)
  -- ← mul_lt_mul_left (by decide : 0 < 2)
  rw [Int.natAbs_lt_iff_sq_lt, pow_two, pow_two]
  apply lt_of_lt_of_le (b := s)
  · have : w' > 0 := pos_of_mul_pos_right (hw' ▸ hb₀) (by decide)
    convert lt_mul_left (mul_pos this this) (by decide : (1 : ℤ) < 4) using 1
    rw [hb, ← hxy_b2, mul_assoc, hxy_w']
    ring
  rw [← hxyw]
  refine' le_mul_of_one_le_left hs₀.le (Int.pos_iff_one_le.1 _)
  positivity
termination_by _ w _ _ _ _ => w.natAbs

/-- Lemma 1, alternate form. -/
theorem pythagoreanTriple_area_ne_sq' {x y w : ℤ} (hxy : ∃ z, PythagoreanTriple x y z)
    (hxyw : x * y = 2 * w * w) : x = 0 ∨ y = 0 := by
  by_contra h
  rw [not_or] at h
  obtain ⟨hx, hy⟩ := h
  have hxy₀ := mul_le_mul_of_nonneg_left (sq_nonneg w) (by decide : (0 : ℤ) ≤ 2)
  rw [mul_zero, pow_two, ← mul_assoc, ← hxyw] at hxy₀
  cases' lt_or_gt_of_ne hx with hx hx
  · cases' lt_or_gt_of_ne hy with hy hy
    · refine pythagoreanTriple_area_ne_sq (x := -x) (y := -y) (w := w)
        (by simpa) (by simpa) ?_ (by simpa)
      obtain ⟨z, hz⟩ := hxy
      exists z
      rwa [PythagoreanTriple, neg_mul_neg, neg_mul_neg]
    · have := lt_of_le_of_lt hxy₀ (mul_neg_of_neg_of_pos hx hy)
      contradiction
  · cases' lt_or_gt_of_ne hy with hy hy
    · have := lt_of_le_of_lt hxy₀ (mul_neg_of_pos_of_neg hx hy)
      contradiction
    · exact pythagoreanTriple_area_ne_sq hx hy hxy hxyw

/-- Lemma 2. -/
theorem two_mul_pow_four_add_one_ne_sq {x y : ℤ} (hxy : 2 * x ^ 4 + 1 = y ^ 2) (hx : x > 0) :
    False := by
  wlog hy₀ : y > 0
  · rw [gt_iff_lt, not_lt, le_iff_lt_or_eq] at hy₀
    rcases hy₀ with hy₀ | rfl
    · exact this (x := x) (y := -y) (by rwa [Even.neg_pow even_two]) hx (Left.neg_pos_iff.2 hy₀)
    · exact Int.even_iff_not_odd.1 even_zero ⟨x ^ 4, hxy.symm⟩
  -- Suppose `x` is minimal
  have hx_min {x' y : ℤ} (hx'y : 2 * x' ^ 4 + 1 = y ^ 2) (hx' : x' > 0) (h : x' < x) : False := by
    have : Int.natAbs x' < Int.natAbs x := by
      rwa [Int.eq_natAbs_of_zero_le hx.le, Int.eq_natAbs_of_zero_le hx'.le, Nat.cast_lt] at h
    exact two_mul_pow_four_add_one_ne_sq hx'y hx'
  have ⟨s, hys⟩ : Odd y := by
    rw [← Int.odd_pow' (by decide : 2 ≠ 0), ← hxy]
    apply odd_two_mul_add_one
  have hs₀ : s > 0 := by
    rw [hys, gt_iff_lt, Int.lt_add_one_iff, mul_nonneg_iff_right_nonneg_of_pos (by decide)] at hy₀
    rcases (le_iff_lt_or_eq.1 hy₀) with h | rfl
    · exact h
    rw [hys] at hxy
    simp only [mul_zero, zero_add, one_pow, add_left_eq_self, mul_eq_zero, zero_lt_four,
      pow_eq_zero_iff, false_or] at hxy
    exact hxy ▸ hx
  have hx4s : x ^ 4 = 2 * s * (s + 1) := by
    apply mul_left_cancel₀ (by decide : (2 : ℤ) ≠ 0)
    rw [hys] at hxy
    linear_combination hxy
  cases' s.even_or_odd.symm with hs hs
  · have hs_2s1_co : IsCoprime s (2 * (s + 1)) := by
      apply IsCoprime.mul_right
      · cases' dvd_or_coprime 2 s Int.prime_two.irreducible with h h
        · exact (Int.odd_iff_not_even.1 hs (even_iff_two_dvd.2 h)).elim
        · exact h.symm
      · have := (isCoprime_one_right (x := s)).mul_add_left_right 1
        rwa [mul_one] at this
    -- Use `hx4s` and `hs_2s1_co` to get `s = u^4` and `2(s+1) = v^4`
    rw [mul_comm 2, mul_assoc] at hx4s
    have ⟨u, hu⟩ := exists_associated_pow_of_mul_eq_pow' hs_2s1_co hx4s.symm
    replace hu := Int.eq_of_associated_of_nonneg hu (pow_bit0_nonneg u 2) hs₀.le
    have ⟨v, hv⟩ := exists_associated_pow_of_mul_eq_pow' hs_2s1_co.symm (mul_comm s _ ▸ hx4s.symm)
    replace hv := Int.eq_of_associated_of_nonneg hv (pow_bit0_nonneg v 2) (by positivity)
    rw [← hu] at hv
    -- Do cases on `v^4 = 2 * (u^4 + 1)` mod 8. This is ugly, but I don't know how to shorten it.
    have : v ^ 4 % 8 = 2 * (u ^ 4 + 1) % 8 := by rw [hv]
    have hu₀ : Even u → 2 * (u ^ 4 + 1) % 8 = 2 := by
      rintro ⟨x, rfl⟩
      suffices (2 + 8 * (4*x^4)) % 8 = 2 by convert this using 2; ring
      simp only [Int.add_mul_emod_self_left]
    have hu₁ : Odd u → 2 * (u ^ 4 + 1) % 8 = 4 := by
      rintro ⟨x, rfl⟩
      suffices (4 + 8 * (4*x^4 + 8*x^3 + 6*x^2 + 2*x)) % 8 = 4 by convert this using 2; ring
      simp only [Int.add_mul_emod_self_left]
    have hv₀ : Even v → v ^ 4 % 8 = 0 := by
      rintro ⟨x, rfl⟩
      suffices 8 * (2*x^4) % 8 = 0 by convert this using 2; ring
      apply Int.mul_emod_right
    have hv₁ : Odd v → v ^ 4 % 8 = 1 := by
      rintro ⟨x, rfl⟩
      suffices (1 + 8 * (2*x^4 + 4*x^3 + 3*x^2 + x)) % 8 = 1 by convert this using 2; ring
      simp only [Int.add_mul_emod_self_left]
    cases' u.even_or_odd with h₁ h₁ <;> cases' v.even_or_odd with h₂ h₂ <;>
      [rw [hu₀ h₁, hv₀ h₂] at this; rw [hu₀ h₁, hv₁ h₂] at this;
      rw [hu₁ h₁, hv₀ h₂] at this; rw [hu₁ h₁, hv₁ h₂] at this] <;> contradiction
  have h2s_s1_co : IsCoprime (2 * s) (s + 1) := by
    apply IsCoprime.mul_left
    · cases' dvd_or_coprime 2 (s + 1) Int.prime_two.irreducible with h h
      · exact (Int.odd_iff_not_even.1 hs.add_one (even_iff_two_dvd.2 h)).elim
      · exact h
    · have := (isCoprime_one_right (x := s)).mul_add_left_right 1
      rwa [mul_one] at this
  -- Use `hx4s` and `h2s_s1_co` to get `2s = u^4` and `s+1 = v^4`
  have ⟨u, hu⟩ := exists_associated_pow_of_mul_eq_pow' h2s_s1_co hx4s.symm
  replace hu := Int.eq_of_associated_of_nonneg hu (pow_bit0_nonneg u 2) (mul_pos (by decide) hs₀).le
  have ⟨v, hv⟩ := exists_associated_pow_of_mul_eq_pow' h2s_s1_co.symm (mul_comm (2*s) _ ▸ hx4s.symm)
  replace hv := Int.eq_of_associated_of_nonneg hv (pow_bit0_nonneg v 2) (by positivity)
  have ⟨w, hw⟩ : Even u := (Int.even_pow.1 ⟨s, two_mul s ▸ hu⟩).1
  have ⟨a, ha⟩ : Odd (v ^ 2) := by
    rw [Int.odd_pow' (by decide), ← Int.odd_pow' (by decide : 4 ≠ 0), hv]
    exact hs.add_one
  have hwa : 2 * w ^ 4 = a * (a + 1) := mul_left_cancel₀ (by decide : (8 : ℤ) ≠ 0) <| by
    calc
    _ = (w + w) ^ 4 := by ring
    _ = 2 * (v ^ 4 - 1) := by rw [← hw, hu, hv, add_sub_cancel]
    _ = 2 * (v ^ 2 - 1) * (v ^ 2 + 1) := by ring
    _ = _ := by rw [ha]; ring
  obtain ⟨a, rfl⟩ : Even a := by
    by_contra h
    rw [← Int.odd_iff_not_even] at h
    obtain ⟨k, rfl⟩ := h
    replace ha : v ^ 2 = 3 + 4 * k := by convert ha using 1; ring
    replace ha : v ^ 2 % 4 = 3 := by rw [ha, Int.add_mul_emod_self_left]; rfl
    rcases v.even_or_odd with ⟨v', rfl⟩ | ⟨v', rfl⟩
    · replace ha : (4 * v' ^ 2) % 4 = 3 := by convert ha using 2; ring
      rw [Int.mul_emod_right] at ha
      contradiction
    · replace ha : (1 + 4 * (v' ^ 2 + v')) % 4 = 3 := by convert ha using 2; ring
      rw [Int.add_mul_emod_self_left] at ha
      contradiction
  replace ha : v ^ 2 = 4 * a + 1 := by rw [ha]; ring
  replace hwa : a * (2 * a + 1) = w ^ 4 := mul_left_cancel₀ (by decide : (2 : ℤ) ≠ 0) <| by
    rw [hwa]; ring
  have ha2a1_co : IsCoprime a (2 * a + 1) := isCoprime_one_right.mul_add_right_right _
  have ha₀ : a ≥ 0 := by
    by_contra h
    rw [ge_iff_le, not_le, Int.lt_iff_add_one_le] at h
    replace h := sub_le_sub_right (mul_nonpos_of_nonneg_of_nonpos (by decide : (0 : ℤ) ≤ 4) h) 3
    replace h : v ^ 2 ≤ -3 := by rw [ha]; convert h using 1; ring
    have := le_trans (sq_nonneg v) h
    contradiction
  replace ha₀ : a > 0 := by
    rcases lt_or_eq_of_le ha₀ with h | rfl
    · exact h
    replace hv : (v ^ 2) ^ 2 = s + 1 := by convert hv using 1; ring
    rw [ha, mul_zero, zero_add, one_pow, self_eq_add_left] at hv
    exact (hs₀.ne hv.symm).elim
  have ⟨b, hb⟩ := exists_associated_pow_of_mul_eq_pow' ha2a1_co hwa
  replace hb := Int.eq_of_associated_of_nonneg hb (pow_bit0_nonneg b 2) ha₀.le
  wlog hb₀ : b > 0 generalizing b hb
  · rw [not_lt, le_iff_lt_or_eq] at hb₀
    rcases hb₀ with hb₀ | rfl
    · exact this (-b) (by rwa [Even.neg_pow (by decide)]) (by rwa [gt_iff_lt, Left.neg_pos_iff])
    · rw [zero_pow (by decide)] at hb; exact ha₀.ne hb
  have ⟨c, hc⟩ := exists_associated_pow_of_mul_eq_pow' ha2a1_co.symm (mul_comm a _ ▸ hwa)
  replace hc := Int.eq_of_associated_of_nonneg hc (pow_bit0_nonneg c 2) (by positivity)
  have hbc : 2 * b ^ 4 + 1 = (c ^ 2) ^ 2 := by rw [hb, ← hc]; ring
  apply hx_min hbc hb₀
  refine (lt_of_pow_lt_pow 4 hx.le ?_)
  rw [← mul_lt_mul_left (by decide : (0 : ℤ) < 2), ← add_lt_add_iff_right 1, hbc, hxy, sq_lt_sq,
    abs_of_nonneg (sq_nonneg c), abs_of_nonneg hy₀.le]
  calc
    _ ≤ 2 * a + 1 := by rw [← hc]; convert Int.le_self_sq _ using 1; ring
    _ < v ^ 2 := by
      rw [ha]
      convert add_lt_add_right ((mul_lt_mul_left (by decide : (0 : ℤ) < 2)).2 ha₀) (2 * a + 1)
        using 1 <;> ring
    _ ≤ s + 1 := by rw [← hv]; convert Int.le_self_sq _ using 1; ring
    _ < y := by rw [hys, add_lt_add_iff_right]; apply lt_mul_left hs₀; decide
termination_by _ x _ _ _ => x.natAbs

/-- Lemma 2, alternate form. -/
theorem two_mul_pow_four_add_one_ne_sq' {x y : ℤ} (hxy : 2 * x ^ 4 + 1 = y ^ 2) : x = 0 := by
  by_contra h
  cases' ne_iff_lt_or_gt.1 h with h h
  · apply two_mul_pow_four_add_one_ne_sq (x := -x) (y := y)
    rwa [Even.neg_pow (by decide)]
    rwa [gt_iff_lt, Left.neg_pos_iff]
  · exact two_mul_pow_four_add_one_ne_sq hxy h

/-- Lemma 3. -/
theorem eight_pow_four_add_one {x y : ℤ} (hxy : 8 * x ^ 4 + 1 = y ^ 2) (hx : x > 0) : x = 1 := by
  rcases y.even_or_odd with ⟨s, rfl⟩ | ⟨s, rfl⟩
  · rw [← eq_sub_iff_add_eq'] at hxy
    have : Even 1 := ⟨2 * s ^ 2 - 4 * x ^ 4, by rw [hxy]; ring⟩
    contradiction
  replace hxy : 2 * x ^ 4 = s * (s + 1) := by
    apply mul_left_cancel₀ (by decide : (4 : ℤ) ≠ 0)
    apply add_right_cancel (b := 1)
    convert hxy using 1 <;> ring
  wlog hs₀ : s ≥ 0 generalizing s hxy
  · apply this (-s - 1) (by rw [hxy]; ring)
    rw [ge_iff_le, not_le] at hs₀
    rw [ge_iff_le, sub_nonneg, le_neg]
    exact Int.le_sub_one_of_lt hs₀
  rcases s.even_or_odd with ⟨s, rfl⟩ | ⟨s, rfl⟩
  · replace hxy : s * (2 * s + 1) = x ^ 4 := by
      apply mul_left_cancel₀ (by decide : (2 : ℤ) ≠ 0); rw [hxy]; ring
    replace hs₀ : s ≥ 0 := nonneg_of_mul_nonneg_right ((two_mul s).symm ▸ hs₀) (by decide)
    have hs_2s1_co : IsCoprime s (2 * s + 1) := isCoprime_one_right.mul_add_right_right _
    have ⟨u, hu⟩ := exists_associated_pow_of_mul_eq_pow' hs_2s1_co hxy
    replace hu := Int.eq_of_associated_of_nonneg hu (pow_bit0_nonneg u 2) hs₀
    have ⟨v, hv⟩ := exists_associated_pow_of_mul_eq_pow' hs_2s1_co.symm (mul_comm s _ ▸ hxy)
    replace hv := Int.eq_of_associated_of_nonneg hv (pow_bit0_nonneg v 2) (by positivity)
    replace hv : 2 * u ^ 4 + 1 = (v ^ 2) ^ 2 := by rw [hu, ← hv]; ring
    rcases two_mul_pow_four_add_one_ne_sq' hv
    rw [zero_pow (by decide)] at hu; rcases hu
    symm at hxy; rw [zero_mul, pow_eq_zero_iff (by decide)] at hxy
    exact (hx.ne hxy.symm).elim
  replace hxy : (s + 1) * (2 * s + 1) = x ^ 4 := by
    apply mul_left_cancel₀ (by decide : (2 : ℤ) ≠ 0); rw [hxy]; ring
  replace hs₀ : s ≥ 0 := by
    by_contra h
    rw [ge_iff_le, not_le, Int.lt_iff_add_one_le] at h
    replace h := sub_le_sub_right (mul_nonpos_of_nonneg_of_nonpos (by decide : (0 : ℤ) ≤ 2) h) 1
    replace h : 2 * s + 1 ≤ -1 := by convert h using 1; ring
    have := le_trans hs₀ h
    contradiction
  have hs1_2s1_co : IsCoprime (s + 1) (2 * s + 1) := by
    convert (isCoprime_one_right (x := s + 1)).neg_right.mul_add_right_right 2 using 1; ring
  have ⟨u, hu⟩ := exists_associated_pow_of_mul_eq_pow' hs1_2s1_co.symm (mul_comm (s + 1) _ ▸ hxy)
  replace hu := Int.eq_of_associated_of_nonneg hu (pow_bit0_nonneg u 2) (by positivity)
  have ⟨v, hv⟩ := exists_associated_pow_of_mul_eq_pow' hs1_2s1_co hxy
  replace hv := Int.eq_of_associated_of_nonneg hv (pow_bit0_nonneg v 2) (by positivity)
  have huv : u ^ 4 + 1 = 2 * v ^ 4 := by rw [hu, hv]; ring
  have ⟨u', hu'⟩ : Odd u := (Int.odd_pow' (by decide)).1 ⟨s, hu⟩
  have ⟨v', hv'⟩ : Odd v := by -- todo: check if `Odd v` is needed anywhere
    by_contra h
    rw [← Int.even_iff_not_odd] at h
    obtain ⟨a, rfl⟩ := h
    -- Do cases on `v^4 = 2 * (u^4 + 1)` mod 4. This is ugly, but I don't know how to shorten it.
    have : (u ^ 4 + 1) % 4 = 2 * (a + a) ^ 4 % 4 := by rw [huv]
    have ha : 2 * (a + a) ^ 4 % 4 = 0 := by
      suffices 4 * (8*a^4) % 4 = 0 by convert this using 2; ring
      apply Int.mul_emod_right
    rw [ha] at this
    have hu₀ : Even u → (u ^ 4 + 1) % 4 = 1 := by
      rintro ⟨x, rfl⟩
      suffices (1 + 4 * (4*x^4)) % 4 = 1 by convert this using 2; ring
      simp only [Int.add_mul_emod_self_left]
    have hu₁ : Odd u → (u ^ 4 + 1) % 4 = 2 := by
      rintro ⟨x, rfl⟩
      suffices (2 + 4 * (4*x^4 + 8*x^3 + 6*x^2 + 2*x)) % 4 = 2 by convert this using 2; ring
      simp only [Int.add_mul_emod_self_left]
    cases' u.even_or_odd with h₁ h₁ <;> [rw [hu₀ h₁] at this; rw [hu₁ h₁] at this] <;> contradiction
  -- Directly show that `(v^4 - u^2)/2` and `(v^4 + u^2)/2` are squares
  have ⟨w₁, hw₁⟩ : ∃ w, 2 * (v ^ 4 - u ^ 2) = (2 * w) ^ 2 :=
    ⟨2*u'^2 + 2*u', by rw [mul_sub_left_distrib, ← huv, hu']; ring⟩
  have ⟨w₂, hw₂⟩ : ∃ w, 2 * (v ^ 4 + u ^ 2) = (2 * w) ^ 2 :=
    ⟨2*u'^2 + 2*u' + 1, by rw [left_distrib, ← huv, hu']; ring⟩
  have h₁ : (v ^ 2 - u) ^ 2 + (v ^ 2 + u) ^ 2 = (2 * w₂) ^ 2 := by rw [← hw₂]; ring
  have h₂ : (v ^ 2 - u) * (v ^ 2 + u) = 2 * w₁ * w₁ :=
    mul_left_cancel₀ (by decide : (2 : ℤ) ≠ 0) (by linear_combination hw₁)
  have hv4 : v ^ 4 = u ^ 2 := by
    cases' pythagoreanTriple_area_ne_sq'
      ⟨2 * w₂, by simp_rw [PythagoreanTriple, ← pow_two]; exact h₁⟩ h₂ with h h
    · rw [sub_eq_zero] at h; rw [← h]; ring
    · rw [add_comm, ← sub_neg_eq_add, sub_eq_zero] at h; rw [h]; ring
  rw [hv4] at huv
  -- Start solving.
  replace huv : (u ^ 2 - 1) ^ 2 = 0 := by linear_combination huv
  rw [sq_eq_zero_iff, sub_eq_zero] at huv
  rw [← mul_one 1, ← huv] at hu
  replace hu : 0 = 2 * s := by linear_combination hu
  simp only [zero_eq_mul, false_or] at hu
  rcases hu
  replace hxy : (x ^ 2) ^ 2 = 1 := by linear_combination hxy.symm
  rw [sq_eq_one_iff, sq_eq_one_iff] at hxy
  rcases hxy with (rfl | rfl) | h
  · rfl
  · contradiction
  · have := h ▸ sq_nonneg x
    contradiction

/-- Suppose `x` and `y` are coprime and `x * y` is 3 times a square. Also suppose `x ≥ 0`.
Then `x % 3 ≠ 2`. -/
theorem mul_eq_three_sq {x y w : ℤ} (hco : IsCoprime x y) (h : x * y = 3 * w ^ 2) (hx : x ≥ 0) :
    x % 3 ≠ 2 := by
  rcases Int.prime_three.dvd_or_dvd ⟨w ^ 2, h⟩ with ⟨k, rfl⟩ | ⟨k, rfl⟩
  · rw [Int.mul_emod_right]; decide
  replace h : x * k = w ^ 2 := mul_left_cancel₀ (by decide : (3 : ℤ) ≠ 0) (by linear_combination h)
  have ⟨u, hu⟩ := exists_associated_pow_of_mul_eq_pow' hco.of_mul_right_right h
  replace hu := Int.eq_of_associated_of_nonneg hu (sq_nonneg u) hx
  rw [← hu, pow_two]
  mod_cases hu3 : u % 3 <;> rw [hu3.mul hu3] <;> decide

/-- Theorem 3½. `x = 24` is the only even solution to the cannonball problem. -/
theorem cannonball_even_24 {x y : ℤ} (h : x * (x + 1) * (2 * x + 1) = 6 * y ^ 2) (hx : x > 0)
    (hx_even : Even x) : x = 24 := by
  have hx_div : 3 ∣ x := by
    obtain ⟨x', hx'⟩ := hx_even
    replace h : (x + 1) * ((2 * x + 1) * x') = 3 * y ^ 2 := by
      apply mul_left_cancel₀ (by decide : (2 : ℤ) ≠ 0)
      rw [hx'] at h ⊢
      linear_combination h
    have hco12 : IsCoprime (x + 1) (2 * x + 1) := by
      convert (isCoprime_one_right (x := x + 1)).neg_right.mul_add_right_right 2 using 1; ring
    have hco13 : IsCoprime (x + 1) x' := by
      rw [hx']; convert (isCoprime_one_left (x := x')).mul_add_right_left 2 using 1; ring
    have hco23 : IsCoprime (2 * x + 1) x' := by
      rw [hx']; convert (isCoprime_one_left (x := x')).mul_add_right_left 4 using 1; ring
    mod_cases hx3 : x % 3
    · exact Int.modEq_zero_iff_dvd.1 hx3
    · absurd mul_eq_three_sq (hco12.mul_right hco13) h (by positivity)
      exact hx3.add_right 1
    · absurd mul_eq_three_sq (hco12.symm.mul_right hco23) (mul_left_comm _ _ x' ▸ h) (by positivity)
      exact (hx3.mul_left 2).add_right 1
  obtain ⟨x, rfl⟩ : 6 ∣ x := by
    have : IsCoprime (2 : ℤ) 3 := (isCoprime_one_right (R := ℤ)).mul_add_right_right 1
    exact this.mul_dvd hx_even.two_dvd hx_div
  clear hx_even hx_div
  replace h : x * (6 * x + 1) * (12 * x + 1) = y ^ 2 :=
    mul_left_cancel₀ (by decide : (6 : ℤ) ≠ 0) (by linear_combination h)
  replace hx := pos_of_mul_pos_right hx (by decide)
  have hco12 : IsCoprime x (6 * x + 1) := isCoprime_one_right.mul_add_right_right _
  have hco13 : IsCoprime x (12 * x + 1) := isCoprime_one_right.mul_add_right_right _
  have hco23 : IsCoprime (6 * x + 1) (12 * x + 1) := by
    convert (isCoprime_one_right (x := 6 * x + 1)).neg_right.mul_add_right_right 2 using 1; ring
  have ⟨qp, r, hqp₀, hr₀, hqp, hr⟩ :=
    pos_sq_of_coprime (hco13.mul_left hco23) h (by positivity) (by positivity)
  have ⟨q, p, hq₀, hp₀, hq, hp⟩ := pos_sq_of_coprime hco12 hqp (by positivity) (by positivity)
  clear qp hqp₀ hqp
  have hqrp : 6 * q ^ 2 = (r + p) * (r - p) := by rw [← sq_sub_sq, ← hq, ← hr, ← hp]; ring
  have hp_odd : Odd p :=
    (Int.odd_pow' (by decide)).1 (hp ▸ ((by decide : Even (6 : ℤ)).mul_right x).add_one)
  have hr_odd : Odd r :=
    (Int.odd_pow' (by decide)).1 (hr ▸ ((by decide : Even (12 : ℤ)).mul_right x).add_one)
  have hrp₁_even := hr_odd.add_odd hp_odd
  have hrp₂_even := hr_odd.sub_odd hp_odd
  have ⟨rp₁, hrp₁⟩ := hrp₁_even
  have ⟨rp₂, hrp₂⟩ := hrp₂_even
  have hrp₁₀ : rp₁ > 0 := by
    refine pos_of_mul_pos_right ?_ (by decide : (0 : ℤ) ≤ 2)
    rw [two_mul, ← hrp₁]
    positivity
  have hrp₂₀ : rp₂ > 0 := by
    have := hqrp ▸ mul_pos (by decide) (sq_pos_of_pos hq₀)
    have := hrp₂ ▸ pos_of_mul_pos_right this (by positivity : 0 ≤ r + p)
    exact pos_of_mul_pos_right ((two_mul rp₂).symm ▸ this) (by decide : (0 : ℤ) ≤ 2)
  rw [hrp₁, hrp₂] at hqrp
  obtain ⟨q, rfl⟩ : Even q := by
    have : Even (3 * q ^ 2) :=
      ⟨rp₁ * rp₂, mul_left_cancel₀ (by decide : (2 : ℤ) ≠ 0) (by linear_combination hqrp)⟩
    simpa [Int.even_mul, Int.even_pow'] using this
  replace hqrp : rp₁ * rp₂ = 2 * (3 * q ^ 2) :=
    mul_left_cancel₀ (by decide : (4 : ℤ) ≠ 0) (by linear_combination -hqrp)
  have hrp₁₂_co : IsCoprime rp₁ rp₂ := by
    rw [hp, hr, IsCoprime.pow_iff (by decide) (by decide)] at hco23
    -- Use `hco23`, `hp_odd`, `hr_odd`
    -- Note: This is similar to `hrs_sub_add_co` in Lemma 1, but I don't know how to join the two.
    have hr' : r = rp₁ + rp₂ :=
      mul_left_cancel₀ (by decide : (2 : ℤ) ≠ 0) (by linear_combination hrp₁+hrp₂)
    have hp' : p = rp₁ - rp₂ :=
      mul_left_cancel₀ (by decide : (2 : ℤ) ≠ 0) (by linear_combination hrp₁-hrp₂)
    rw [hr', hp', ← IsCoprime.add_mul_left_left_iff (z := 1), mul_one,
      sub_add_add_cancel, ← two_mul, IsCoprime.mul_left_iff] at hco23
    replace hco23 := hco23.2
    convert hco23.mul_add_left_right (-1) using 1
    ring
  -- and then do cases on `rp₁` and `rp₂`
  rcases Int.prime_two.dvd_or_dvd ⟨_, hqrp⟩ with h₂ | h₂ <;>
    rcases Int.prime_three.dvd_or_dvd ⟨_, mul_left_comm _ _ (q ^ 2) ▸ hqrp⟩ with h₃ | h₃
  · obtain ⟨aa, rfl⟩ : 6 ∣ rp₁ :=
      ((isCoprime_one_right (x := (2 : ℤ))).add_mul_left_right 1).mul_dvd h₂ h₃
    replace hqrp : aa * rp₂ = q ^ 2 :=
      mul_left_cancel₀ (by decide : (6 : ℤ) ≠ 0) (by linear_combination hqrp)
    rw [hq, ← two_mul, mul_pow, ← hqrp]
    replace hrp₁₀ : aa > 0 := pos_of_mul_pos_right hrp₁₀ (by decide)
    have ⟨a, ha⟩ := exists_associated_pow_of_mul_eq_pow' hrp₁₂_co.of_mul_left_right hqrp
    rcases Int.eq_of_associated_of_nonneg ha (sq_nonneg a) (by positivity)
    have ⟨b, hb⟩ :=
      exists_associated_pow_of_mul_eq_pow' hrp₁₂_co.of_mul_left_right.symm (mul_comm _ rp₂ ▸ hqrp)
    replace hb := Int.eq_of_associated_of_nonneg hb (sq_nonneg b) (by positivity)
    wlog hb₀ : b > 0 generalizing b
    · rw [not_lt, le_iff_lt_or_eq] at hb₀
      rcases hb₀ with hb₀ | rfl
      · exact this (-b) (by rwa [Even.neg_pow (by decide)]) (by rwa [gt_iff_lt, Left.neg_pos_iff])
      · rw [zero_pow (by decide)] at hb; exact (hrp₂₀.ne hb).elim
    rcases hb
    have hp2 : p = 6 * a ^ 2 - b ^ 2 :=
      mul_left_cancel₀ (by decide : (2 : ℤ) ≠ 0) (by linear_combination hrp₁ - hrp₂)
    have h : 24 * a ^ 2 * b ^ 2 + 1 = (6 * a ^ 2 - b ^ 2) ^ 2 := by
      rw [mul_assoc, hqrp, ← hp2, ← hp, hq]; ring
    replace h : 8 * b ^ 4 + 1 = (6 * a ^ 2 - 3 * b ^ 2) ^ 2 := by
      rw [← eq_sub_iff_add_eq'] at h ⊢
      linear_combination h
    rcases eight_pow_four_add_one h hb₀
    replace h : 0 = a ^ 2 * (a ^ 2 - 1) :=
      mul_left_cancel₀ (by decide : (36 : ℤ) ≠ 0) (by linear_combination h)
    rcases zero_eq_mul.1 h with h | h
    · exact (hrp₁₀.ne h.symm).elim
    · rw [sub_eq_iff_eq_add.1 h]; rfl
  · obtain ⟨aa, rfl⟩ := h₃
    obtain ⟨bb, rfl⟩ := h₂
    replace hrp₂₀ : aa > 0 := pos_of_mul_pos_right hrp₂₀ (by decide)
    replace hrp₁₀ : bb > 0 := pos_of_mul_pos_right hrp₁₀ (by decide)
    replace hqrp : aa * bb = q ^ 2 :=
      mul_left_cancel₀ (by decide : (6 : ℤ) ≠ 0) (by linear_combination hqrp)
    replace hrp₁₂_co := hrp₁₂_co.of_mul_left_right.of_mul_right_right
    have hp2 : p = 2 * bb - 3 * aa :=
      mul_left_cancel₀ (by decide : (2 : ℤ) ≠ 0) (by linear_combination hrp₁ - hrp₂)
    have h : 24 * aa * bb + 1 = (2 * bb - 3 * aa) ^ 2 := by
      rw [mul_assoc, hqrp, ← hp2, ← hp, hq]; ring
    have ⟨a, ha⟩ := exists_associated_pow_of_mul_eq_pow' hrp₁₂_co.symm hqrp
    rcases Int.eq_of_associated_of_nonneg ha (sq_nonneg a) (by positivity)
    have ⟨b, hb⟩ := exists_associated_pow_of_mul_eq_pow' hrp₁₂_co (mul_comm _ bb ▸ hqrp)
    rcases Int.eq_of_associated_of_nonneg hb (sq_nonneg b) (by positivity)
    replace h : 2 * (2 * b) ^ 4 + 1 = (3 * a ^ 2 - 6 * b ^ 2) ^ 2 := by
      rw [← eq_sub_iff_add_eq'] at h ⊢
      linear_combination h
    have := two_mul_pow_four_add_one_ne_sq' h
    simp only [mul_eq_zero, false_or] at this
    rcases this
    contradiction
  · -- Essentially a copy-paste of the `2 ∣ rp₁` `3 ∣ rp₂` case
    obtain ⟨aa, rfl⟩ := h₃
    obtain ⟨bb, rfl⟩ := h₂
    replace hrp₁₀ : aa > 0 := pos_of_mul_pos_right hrp₁₀ (by decide)
    replace hrp₂₀ : bb > 0 := pos_of_mul_pos_right hrp₂₀ (by decide)
    replace hqrp : aa * bb = q ^ 2 :=
      mul_left_cancel₀ (by decide : (6 : ℤ) ≠ 0) (by linear_combination hqrp)
    replace hrp₁₂_co := hrp₁₂_co.of_mul_left_right.of_mul_right_right
    have hp2 : p = 3 * aa - 2 * bb :=
      mul_left_cancel₀ (by decide : (2 : ℤ) ≠ 0) (by linear_combination hrp₁ - hrp₂)
    have h : 24 * aa * bb + 1 = (3 * aa - 2 * bb) ^ 2 := by
      rw [mul_assoc, hqrp, ← hp2, ← hp, hq]; ring
    have ⟨a, ha⟩ := exists_associated_pow_of_mul_eq_pow' hrp₁₂_co hqrp
    rcases Int.eq_of_associated_of_nonneg ha (sq_nonneg a) (by positivity)
    have ⟨b, hb⟩ := exists_associated_pow_of_mul_eq_pow' hrp₁₂_co.symm (mul_comm _ bb ▸ hqrp)
    rcases Int.eq_of_associated_of_nonneg hb (sq_nonneg b) (by positivity)
    replace h : 2 * (2 * b) ^ 4 + 1 = (3 * a ^ 2 - 6 * b ^ 2) ^ 2 := by
      rw [← eq_sub_iff_add_eq'] at h ⊢
      linear_combination h
    have := two_mul_pow_four_add_one_ne_sq' h
    simp only [mul_eq_zero, false_or] at this
    rcases this
    contradiction
  · -- Essentially a copy-paste of the `2 ∣ rp₁` `3 ∣ rp₁` case
    obtain ⟨aa, rfl⟩ : 6 ∣ rp₂ :=
      ((isCoprime_one_right (x := (2 : ℤ))).add_mul_left_right 1).mul_dvd h₂ h₃
    replace hqrp : aa * rp₁ = q ^ 2 :=
      mul_left_cancel₀ (by decide : (6 : ℤ) ≠ 0) (by linear_combination hqrp)
    rw [hq, ← two_mul, mul_pow, ← hqrp]
    replace hrp₂₀ : aa > 0 := pos_of_mul_pos_right hrp₂₀ (by decide)
    have ⟨a, ha⟩ := exists_associated_pow_of_mul_eq_pow' hrp₁₂_co.of_mul_right_right.symm hqrp
    rcases Int.eq_of_associated_of_nonneg ha (sq_nonneg a) (by positivity)
    have ⟨b, hb⟩ :=
      exists_associated_pow_of_mul_eq_pow' hrp₁₂_co.of_mul_right_right (mul_comm _ rp₁ ▸ hqrp)
    replace hb := Int.eq_of_associated_of_nonneg hb (sq_nonneg b) (by positivity)
    wlog hb₀ : b > 0 generalizing b
    · rw [not_lt, le_iff_lt_or_eq] at hb₀
      rcases hb₀ with hb₀ | rfl
      · exact this (-b) (by rwa [Even.neg_pow (by decide)]) (by rwa [gt_iff_lt, Left.neg_pos_iff])
      · rw [zero_pow (by decide)] at hb; exact (hrp₁₀.ne hb).elim
    rcases hb
    have hp2 : p = b ^ 2 - 6 * a ^ 2 :=
      mul_left_cancel₀ (by decide : (2 : ℤ) ≠ 0) (by linear_combination hrp₁ - hrp₂)
    have h : 24 * a ^ 2 * b ^ 2 + 1 = (b ^ 2 - 6 * a ^ 2) ^ 2 := by
      rw [mul_assoc, hqrp, ← hp2, ← hp, hq]; ring
    replace h : 8 * b ^ 4 + 1 = (6 * a ^ 2 - 3 * b ^ 2) ^ 2 := by
      rw [← eq_sub_iff_add_eq'] at h ⊢
      linear_combination h
    rcases eight_pow_four_add_one h hb₀
    replace h : 0 = a ^ 2 * (a ^ 2 - 1) :=
      mul_left_cancel₀ (by decide : (36 : ℤ) ≠ 0) (by linear_combination h)
    rcases zero_eq_mul.1 h with h | h
    · exact (hrp₂₀.ne h.symm).elim
    · rw [sub_eq_iff_eq_add.1 h]; rfl






