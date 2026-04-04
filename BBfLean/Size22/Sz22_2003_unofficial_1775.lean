import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #1775: [9/10, 275/21, 44/3, 7/11, 3/2]

Vector representation:
```
-1  2 -1  0  0
 0 -1  2 -1  1
 2 -1  0  0  1
 0  0  0  1 -1
-1  1  0  0  0
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_1775

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a+1, b, c+1, d, e⟩ => some ⟨a, b+2, c, d, e⟩
  | ⟨a, b+1, c, d+1, e⟩ => some ⟨a, b, c+2, d, e+1⟩
  | ⟨a, b+1, c, d, e⟩ => some ⟨a+2, b, c, d, e+1⟩
  | ⟨a, b, c, d, e+1⟩ => some ⟨a, b, c, d+1, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b+1, c, d, e⟩
  | _ => none

theorem e_to_d : ∀ k, ∀ d, ⟨a, 0, 0, d, k⟩ [fm]⊢* ⟨a, 0, 0, d + k, 0⟩ := by
  intro k; induction k with
  | zero => intro d; exists 0
  | succ k ih =>
    intro d
    rw [show d + (k + 1) = (d + 1) + k from by ring]
    step fm
    exact ih (d + 1)

theorem r3_chain : ∀ k, ∀ a e, ⟨a, k, 0, 0, e⟩ [fm]⊢* ⟨a + 2 * k, 0, 0, 0, e + k⟩ := by
  intro k; induction k with
  | zero => intro a e; simp; exists 0
  | succ k ih =>
    intro a e
    step fm
    apply stepStar_trans (ih (a + 2) (e + 1))
    ring_nf; finish

theorem r1r1r2_chain : ∀ k, ∀ a b d e,
    ⟨a + 2 * k, b, 2, d + k, e⟩ [fm]⊢* ⟨a, b + 3 * k, 2, d, e + k⟩ := by
  intro k; induction k with
  | zero => intro a b d e; simp; exists 0
  | succ k ih =>
    intro a b d e
    rw [show a + 2 * (k + 1) = (a + 2) + 2 * k from by ring,
        show d + (k + 1) = (d + 1) + k from by ring]
    apply stepStar_trans (ih (a + 2) b (d + 1) e)
    step fm; step fm; step fm
    ring_nf; finish

theorem cleanup_a2 : ⟨a + 2, b, 2, 0, e⟩ [fm]⊢* ⟨a + 2 * b + 8, 0, 0, 0, e + b + 4⟩ := by
  step fm; step fm
  apply stepStar_trans (r3_chain (b + 4) a e)
  ring_nf; finish

theorem cleanup_a1 : ⟨1, b, 2, 0, e⟩ [fm]⊢* ⟨2 * b + 7, 0, 0, 0, e + b + 4⟩ := by
  step fm; step fm; step fm
  apply stepStar_trans (r3_chain (b + 3) 1 (e + 1))
  ring_nf; finish

theorem r2_drain : ∀ k, ∀ b c e, ⟨0, b + k, c, k, e⟩ [fm]⊢* ⟨0, b, c + 2 * k, 0, e + k⟩ := by
  intro k; induction k with
  | zero => intro b c e; simp; exists 0
  | succ k ih =>
    intro b c e
    rw [show b + (k + 1) = b + k + 1 from by ring]
    step fm
    rw [show b + k = b + k from rfl]
    apply stepStar_trans (ih b (c + 2) (e + 1))
    ring_nf; finish

theorem r3r1r1_chain : ∀ k, ∀ b e, ⟨0, b + 1, 2 * k + 2, 0, e⟩ [fm]⊢* ⟨0, b + 3 * k + 4, 0, 0, e + k + 1⟩ := by
  intro k; induction k with
  | zero => intro b e; step fm; step fm; step fm; finish
  | succ k ih =>
    intro b e
    rw [show 2 * (k + 1) + 2 = (2 * k + 2) + 1 + 1 from by ring]
    step fm; step fm; step fm
    apply stepStar_trans (ih (b + 3) (e + 1))
    ring_nf; finish

theorem r3r1_odd_chain : ∀ k, ∀ b e, ⟨0, b + 1, 2 * k + 1, 0, e⟩ [fm]⊢* ⟨1, b + 3 * k + 2, 0, 0, e + k + 1⟩ := by
  intro k; induction k with
  | zero => intro b e; step fm; step fm; finish
  | succ k ih =>
    intro b e
    rw [show 2 * (k + 1) + 1 = (2 * k + 1) + 1 + 1 from by ring]
    step fm; step fm; step fm
    apply stepStar_trans (ih (b + 3) (e + 1))
    ring_nf; finish

-- Case a+1 = 2m (even): (2m, 0, 2, d, 1) with d >= m.
-- After m R1R1R2 rounds: (0, 3m, 2, d-m, m+1).
-- R2 drain (d-m): (0, 4m-d, 2(d-m)+2, 0, d+1).
-- c = 2(d-m)+2 = 2(d-m+1) even. r3r1r1_chain (d-m): b+1 = 4m-d, b = 4m-d-1.
-- Result: (0, (4m-d-1)+3(d-m)+4, 0, 0, d+1+(d-m)+1) = (0, m+2d+3, 0, 0, 2d-m+2).
-- Wait: 4m-d-1+3(d-m)+4 = 4m-d-1+3d-3m+4 = m+2d+3. YES.
-- R3 chain (m+2d+3): (0+2(m+2d+3), 0, 0, 0, 2d-m+2+m+2d+3) = (2m+4d+6, 0, 0, 0, 4d+5).
-- Expected: a+4d+7 = (2m-1)+4d+7 = 2m+4d+6. YES!
-- But 4m-d >= 1 is needed for b+1 form. 4m >= d+1. Since 2m >= d+1 (m >= 1, d >= m), 4m >= 2d+2 > d+1. YES.
-- Also need 4m-d >= 1 for r2_drain: 3m = (4m-d) + (d-m), need 4m-d >= 0. Since 2m >= d, 4m >= 2d >= d. YES.
theorem main_trans_a1even (m d : ℕ) (hm : m ≥ 1) (hd : d ≥ m) (hd2 : d ≤ 2 * m) :
    ⟨2 * m, 0, 2, d, 1⟩ [fm]⊢* ⟨2 * m + 4 * d + 6, 0, 0, 0, 4 * d + 5⟩ := by
  rw [show 2 * m = 0 + 2 * m from by ring,
      show d = (d - m) + m from by omega]
  apply stepStar_trans (r1r1r2_chain m 0 0 (d - m) 1)
  simp only [Nat.zero_add]; rw [show 1 + m = m + 1 from by ring, show d - m + m = d from by omega]
  rw [show 3 * m = (4 * m - d) + (d - m) from by omega]
  apply stepStar_trans (r2_drain (d - m) (4 * m - d) 2 (m + 1))
  rw [show 2 + 2 * (d - m) = 2 * (d - m) + 2 from by ring,
      show 4 * m - d = (4 * m - d - 1) + 1 from by omega]
  apply stepStar_trans (r3r1r1_chain (d - m) (4 * m - d - 1) (m + 1 + (d - m)))
  rw [show 4 * m - d - 1 + 3 * (d - m) + 4 = m + 2 * d + 3 from by omega]
  apply stepStar_trans (r3_chain (m + 2 * d + 3) 0 (m + 1 + (d - m) + (d - m) + 1))
  rw [show 0 + 2 * (m + 2 * d + 3) = 2 * m + 4 * d + 6 from by ring,
      show m + 1 + (d - m) + (d - m) + 1 + (m + 2 * d + 3) = 4 * d + 5 from by omega]
  finish

-- Case a+1 = 2m+1 (odd): (2m+1, 0, 2, d, 1) with d >= m.
-- After m R1R1R2 rounds: (1, 3m, 2, d-m, m+1).
-- R1: (0, 3m+2, 1, d-m, m+1).
-- R2 drain (d-m): (0, 4m-d+2, 2(d-m)+1, 0, d+1).
-- c = 2(d-m)+1 odd. r3r1_odd_chain (d-m): b+1 = 4m-d+2, b = 4m-d+1.
-- Result: (1, (4m-d+1)+3(d-m)+2, 0, 0, d+1+(d-m)+1) = (1, m+2d+3, 0, 0, 2d-m+2).
-- R3 chain (m+2d+3): (1+2(m+2d+3), 0, 0, 0, 2d-m+2+m+2d+3) = (2m+4d+7, 0, 0, 0, 4d+5).
-- Expected: a+4d+7 = 2m+4d+7. YES!
-- Need 4m-d+2 >= 1: always since 4m >= d. YES.
theorem main_trans_a1odd (m d : ℕ) (hd : d ≥ m) (hd2 : d ≤ 2 * m) :
    ⟨2 * m + 1, 0, 2, d, 1⟩ [fm]⊢* ⟨2 * m + 4 * d + 7, 0, 0, 0, 4 * d + 5⟩ := by
  rw [show 2 * m + 1 = 1 + 2 * m from by ring,
      show d = (d - m) + m from by omega]
  apply stepStar_trans (r1r1r2_chain m 1 0 (d - m) 1)
  simp only [Nat.zero_add]; rw [show 1 + m = m + 1 from by ring, show d - m + m = d from by omega]
  step fm
  rw [show 3 * m + 2 = (4 * m - d + 2) + (d - m) from by omega]
  apply stepStar_trans (r2_drain (d - m) (4 * m - d + 2) 1 (m + 1))
  rw [show 1 + 2 * (d - m) = 2 * (d - m) + 1 from by ring,
      show 4 * m - d + 2 = (4 * m - d + 1) + 1 from by omega]
  apply stepStar_trans (r3r1_odd_chain (d - m) (4 * m - d + 1) (m + 1 + (d - m)))
  rw [show 4 * m - d + 1 + 3 * (d - m) + 2 = m + 2 * d + 3 from by omega]
  apply stepStar_trans (r3_chain (m + 2 * d + 3) 1 (m + 1 + (d - m) + (d - m) + 1))
  rw [show 1 + 2 * (m + 2 * d + 3) = 2 * m + 4 * d + 7 from by ring,
      show m + 1 + (d - m) + (d - m) + 1 + (m + 2 * d + 3) = 4 * d + 5 from by omega]
  finish

-- Case d < (a+1)/2: do d R1R1R2 rounds, then cleanup.
-- After d rounds from (a+1, 0, 2, d, 1): (a+1-2d, 3d, 2, 0, d+1).
-- a+1-2d >= 1 since a >= d and a+1 > 2d requires a >= 2d.
-- Actually a+1-2d >= 2 when a >= 2d+1, or = 1 when a = 2d.
theorem main_trans_hi (ha : a + 1 ≥ 2 * d + 1) :
    ⟨a + 1, 0, 2, d, 1⟩ [fm]⊢* ⟨a + 4 * d + 7, 0, 0, 4 * d + 5, 0⟩ := by
  have : ⟨a + 1, 0, 2, d, 1⟩ = (⟨(a + 1 - 2 * d) + 2 * d, 0, 2, 0 + d, 1⟩ : Q) := by
    simp; omega
  rw [this]
  apply stepStar_trans (r1r1r2_chain d (a + 1 - 2 * d) 0 0 1)
  simp only [Nat.zero_add]; rw [show 1 + d = d + 1 from by ring]
  -- a + 1 - 2d >= 1. Split: = 1 or >= 2.
  rcases (show a + 1 - 2 * d = 1 ∨ a + 1 - 2 * d ≥ 2 from by omega) with h1 | h2
  · -- a + 1 - 2d = 1, so a = 2d
    rw [show a + 1 - 2 * d = 1 from h1]
    apply stepStar_trans (cleanup_a1 (b := 3 * d) (e := d + 1))
    rw [show d + 1 + 3 * d + 4 = 4 * d + 5 from by ring,
        show 2 * (3 * d) + 7 = a + 4 * d + 7 from by omega]
    apply stepStar_trans (e_to_d (a := a + 4 * d + 7) (4 * d + 5) 0)
    simp; finish
  · -- a + 1 - 2d >= 2
    obtain ⟨r, hr⟩ := Nat.exists_eq_add_of_le (show 2 ≤ a + 1 - 2 * d from h2)
    rw [show a + 1 - 2 * d = r + 2 from by omega]
    apply stepStar_trans (cleanup_a2 (a := r) (b := 3 * d) (e := d + 1))
    rw [show d + 1 + 3 * d + 4 = 4 * d + 5 from by ring,
        show r + 2 * (3 * d) + 8 = a + 4 * d + 7 from by omega]
    apply stepStar_trans (e_to_d (a := a + 4 * d + 7) (4 * d + 5) 0)
    simp; finish

theorem main_trans (ha : a ≥ d) :
    ⟨a + 2, 0, 0, d + 1, 0⟩ [fm]⊢⁺ ⟨a + 4 * d + 7, 0, 0, 4 * d + 5, 0⟩ := by
  apply step_stepStar_stepPlus (show ⟨a + 2, 0, 0, d + 1, 0⟩ [fm]⊢ ⟨a + 1, 1, 0, d + 1, 0⟩ from by simp [fm])
  step fm
  rcases le_or_gt (2 * d + 1) (a + 1) with h | h
  · exact main_trans_hi h
  · -- a + 1 < 2*d + 1, i.e., a + 1 <= 2*d, i.e., a < 2*d.
    -- But also a >= d. So d <= a < 2d.
    rcases Nat.even_or_odd (a + 1) with ⟨m, hm⟩ | ⟨m, hm⟩
    · rw [show a + 1 = 2 * m from by omega]
      apply stepStar_trans (main_trans_a1even m d (by omega) (by omega) (by omega))
      apply stepStar_trans (e_to_d (a := 2 * m + 4 * d + 6) (4 * d + 5) 0)
      rw [show 0 + (4 * d + 5) = 4 * d + 5 from by ring,
          show a + 4 * d + 7 = 2 * m + 4 * d + 6 from by omega]; finish
    · rw [show a + 1 = 2 * m + 1 from by omega]
      apply stepStar_trans (main_trans_a1odd m d (by omega) (by omega))
      apply stepStar_trans (e_to_d (a := 2 * m + 4 * d + 7) (4 * d + 5) 0)
      rw [show 0 + (4 * d + 5) = 4 * d + 5 from by ring,
          show a + 4 * d + 7 = 2 * m + 4 * d + 7 from by omega]; finish

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨2, 0, 0, 1, 0⟩) (by execute fm 3)
  apply progress_nonhalt (fm := fm)
    (P := fun q ↦ ∃ a d, q = ⟨a + 2, 0, 0, d + 1, 0⟩ ∧ a ≥ d)
  · intro c ⟨a, d, hq, ha⟩; subst hq
    refine ⟨⟨a + 4 * d + 7, 0, 0, 4 * d + 5, 0⟩,
      ⟨a + 4 * d + 5, 4 * d + 4, ?_, ?_⟩, main_trans ha⟩
    · change (a + 4 * d + 7, 0, 0, 4 * d + 5, 0) = ((a + 4 * d + 5) + 2, 0, 0, (4 * d + 4) + 1, 0)
      simp
    · omega
  · exact ⟨0, 0, rfl, le_refl 0⟩
