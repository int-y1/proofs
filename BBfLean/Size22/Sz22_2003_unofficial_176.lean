import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #176: [1/45, 98/15, 33/7, 275/2, 3/11]

Vector representation:
```
 0 -2 -1  0  0
 1 -1 -1  2  0
 0  1  0 -1  1
-1  0  2  0  1
 0  1  0  0 -1
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_176

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a, b+2, c+1, d, e⟩ => some ⟨a, b, c, d, e⟩
  | ⟨a, b+1, c+1, d, e⟩ => some ⟨a+1, b, c, d+2, e⟩
  | ⟨a, b, c, d+1, e⟩ => some ⟨a, b+1, c, d, e+1⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b, c+2, d, e+1⟩
  | ⟨a, b, c, d, e+1⟩ => some ⟨a, b+1, c, d, e⟩
  | _ => none

-- R3 chain (c=0): (a, b, 0, d+k, e) →* (a, b+k, 0, d, e+k)
theorem d_to_b : ∀ k a b d e,
    ⟨a, b, 0, d + k, e⟩ [fm]⊢* ⟨a, b + k, (0 : ℕ), d, e + k⟩ := by
  intro k; induction k with
  | zero => intro a b d e; exists 0
  | succ k ih =>
    intro a b d e
    rw [show d + (k + 1) = (d + k) + 1 from by ring]
    step fm
    apply stepStar_trans (ih _ _ _ _)
    ring_nf; finish

-- R4 chain (b=0, d=0): (a+k, 0, c, 0, e) →* (a, 0, c+2k, 0, e+k)
theorem a_to_c : ∀ k a c e,
    ⟨a + k, 0, c, 0, e⟩ [fm]⊢* ⟨a, (0 : ℕ), c + 2 * k, 0, e + k⟩ := by
  intro k; induction k with
  | zero => intro a c e; exists 0
  | succ k ih =>
    intro a c e
    rw [show a + (k + 1) = (a + k) + 1 from by ring]
    step fm
    apply stepStar_trans (ih _ _ _)
    ring_nf; finish

-- R2+R3 alternating chain: k pairs
theorem r2r3_chain : ∀ k a c d e,
    ⟨a, 1, c + k, d, e⟩ [fm]⊢* ⟨a + k, (1 : ℕ), c, d + k, e + k⟩ := by
  intro k; induction k with
  | zero => intro a c d e; exists 0
  | succ k ih =>
    intro a c d e
    rw [show c + (k + 1) = (c + k) + 1 from by ring]
    step fm
    rw [show d + 2 = (d + 1) + 1 from by ring]
    step fm
    apply stepStar_trans (ih _ _ _ _)
    ring_nf; finish

-- R4,R1,R1 rounds
theorem r4r1r1_rounds : ∀ k a b e,
    ⟨a + k, b + 4 * k, 0, 0, e⟩ [fm]⊢* ⟨a, b, (0 : ℕ), 0, e + k⟩ := by
  intro k; induction k with
  | zero => intro a b e; exists 0
  | succ k ih =>
    intro a b e
    rw [show a + (k + 1) = (a + k) + 1 from by ring,
        show b + 4 * (k + 1) = (b + 4 * k) + 4 from by ring]
    step fm
    rw [show b + 4 * k + 4 = (b + 4 * k + 2) + 2 from by ring]
    step fm
    rw [show b + 4 * k + 2 = (b + 4 * k) + 2 from by ring]
    step fm
    apply stepStar_trans (ih _ _ _)
    ring_nf; finish

-- Phase 1: (0, 0, C+1, 0, E+1) ⊢* (C+1, C+2, 0, 0, E+2C+2)
theorem phase1 (C E : ℕ) :
    ⟨0, 0, C + 1, 0, E + 1⟩ [fm]⊢* ⟨C + 1, C + 2, (0 : ℕ), 0, E + 2 * C + 2⟩ := by
  step fm
  apply stepStar_trans (c₂ := ⟨C + 1, 1, 0, C + 1, E + C + 1⟩)
  · have h := r2r3_chain (C + 1) 0 0 0 E
    simp only [Nat.zero_add] at h
    rw [show E + (C + 1) = E + C + 1 from by ring] at h; exact h
  have h := d_to_b (C + 1) (C + 1) 1 0 (E + C + 1)
  simp only [Nat.zero_add] at h
  refine stepStar_trans h ?_
  ring_nf; finish

-- Tail b=2: (A+1, 2, 0, 0, F) →* (0, 0, 2A+1, 0, F+A+1)
theorem tail_b2 (A F : ℕ) :
    ⟨A + 1, 2, 0, 0, F⟩ [fm]⊢* ⟨(0 : ℕ), 0, 2 * A + 1, 0, F + A + 1⟩ := by
  step fm
  rw [show (2 : ℕ) = 0 + 2 from by ring]
  step fm
  have h := a_to_c A 0 1 (F + 1)
  simp only [Nat.zero_add] at h
  refine stepStar_trans h ?_
  ring_nf; finish

-- Tail b=3: (A+1, 3, 0, 0, F) →* (0, 0, 2A+1, 0, F+A+4)
theorem tail_b3 (A F : ℕ) :
    ⟨A + 1, 3, 0, 0, F⟩ [fm]⊢* ⟨(0 : ℕ), 0, 2 * A + 1, 0, F + A + 4⟩ := by
  step fm
  rw [show (3 : ℕ) = 1 + 2 from by ring]
  step fm
  rw [show (1 : ℕ) = 0 + 1 from by ring]
  step fm
  apply stepStar_trans (c₂ := ⟨A + 1, 2, 0, 0, F + 3⟩)
  · have h := d_to_b 2 (A + 1) 0 0 (F + 1)
    simp only [Nat.zero_add] at h
    refine stepStar_trans h ?_
    ring_nf; finish
  refine stepStar_trans (tail_b2 A (F + 3)) ?_
  ring_nf; finish

-- Tail b=1: (A+1, 1, 0, 0, F) →* (0, 0, 2A+3, 0, F+A+10)
theorem tail_b1 (A F : ℕ) :
    ⟨A + 1, 1, 0, 0, F⟩ [fm]⊢* ⟨(0 : ℕ), 0, 2 * A + 3, 0, F + A + 10⟩ := by
  step fm
  rw [show (1 : ℕ) = 0 + 1 from by ring, show (2 : ℕ) = 0 + 1 + 1 from by ring]
  step fm
  rw [show (2 : ℕ) = 1 + 1 from by ring]
  step fm
  rw [show (1 : ℕ) = 0 + 1 from by ring]
  step fm
  apply stepStar_trans (c₂ := ⟨A + 2, 3, 0, 0, F + 5⟩)
  · have h := d_to_b 3 (A + 2) 0 0 (F + 2)
    simp only [Nat.zero_add] at h
    refine stepStar_trans h ?_
    ring_nf; finish
  refine stepStar_trans (tail_b3 (A + 1) (F + 5)) ?_
  ring_nf; finish

-- Main transition C=4m+3:
-- (0, 0, 4m+3, 0, E+1) ⊢⁺ (0, 0, 6m+4, 0, E+12m+9)
theorem main_mod3 (m E : ℕ) :
    ⟨0, 0, 4 * m + 3, 0, E + 1⟩ [fm]⊢⁺ ⟨(0 : ℕ), 0, 6 * m + 4, 0, E + 12 * m + 9⟩ := by
  apply step_stepStar_stepPlus (c₂ := ⟨0, 1, 4 * m + 3, 0, E⟩)
  · simp [fm]
  apply stepStar_trans (c₂ := ⟨4 * m + 3, 4 * m + 4, 0, 0, E + 8 * m + 6⟩)
  · apply stepStar_trans (c₂ := ⟨4 * m + 3, 1, 0, 4 * m + 3, E + 4 * m + 3⟩)
    · have h := r2r3_chain (4 * m + 3) 0 0 0 E
      simp only [Nat.zero_add] at h
      refine stepStar_trans h ?_; ring_nf; finish
    have h := d_to_b (4 * m + 3) (4 * m + 3) 1 0 (E + 4 * m + 3)
    simp only [Nat.zero_add] at h
    refine stepStar_trans h ?_; ring_nf; finish
  apply stepStar_trans (c₂ := ⟨3 * m + 2, 0, 0, 0, E + 9 * m + 7⟩)
  · have h := r4r1r1_rounds (m + 1) (3 * m + 2) 0 (E + 8 * m + 6)
    rw [show 3 * m + 2 + (m + 1) = 4 * m + 3 from by ring,
        show 0 + 4 * (m + 1) = 4 * m + 4 from by ring] at h
    refine stepStar_trans h ?_; ring_nf; finish
  have h := a_to_c (3 * m + 2) 0 0 (E + 9 * m + 7)
  simp only [Nat.zero_add] at h
  refine stepStar_trans h ?_; ring_nf; finish

-- Main transition C=4m+2:
-- (0, 0, 4m+2, 0, E+1) ⊢⁺ (0, 0, 6m+3, 0, E+12m+9)
theorem main_mod2 (m E : ℕ) :
    ⟨0, 0, 4 * m + 2, 0, E + 1⟩ [fm]⊢⁺ ⟨(0 : ℕ), 0, 6 * m + 3, 0, E + 12 * m + 9⟩ := by
  apply step_stepStar_stepPlus (c₂ := ⟨0, 1, 4 * m + 2, 0, E⟩)
  · simp [fm]
  apply stepStar_trans (c₂ := ⟨4 * m + 2, 4 * m + 3, 0, 0, E + 8 * m + 4⟩)
  · apply stepStar_trans (c₂ := ⟨4 * m + 2, 1, 0, 4 * m + 2, E + 4 * m + 2⟩)
    · have h := r2r3_chain (4 * m + 2) 0 0 0 E
      simp only [Nat.zero_add] at h
      refine stepStar_trans h ?_; ring_nf; finish
    have h := d_to_b (4 * m + 2) (4 * m + 2) 1 0 (E + 4 * m + 2)
    simp only [Nat.zero_add] at h
    refine stepStar_trans h ?_; ring_nf; finish
  apply stepStar_trans (c₂ := ⟨3 * m + 2, 3, 0, 0, E + 9 * m + 4⟩)
  · have h := r4r1r1_rounds m (3 * m + 2) 3 (E + 8 * m + 4)
    rw [show 3 * m + 2 + m = 4 * m + 2 from by ring,
        show 3 + 4 * m = 4 * m + 3 from by ring] at h
    refine stepStar_trans h ?_; ring_nf; finish
  refine stepStar_trans (tail_b3 (3 * m + 1) (E + 9 * m + 4)) ?_
  ring_nf; finish

-- Main transition C=4m+4:
-- (0, 0, 4m+4, 0, E+1) ⊢⁺ (0, 0, 6m+7, 0, E+12m+21)
theorem main_mod0 (m E : ℕ) :
    ⟨0, 0, 4 * m + 4, 0, E + 1⟩ [fm]⊢⁺ ⟨(0 : ℕ), 0, 6 * m + 7, 0, E + 12 * m + 21⟩ := by
  apply step_stepStar_stepPlus (c₂ := ⟨0, 1, 4 * m + 4, 0, E⟩)
  · simp [fm]
  apply stepStar_trans (c₂ := ⟨4 * m + 4, 4 * m + 5, 0, 0, E + 8 * m + 8⟩)
  · apply stepStar_trans (c₂ := ⟨4 * m + 4, 1, 0, 4 * m + 4, E + 4 * m + 4⟩)
    · have h := r2r3_chain (4 * m + 4) 0 0 0 E
      simp only [Nat.zero_add] at h
      refine stepStar_trans h ?_; ring_nf; finish
    have h := d_to_b (4 * m + 4) (4 * m + 4) 1 0 (E + 4 * m + 4)
    simp only [Nat.zero_add] at h
    refine stepStar_trans h ?_; ring_nf; finish
  apply stepStar_trans (c₂ := ⟨3 * m + 3, 1, 0, 0, E + 9 * m + 9⟩)
  · have h := r4r1r1_rounds (m + 1) (3 * m + 3) 1 (E + 8 * m + 8)
    rw [show 3 * m + 3 + (m + 1) = 4 * m + 4 from by ring,
        show 1 + 4 * (m + 1) = 4 * m + 5 from by ring] at h
    refine stepStar_trans h ?_; ring_nf; finish
  refine stepStar_trans (tail_b1 (3 * m + 2) (E + 9 * m + 9)) ?_
  ring_nf; finish

-- Main transition C=4m+5:
-- (0, 0, 4m+5, 0, E+1) ⊢⁺ (0, 0, 6m+7, 0, E+12m+15)
theorem main_mod1 (m E : ℕ) :
    ⟨0, 0, 4 * m + 5, 0, E + 1⟩ [fm]⊢⁺ ⟨(0 : ℕ), 0, 6 * m + 7, 0, E + 12 * m + 15⟩ := by
  apply step_stepStar_stepPlus (c₂ := ⟨0, 1, 4 * m + 5, 0, E⟩)
  · simp [fm]
  apply stepStar_trans (c₂ := ⟨4 * m + 5, 4 * m + 6, 0, 0, E + 8 * m + 10⟩)
  · apply stepStar_trans (c₂ := ⟨4 * m + 5, 1, 0, 4 * m + 5, E + 4 * m + 5⟩)
    · have h := r2r3_chain (4 * m + 5) 0 0 0 E
      simp only [Nat.zero_add] at h
      refine stepStar_trans h ?_; ring_nf; finish
    have h := d_to_b (4 * m + 5) (4 * m + 5) 1 0 (E + 4 * m + 5)
    simp only [Nat.zero_add] at h
    refine stepStar_trans h ?_; ring_nf; finish
  apply stepStar_trans (c₂ := ⟨3 * m + 4, 2, 0, 0, E + 9 * m + 11⟩)
  · have h := r4r1r1_rounds (m + 1) (3 * m + 4) 2 (E + 8 * m + 10)
    rw [show 3 * m + 4 + (m + 1) = 4 * m + 5 from by ring,
        show 2 + 4 * (m + 1) = 4 * m + 6 from by ring] at h
    refine stepStar_trans h ?_; ring_nf; finish
  refine stepStar_trans (tail_b2 (3 * m + 3) (E + 9 * m + 11)) ?_
  ring_nf; finish

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨0, 0, 2, 0, 1⟩) (by execute fm 1)
  apply progress_nonhalt (fm := fm)
    (P := fun q ↦ ∃ C E, q = ⟨0, 0, C + 2, 0, E + 1⟩)
  · intro q ⟨C, E, hq⟩
    subst hq
    rcases Nat.even_or_odd C with ⟨K, hK⟩ | ⟨K, hK⟩
    · rcases Nat.even_or_odd K with ⟨m, hm⟩ | ⟨m, hm⟩
      · -- C = 4m, C+2 = 4m+2
        refine ⟨⟨0, 0, 6 * m + 3, 0, E + 12 * m + 9⟩,
                ⟨6 * m + 1, E + 12 * m + 8, show (0, 0, 6 * m + 3, 0, E + 12 * m + 9) =
                  (0, 0, (6 * m + 1) + 2, 0, (E + 12 * m + 8) + 1) from by ring_nf⟩, ?_⟩
        have : C + 2 = 4 * m + 2 := by omega
        rw [this]; exact main_mod2 m E
      · -- C = 4m+2, C+2 = 4m+4
        refine ⟨⟨0, 0, 6 * m + 7, 0, E + 12 * m + 21⟩,
                ⟨6 * m + 5, E + 12 * m + 20, show (0, 0, 6 * m + 7, 0, E + 12 * m + 21) =
                  (0, 0, (6 * m + 5) + 2, 0, (E + 12 * m + 20) + 1) from by ring_nf⟩, ?_⟩
        have : C + 2 = 4 * m + 4 := by omega
        rw [this]; exact main_mod0 m E
    · rcases Nat.even_or_odd K with ⟨m, hm⟩ | ⟨m, hm⟩
      · -- C = 4m+1, C+2 = 4m+3
        refine ⟨⟨0, 0, 6 * m + 4, 0, E + 12 * m + 9⟩,
                ⟨6 * m + 2, E + 12 * m + 8, show (0, 0, 6 * m + 4, 0, E + 12 * m + 9) =
                  (0, 0, (6 * m + 2) + 2, 0, (E + 12 * m + 8) + 1) from by ring_nf⟩, ?_⟩
        have : C + 2 = 4 * m + 3 := by omega
        rw [this]; exact main_mod3 m E
      · -- C = 4m+3, C+2 = 4m+5
        refine ⟨⟨0, 0, 6 * m + 7, 0, E + 12 * m + 15⟩,
                ⟨6 * m + 5, E + 12 * m + 14, show (0, 0, 6 * m + 7, 0, E + 12 * m + 15) =
                  (0, 0, (6 * m + 5) + 2, 0, (E + 12 * m + 14) + 1) from by ring_nf⟩, ?_⟩
        have : C + 2 = 4 * m + 5 := by omega
        rw [this]; exact main_mod1 m E
  · exact ⟨0, 0, show (0, 0, 2, 0, 1) = (0, 0, 0 + 2, 0, 0 + 1) from by ring_nf⟩

end Sz22_2003_unofficial_176
