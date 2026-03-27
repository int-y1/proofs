import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #649: [35/6, 143/2, 56/55, 3/7, 5/13]

Vector representation:
```
-1 -1  1  1  0  0
-1  0  0  0  1  1
 3  0 -1  1 -1  0
 0  1  0 -1  0  0
 0  0  1  0  0 -1
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_649

def Q := ℕ × ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a+1, b+1, c, d, e, f⟩ => some ⟨a, b, c+1, d+1, e, f⟩
  | ⟨a+1, b, c, d, e, f⟩ => some ⟨a, b, c, d, e+1, f+1⟩
  | ⟨a, b, c+1, d, e+1, f⟩ => some ⟨a+3, b, c, d+1, e, f⟩
  | ⟨a, b, c, d+1, e, f⟩ => some ⟨a, b+1, c, d, e, f⟩
  | ⟨a, b, c, d, e, f+1⟩ => some ⟨a, b, c+1, d, e, f⟩
  | _ => none

-- R4 repeated: drain d to b
theorem d_to_b : ∀ k b, ⟨0, b, 0, D+k, E, F⟩ [fm]⊢* ⟨0, b+k, 0, D, E, F⟩ := by
  intro k; induction' k with k h <;> intro b
  · exists 0
  rw [← Nat.add_assoc]; step fm
  apply stepStar_trans (h _); ring_nf; finish

-- R1x3+R3 rounds
theorem r1r3_rounds :
    ∀ k C D, ⟨3, B+3*k, C, D, E+k, F⟩ [fm]⊢* ⟨3, B, C+2*k, D+4*k, E, F⟩ := by
  intro k; induction' k with k h <;> intro C D
  · exists 0
  rw [show B + 3 * (k + 1) = (B + 3 * k) + 3 from by ring,
      show E + (k + 1) = (E + k) + 1 from by ring]
  step fm; step fm; step fm; step fm
  apply stepStar_trans (h _ _); ring_nf; finish

-- R2x3+R3 drain: from a=3 b=0, drain c
theorem r2r3_drain_a3 :
    ∀ k D E F, ⟨3, 0, k, D, E, F⟩ [fm]⊢* ⟨0, 0, 0, D+k, E+2*k+3, F+3*k+3⟩ := by
  intro k; induction' k with k h <;> intro D E F
  · step fm; step fm; step fm; ring_nf; finish
  step fm; step fm; step fm; step fm
  apply stepStar_trans (h _ _ _); ring_nf; finish

-- Main transition for d ≡ 0 (mod 3): d = 3*(q+1)
theorem main_trans_mod0 (q g : ℕ) :
    ⟨0, 0, 0, 3*q+3, 3*q+3+g, 6*q+7⟩ [fm]⊢⁺
    ⟨0, 0, 0, 6*q+7, 6*q+g+8, 12*q+15⟩ := by
  -- d_to_b
  have h1 : ⟨0, 0, 0, 3*q+3, 3*q+3+g, 6*q+7⟩ [fm]⊢*
      ⟨0, 3*q+3, 0, 0, 3*q+3+g, 6*q+7⟩ := by
    have := d_to_b (D := 0) (E := 3*q+3+g) (F := 6*q+7) (3*q+3) 0
    convert this using 2; ring_nf
  -- R5 + R3
  have h2 : ⟨0, 3*q+3, 0, 0, 3*q+3+g, 6*q+7⟩ [fm]⊢⁺
      ⟨3, 3*q+3, 0, 1, 3*q+2+g, 6*q+6⟩ := by
    rw [show 6 * q + 7 = (6 * q + 6) + 1 from by ring]; step fm
    rw [show 3 * q + 3 + g = (3 * q + 2 + g) + 1 from by ring]; step fm; finish
  -- r1r3_rounds
  have h3 : ⟨3, 3*q+3, 0, 1, 3*q+2+g, 6*q+6⟩ [fm]⊢*
      ⟨3, 0, 2*q+2, 4*q+5, 2*q+g+1, 6*q+6⟩ := by
    have h := r1r3_rounds (B := 0) (E := 2*q+g+1) (F := 6*q+6) (q+1) 0 1
    convert h using 2; all_goals ring_nf
  -- r2r3_drain_a3
  have h4 := r2r3_drain_a3 (2*q+2) (4*q+5) (2*q+g+1) (6*q+6)
  exact stepStar_stepPlus_stepPlus h1 (stepPlus_stepStar_stepPlus h2
    (stepStar_trans h3 (stepStar_trans h4 (by ring_nf; finish))))

-- Main transition for d ≡ 1 (mod 3): d = 3*q+1
theorem main_trans_mod1 (q g : ℕ) :
    ⟨0, 0, 0, 3*q+1, 3*q+1+g, 6*q+3⟩ [fm]⊢⁺ ⟨0, 0, 0, 6*q+3, 6*q+g+4, 12*q+7⟩ := by
  -- d_to_b
  have h1 : ⟨0, 0, 0, 3*q+1, 3*q+1+g, 6*q+3⟩ [fm]⊢*
      ⟨0, 3*q+1, 0, 0, 3*q+1+g, 6*q+3⟩ := by
    have := d_to_b (D := 0) (E := 3*q+1+g) (F := 6*q+3) (3*q+1) 0
    convert this using 2; ring_nf
  -- R5 + R3
  have h2 : ⟨0, 3*q+1, 0, 0, 3*q+1+g, 6*q+3⟩ [fm]⊢⁺
      ⟨3, 3*q+1, 0, 1, 3*q+g, 6*q+2⟩ := by
    rw [show 6 * q + 3 = (6 * q + 2) + 1 from by ring]; step fm
    rw [show 3 * q + 1 + g = (3 * q + g) + 1 from by ring]; step fm; finish
  -- r1r3_rounds with k=q, B=1
  have h3 : ⟨3, 3*q+1, 0, 1, 3*q+g, 6*q+2⟩ [fm]⊢*
      ⟨3, 1, 2*q, 4*q+1, 2*q+g, 6*q+2⟩ := by
    have h := r1r3_rounds (B := 1) (E := 2*q+g) (F := 6*q+2) q 0 1
    convert h using 2; ring_nf
  -- R1 + R2x2 + R3 (4 steps)
  have h4 : ⟨3, 1, 2*q, 4*q+1, 2*q+g, 6*q+2⟩ [fm]⊢*
      ⟨3, 0, 2*q, 4*q+3, 2*q+g+1, 6*q+4⟩ := by
    step fm; step fm; step fm
    rw [show 2 * q + g + 2 = (2 * q + g + 1) + 1 from by ring]; step fm; finish
  -- r2r3_drain_a3
  have h5 := r2r3_drain_a3 (2*q) (4*q+3) (2*q+g+1) (6*q+4)
  exact stepStar_stepPlus_stepPlus h1 (stepPlus_stepStar_stepPlus h2
    (stepStar_trans h3 (stepStar_trans h4 (stepStar_trans h5 (by ring_nf; finish)))))

-- Main transition for d ≡ 2 (mod 3): d = 3*q+2
theorem main_trans_mod2 (q g : ℕ) :
    ⟨0, 0, 0, 3*q+2, 3*q+2+g, 6*q+5⟩ [fm]⊢⁺ ⟨0, 0, 0, 6*q+5, 6*q+g+6, 12*q+11⟩ := by
  -- d_to_b
  have h1 : ⟨0, 0, 0, 3*q+2, 3*q+2+g, 6*q+5⟩ [fm]⊢*
      ⟨0, 3*q+2, 0, 0, 3*q+2+g, 6*q+5⟩ := by
    have := d_to_b (D := 0) (E := 3*q+2+g) (F := 6*q+5) (3*q+2) 0
    convert this using 2; ring_nf
  -- R5 + R3
  have h2 : ⟨0, 3*q+2, 0, 0, 3*q+2+g, 6*q+5⟩ [fm]⊢⁺
      ⟨3, 3*q+2, 0, 1, 3*q+g+1, 6*q+4⟩ := by
    rw [show 6 * q + 5 = (6 * q + 4) + 1 from by ring]; step fm
    rw [show 3 * q + 2 + g = (3 * q + g + 1) + 1 from by ring]; step fm; finish
  -- r1r3_rounds with k=q, B=2
  have h3 : ⟨3, 3*q+2, 0, 1, 3*q+g+1, 6*q+4⟩ [fm]⊢*
      ⟨3, 2, 2*q, 4*q+1, 2*q+g+1, 6*q+4⟩ := by
    have h := r1r3_rounds (B := 2) (E := 2*q+g+1) (F := 6*q+4) q 0 1
    convert h using 2; ring_nf
  -- R1x2 + R2 + R3 (4 steps)
  have h4 : ⟨3, 2, 2*q, 4*q+1, 2*q+g+1, 6*q+4⟩ [fm]⊢*
      ⟨3, 0, 2*q+1, 4*q+4, 2*q+g+1, 6*q+5⟩ := by
    rw [show 2 * q + g + 1 = (2 * q + g) + 1 from by ring]; step fm; step fm
    step fm
    rw [show 2 * q + g + 1 = (2 * q + g) + 1 from by ring]; step fm; finish
  -- r2r3_drain_a3
  have h5 := r2r3_drain_a3 (2*q+1) (4*q+4) (2*q+g+1) (6*q+5)
  exact stepStar_stepPlus_stepPlus h1 (stepPlus_stepStar_stepPlus h2
    (stepStar_trans h3 (stepStar_trans h4 (stepStar_trans h5 (by ring_nf; finish)))))

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨0, 0, 0, 1, 3, 3⟩) (by execute fm 6)
  apply progress_nonhalt (fm := fm)
    (P := fun q ↦ ∃ d g, q = ⟨0, 0, 0, d, d+g, 2*d+1⟩ ∧ d ≥ 1)
  · intro c ⟨d, g, hq, hd⟩; subst hq
    rcases (show d % 3 = 0 ∨ d % 3 = 1 ∨ d % 3 = 2 from by omega) with hm | hm | hm
    · obtain ⟨q, rfl⟩ : ∃ q, d = 3 * q := ⟨d / 3, by omega⟩
      obtain ⟨q', rfl⟩ : ∃ q', q = q' + 1 := ⟨q - 1, by omega⟩
      refine ⟨⟨0, 0, 0, 6*q'+7, 6*q'+g+8, 12*q'+15⟩,
             ⟨6*q'+7, g+1, by ring_nf, by omega⟩, ?_⟩
      have := main_trans_mod0 q' g
      convert this using 2; ring_nf
    · obtain ⟨q, rfl⟩ : ∃ q, d = 3 * q + 1 := ⟨d / 3, by omega⟩
      refine ⟨⟨0, 0, 0, 6*q+3, 6*q+g+4, 12*q+7⟩,
             ⟨6*q+3, g+1, by ring_nf, by omega⟩, ?_⟩
      have := main_trans_mod1 q g
      convert this using 2; ring_nf
    · obtain ⟨q, rfl⟩ : ∃ q, d = 3 * q + 2 := ⟨d / 3, by omega⟩
      refine ⟨⟨0, 0, 0, 6*q+5, 6*q+g+6, 12*q+11⟩,
             ⟨6*q+5, g+1, by ring_nf, by omega⟩, ?_⟩
      have := main_trans_mod2 q g
      convert this using 2; ring_nf
  · exact ⟨1, 2, rfl, by omega⟩
