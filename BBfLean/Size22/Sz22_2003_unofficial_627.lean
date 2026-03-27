import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #627: [35/6, 143/2, 4/55, 3/7, 14/13]

Vector representation:
```
-1 -1  1  1  0  0
-1  0  0  0  1  1
 2  0 -1  0 -1  0
 0  1  0 -1  0  0
 1  0  0  1  0 -1
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_627

def Q := ℕ × ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a+1, b+1, c, d, e, f⟩ => some ⟨a, b, c+1, d+1, e, f⟩
  | ⟨a+1, b, c, d, e, f⟩ => some ⟨a, b, c, d, e+1, f+1⟩
  | ⟨a, b, c+1, d, e+1, f⟩ => some ⟨a+2, b, c, d, e, f⟩
  | ⟨a, b, c, d+1, e, f⟩ => some ⟨a, b+1, c, d, e, f⟩
  | ⟨a, b, c, d, e, f+1⟩ => some ⟨a+1, b, c, d+1, e, f⟩
  | _ => none

-- R4 chain: convert d to b
theorem d_to_b : ∀ k, ∀ b d e f, ⟨0, b, 0, d+k, e, f⟩ [fm]⊢* ⟨0, b+k, 0, d, e, f⟩ := by
  intro k; induction' k with k h <;> intro b d e f
  · exists 0
  rw [show d + (k + 1) = (d + k) + 1 from by ring]
  step fm
  apply stepStar_trans (h _ _ _ _)
  ring_nf; finish

-- R1,R1,R3 chain
theorem r1r1r3_chain : ∀ k, ∀ B C D E F,
    ⟨2, B+2*k, C, D, E+k, F⟩ [fm]⊢* ⟨2, B, C+k, D+2*k, E, F⟩ := by
  intro k; induction' k with k h <;> intro B C D E F
  · exists 0
  rw [show B + 2 * (k + 1) = (B + 2 * k) + 2 from by ring,
      show E + (k + 1) = (E + k) + 1 from by ring]
  step fm; step fm; step fm
  apply stepStar_trans (h _ _ _ _ _)
  ring_nf; finish

-- R2,R2,R3 drain chain
theorem r2r2r3_chain : ∀ k, ∀ C D E F,
    ⟨2, 0, C+k, D, E, F⟩ [fm]⊢* ⟨2, 0, C, D, E+k, F+2*k⟩ := by
  intro k; induction' k with k h <;> intro C D E F
  · exists 0
  rw [show C + (k + 1) = (C + k) + 1 from by ring]
  step fm; step fm; step fm
  apply stepStar_trans (h _ _ _ _)
  ring_nf; finish

-- Combined inner phase for odd case:
-- (2, 2*m, 0, 2, 2*m+1, F) ⊢* (0, 0, 0, 2*m+2, 2*m+3, F+2*m+2)
theorem odd_inner (m F : ℕ) :
    (⟨2, 2*m, 0, 2, 2*m+1, F⟩ : Q) [fm]⊢* ⟨0, 0, 0, 2*m+2, 2*m+3, F+2*m+2⟩ := by
  have h1 := r1r1r3_chain m 0 0 2 (m+1) F
  rw [show 0+2*m = 2*m from by omega, show (m+1)+m = 2*m+1 from by omega] at h1
  apply stepStar_trans h1
  rw [show (2+2*m : ℕ) = 2*m+2 from by ring]
  apply stepStar_trans (r2r2r3_chain m 0 (2*m+2) (m+1) F)
  rw [show (m+1+m : ℕ) = 2*m+1 from by omega]
  step fm; step fm
  ring_nf; finish

-- Combined inner phase for even case:
-- (2, 2*m+1, 0, 2, 2*m+2, F) ⊢* (0, 0, 0, 2*m+3, 2*m+4, F+2*m+3)
theorem even_inner (m F : ℕ) :
    (⟨2, 2*m+1, 0, 2, 2*m+2, F⟩ : Q) [fm]⊢* ⟨0, 0, 0, 2*m+3, 2*m+4, F+2*m+3⟩ := by
  have h1 := r1r1r3_chain m 1 0 2 (m+2) F
  rw [show 1+2*m = 2*m+1 from by omega, show (m+2)+m = 2*m+2 from by omega] at h1
  apply stepStar_trans h1
  rw [show (2+2*m : ℕ) = 2*m+2 from by ring]
  step fm; step fm; step fm
  rw [show (2*m+2+1 : ℕ) = 2*m+3 from by omega]
  apply stepStar_trans (r2r2r3_chain m 0 (2*m+3) (m+2) (F+1))
  rw [show (m+2+m : ℕ) = 2*m+2 from by omega,
      show (F+1+2*m : ℕ) = F+2*m+1 from by ring]
  step fm; step fm
  ring_nf; finish

-- Odd case: (0,0,0,2m+1,2m+2,F+1) ⊢⁺ (0,0,0,2m+2,2m+3,F+2m+2)
theorem odd_trans (m F : ℕ) : (⟨0, 0, 0, 2*m+1, 2*m+2, F+1⟩ : Q) [fm]⊢⁺ ⟨0, 0, 0, 2*m+2, 2*m+3, F+2*m+2⟩ := by
  rw [show (2*m+1 : ℕ) = 0 + (2*m+1) from by ring]
  apply stepStar_stepPlus_stepPlus (d_to_b (2*m+1) 0 0 (2*m+2) (F+1))
  simp only [Nat.zero_add]
  -- (0, 2m+1, 0, 0, 2m+2, F+1)
  step fm; step fm; step fm -- R5, R1, R3
  -- Goal: (2, 2*m, 0, 2, 2*m+1, F) ⊢* (0, 0, 0, 2*m+2, 2*m+3, F+2*m+2)
  exact odd_inner m F

-- Even case: (0,0,0,2m+2,2m+3,F+1) ⊢⁺ (0,0,0,2m+3,2m+4,F+2m+3)
theorem even_trans (m F : ℕ) : (⟨0, 0, 0, 2*m+2, 2*m+3, F+1⟩ : Q) [fm]⊢⁺ ⟨0, 0, 0, 2*m+3, 2*m+4, F+2*m+3⟩ := by
  rw [show (2*m+2 : ℕ) = 0 + (2*m+2) from by ring]
  apply stepStar_stepPlus_stepPlus (d_to_b (2*m+2) 0 0 (2*m+3) (F+1))
  simp only [Nat.zero_add]
  step fm; step fm; step fm
  exact even_inner m F

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨0, 0, 0, 1, 2, 1⟩) (by execute fm 3)
  apply progress_nonhalt (fm := fm)
    (P := fun q ↦ ∃ d f, q = ⟨0, 0, 0, d+1, d+2, f+1⟩)
  · intro c ⟨d, f, hq⟩; subst hq
    rcases Nat.even_or_odd d with ⟨m, hm⟩ | ⟨m, hm⟩
    · -- d even: d = m+m
      subst hm
      rcases m with _ | m
      · -- d=0: use odd_trans 0
        exact ⟨_, ⟨1, f+1, rfl⟩, odd_trans 0 f⟩
      · -- d=2(m+1): d+1 = 2m+3 is odd, use odd_trans (m+1)
        refine ⟨⟨0, 0, 0, 2*(m+1)+2, 2*(m+1)+3, f+2*(m+1)+2⟩,
                ⟨2*(m+1)+1, f+2*(m+1)+1, by ring_nf⟩, ?_⟩
        rw [show (m+1)+(m+1)+1 = 2*(m+1)+1 from by ring,
            show (m+1)+(m+1)+2 = 2*(m+1)+2 from by ring]
        exact odd_trans (m+1) f
    · -- d odd: d = 2m+1, d+1 = 2m+2 is even, use even_trans m
      subst hm
      refine ⟨⟨0, 0, 0, 2*m+3, 2*m+4, f+2*m+3⟩,
              ⟨2*m+2, f+2*m+2, by ring_nf⟩, ?_⟩
      rw [show 2*m+1+1 = 2*m+2 from by ring,
          show 2*m+1+2 = 2*m+3 from by ring]
      exact even_trans m f
  · exact ⟨0, 0, rfl⟩

end Sz22_2003_unofficial_627
