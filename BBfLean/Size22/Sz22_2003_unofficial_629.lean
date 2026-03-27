import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #629: [35/6, 143/2, 4/55, 3/7, 154/13]

Vector representation:
```
-1 -1  1  1  0  0
-1  0  0  0  1  1
 2  0 -1  0 -1  0
 0  1  0 -1  0  0
 1  0  0  1  1 -1
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_629

def Q := ℕ × ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a+1, b+1, c, d, e, f⟩ => some ⟨a, b, c+1, d+1, e, f⟩
  | ⟨a+1, b, c, d, e, f⟩ => some ⟨a, b, c, d, e+1, f+1⟩
  | ⟨a, b, c+1, d, e+1, f⟩ => some ⟨a+2, b, c, d, e, f⟩
  | ⟨a, b, c, d+1, e, f⟩ => some ⟨a, b+1, c, d, e, f⟩
  | ⟨a, b, c, d, e, f+1⟩ => some ⟨a+1, b, c, d+1, e+1, f⟩
  | _ => none

-- R4 chain: transfer d to b (when a=0, c=0)
theorem d_to_b : ∀ k b, ⟨0, b, 0, d+k, e, f⟩ [fm]⊢* ⟨0, b+k, 0, d, e, f⟩ := by
  intro k; induction' k with k h <;> intro b
  · exists 0
  rw [← Nat.add_assoc]; step fm
  apply stepStar_trans (h _); ring_nf; finish

-- R3,R2,R2 chain: convert c to e,f (when a=0, b=0, e>=1)
theorem r322_chain : ∀ k c e f, ⟨0, 0, c+k, D, e+1, f⟩ [fm]⊢* ⟨0, 0, c, D, e+1+k, f+2*k⟩ := by
  intro k; induction' k with k h <;> intro c e f
  · exists 0
  rw [show c + (k + 1) = (c + k) + 1 from by ring]
  step fm; step fm; step fm
  apply stepStar_trans (h _ _ _); ring_nf; finish

-- R1,R1,R3 chain: interleaved when a=2
theorem r113_chain : ∀ k c D e, ⟨2, b+2*k, c, D, e+k, F⟩ [fm]⊢* ⟨2, b, c+k, D+2*k, e, F⟩ := by
  intro k; induction' k with k h <;> intro c D e
  · exists 0
  rw [show b + 2 * (k + 1) = (b + 2 * k) + 1 + 1 from by ring,
      show e + (k + 1) = (e + k) + 1 from by ring]
  step fm; step fm; step fm
  apply stepStar_trans (h _ _ _); ring_nf; finish

-- Even transition: (0,0,0,2m+2,4m+5,f+1) →⁺ (0,0,0,2m+3,4m+7,f+2m+3)
theorem even_trans (m : ℕ) :
    ⟨0, 0, 0, 2*m+2, 4*m+5, f+1⟩ [fm]⊢⁺ ⟨0, 0, 0, 2*m+3, 4*m+7, f+2*m+3⟩ := by
  -- R4 chain
  rw [show 2*m+2 = 0+(2*m+2) from by ring]
  apply stepStar_stepPlus_stepPlus (d_to_b (d := 0) (e := 4*m+5) (f := f+1) (2*m+2) 0)
  simp only [Nat.zero_add]
  -- R5, R1, R3
  step fm
  rw [show (1 : ℕ) = 0 + 1 from by ring, show 2*m+2 = (2*m+1) + 1 from by ring]
  step fm
  rw [show 4*m + 6 = (4*m + 5) + 1 from by ring]
  step fm
  -- R113 chain (m rounds)
  rw [show 2*m+1 = 1+2*m from by ring, show 4*m+5 = (3*m+5)+m from by ring]
  apply stepStar_trans (r113_chain (b := 1) (F := f) m 0 2 (3*m+5))
  -- Clean up 0+m artifacts
  simp only [Nat.zero_add]
  -- R1, R2
  rw [show (2 : ℕ) = 0+1+1 from by ring, show (1 : ℕ) = 0+1 from by ring,
      show 2+2*m = 2*m+2 from by ring]
  step fm; step fm
  -- R322 chain (m+1 rounds)
  rw [show m+1 = 0+(m+1) from by ring, show 3*m+5+1 = (3*m+5)+1 from by ring]
  apply stepStar_trans (r322_chain (D := 2*m+2+1) (m+1) 0 (3*m+5) (f+1))
  ring_nf; finish

-- Odd transition: (0,0,0,2m+3,4m+7,f+1) →⁺ (0,0,0,2m+4,4m+9,f+2m+4)
theorem odd_trans (m : ℕ) :
    ⟨0, 0, 0, 2*m+3, 4*m+7, f+1⟩ [fm]⊢⁺ ⟨0, 0, 0, 2*m+4, 4*m+9, f+2*m+4⟩ := by
  -- R4 chain
  rw [show 2*m+3 = 0+(2*m+3) from by ring]
  apply stepStar_stepPlus_stepPlus (d_to_b (d := 0) (e := 4*m+7) (f := f+1) (2*m+3) 0)
  simp only [Nat.zero_add]
  -- R5, R1, R3
  step fm
  rw [show (1 : ℕ) = 0 + 1 from by ring, show 2*m+3 = (2*m+2) + 1 from by ring]
  step fm
  rw [show 4*m + 8 = (4*m + 7) + 1 from by ring]
  step fm
  -- R113 chain (m+1 rounds)
  rw [show 2*m+2 = 0+2*(m+1) from by ring, show 4*m+7 = (3*m+6)+(m+1) from by ring]
  apply stepStar_trans (r113_chain (b := 0) (F := f) (m+1) 0 2 (3*m+6))
  simp only [Nat.zero_add]
  -- R2, R2
  rw [show 2+2*(m+1) = 2*m+4 from by ring]
  step fm; step fm
  -- R322 chain (m+1 rounds)
  rw [show m+1 = 0+(m+1) from by ring, show 3*m+6+1+1 = (3*m+7)+1 from by ring]
  apply stepStar_trans (r322_chain (D := 2*m+4) (m+1) 0 (3*m+7) (f+2))
  ring_nf; finish

-- d=0 transition
theorem d0_trans : ⟨0, 0, 0, 0, 1, f+1⟩ [fm]⊢⁺ ⟨0, 0, 0, 1, 3, f+1⟩ := by
  step fm; step fm; finish

-- d=1 transition
theorem d1_trans : ⟨0, 0, 0, 1, 3, f+1⟩ [fm]⊢⁺ ⟨0, 0, 0, 2, 5, f+2⟩ := by
  execute fm 6

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨0, 0, 0, 0, 1, 1⟩)
  · execute fm 1
  apply progress_nonhalt (fm := fm)
    (P := fun q ↦ ∃ d f, q = ⟨0, 0, 0, d, 2*d+1, f+1⟩)
  · intro c ⟨d, f, hq⟩; subst hq
    rcases d with _ | _ | d
    · -- d=0
      exact ⟨_, ⟨1, f, rfl⟩, d0_trans⟩
    · -- d=1
      exact ⟨_, ⟨2, f+1, by ring_nf⟩, d1_trans⟩
    · -- d+2
      rcases Nat.even_or_odd d with ⟨m, hm⟩ | ⟨m, hm⟩
      · -- d even: d=m+m, so d+2=m+m+2
        subst hm
        have key := @even_trans (f := f) m
        refine ⟨⟨0, 0, 0, 2*m+3, 4*m+7, f+2*m+3⟩, ⟨2*m+3, f+2*m+2, by ring_nf⟩, ?_⟩
        rw [show m+m+1+1 = 2*m+2 from by ring,
            show 2*(2*m+2)+1 = 4*m+5 from by ring]
        exact key
      · -- d odd: d=2m+1, so d+2=2m+3
        subst hm
        have key := @odd_trans (f := f) m
        refine ⟨⟨0, 0, 0, 2*m+4, 4*m+9, f+2*m+4⟩, ⟨2*m+4, f+2*m+3, by ring_nf⟩, ?_⟩
        -- Goal: (0,0,0,2*m+3,2*(2*m+3)+1,f+1) ⊢⁺ (0,0,0,2*m+4,4*m+9,f+2*m+4)
        rw [show 2*(2*m+3)+1 = 4*m+7 from by ring]
        exact key
  · exact ⟨0, 0, rfl⟩

end Sz22_2003_unofficial_629
