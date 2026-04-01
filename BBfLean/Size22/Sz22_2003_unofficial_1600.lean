import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #1600: [77/15, 14/3, 27/22, 5/7, 9/2]

Vector representation:
```
 0 -1 -1  1  1
 1 -1  0  1  0
-1  3  0  0 -1
 0  0  1 -1  0
-1  2  0  0  0
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_1600

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a, b+1, c+1, d, e⟩ => some ⟨a, b, c, d+1, e+1⟩
  | ⟨a, b+1, c, d, e⟩ => some ⟨a+1, b, c, d+1, e⟩
  | ⟨a+1, b, c, d, e+1⟩ => some ⟨a, b+3, c, d, e⟩
  | ⟨a, b, c, d+1, e⟩ => some ⟨a, b, c+1, d, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b+2, c, d, e⟩
  | _ => none

-- R4 chain: transfer d to c
theorem d_to_c : ∀ k c, ⟨a, 0, c, k, 0⟩ [fm]⊢* ⟨a, 0, c + k, 0, 0⟩ := by
  intro k; induction' k with k ih <;> intro c
  · exists 0
  · step fm; apply stepStar_trans (ih (c + 1)); ring_nf; finish

-- R1 chain: drain b and c together
theorem r1_chain : ∀ k c d e, ⟨a, k, c + k, d, e⟩ [fm]⊢* ⟨a, 0, c, d + k, e + k⟩ := by
  intro k; induction' k with k ih <;> intro c d e
  · exists 0
  · rw [show c + (k + 1) = (c + k) + 1 from by ring]
    step fm; apply stepStar_trans (ih c (d + 1) (e + 1)); ring_nf; finish

-- k rounds of (R3, R1x3): each round a-=1, c-=3, d+=3, e+=2
theorem r3_r1x3_chain : ∀ k, ∀ A C D E,
    ⟨A + k + 1, 0, C + 3 * k, D, E + 1⟩ [fm]⊢* ⟨A + 1, 0, C, D + 3 * k, E + 2 * k + 1⟩ := by
  intro k; induction' k with k ih <;> intro A C D E
  · simp; exists 0
  · rw [show A + (k + 1) + 1 = (A + k + 1) + 1 from by ring,
        show C + 3 * (k + 1) = (C + 3 * k) + 3 from by ring,
        show (C + 3 * k + 3 : ℕ) = (C + 3 * k + 2) + 1 from by ring]
    step fm
    rw [show (C + 3 * k + 2 + 1 : ℕ) = (C + 3 * k + 1) + 1 + 1 from by ring]
    step fm
    rw [show (C + 3 * k + 1 + 1 : ℕ) = (C + 3 * k) + 1 + 1 from by ring]
    step fm
    rw [show (C + 3 * k + 1 : ℕ) = C + 3 * k + 1 from rfl]
    step fm
    -- Goal state: (A + k + 1, 0, C + 3 * k, D + 3, E + 2 + 1) ⊢* target
    -- Need to rewrite to match ih signature
    rw [show E + 2 + 1 = (E + 2) + 1 from by ring,
        show D + 3 * (k + 1) = (D + 3) + 3 * k from by ring,
        show E + 2 * (k + 1) + 1 = (E + 2) + 2 * k + 1 from by ring]
    exact ih A C (D + 3) (E + 2)

-- (R3, R2x3) chain: each round a+=2, d+=3, e-=1
theorem r3_r2x3_chain : ∀ k, ∀ A D,
    ⟨A + 1, 0, 0, D, k + 1⟩ [fm]⊢* ⟨A + 2 * k + 3, 0, 0, D + 3 * k + 3, 0⟩ := by
  intro k; induction' k with k ih <;> intro A D
  · step fm; step fm; step fm; step fm; ring_nf; finish
  · rw [show (k + 1 + 1 : ℕ) = (k + 1) + 1 from by ring]
    step fm; step fm; step fm; step fm
    rw [show A + 1 + 1 + 1 = (A + 2) + 1 from by ring,
        show D + 1 + 1 + 1 = D + 3 from by ring,
        show A + 2 * (k + 1) + 3 = (A + 2) + 2 * k + 3 from by ring,
        show D + 3 * (k + 1) + 3 = (D + 3) + 3 * k + 3 from by ring]
    exact ih (A + 2) (D + 3)

-- Main transition: (3m+2, 0, 0, 6m+2, 0) ⊢⁺ (9m+5, 0, 0, 18m+8, 0)
theorem main_trans (m : ℕ) :
    ⟨3 * m + 2, 0, 0, 6 * m + 2, 0⟩ [fm]⊢⁺ ⟨9 * m + 5, 0, 0, 18 * m + 8, 0⟩ := by
  -- Phase 1: R4: d->c
  have p1 : ⟨3 * m + 2, 0, 0, 6 * m + 2, 0⟩ [fm]⊢* ⟨3 * m + 2, 0, 6 * m + 2, 0, 0⟩ := by
    have := d_to_c (a := 3 * m + 2) (6 * m + 2) 0; simpa using this
  -- Phase 2: R5
  have p2 : ⟨3 * m + 2, 0, 6 * m + 2, 0, 0⟩ [fm]⊢* ⟨3 * m + 1, 2, 6 * m + 2, 0, 0⟩ := by
    rw [show 3 * m + 2 = (3 * m + 1) + 1 from by ring]; step fm; finish
  -- Phase 3: R1 x 2
  have p3 : ⟨3 * m + 1, 2, 6 * m + 2, 0, 0⟩ [fm]⊢* ⟨3 * m + 1, 0, 6 * m, 2, 2⟩ := by
    exact r1_chain (a := 3 * m + 1) 2 (6 * m) 0 0
  -- Phase 4: (R3, R1x3) x 2m: (3m+1, 0, 6m, 2, 2) -> (m+1, 0, 0, 6m+2, 4m+2)
  -- Use r3_r1x3_chain with k=2m, A=m, C=0, D=2, E=1
  -- source: (m+2m+1, 0, 0+6m, 2, 1+1) = (3m+1, 0, 6m, 2, 2)
  -- target: (m+1, 0, 0, 2+6m, 1+4m+1) = (m+1, 0, 0, 6m+2, 4m+2)
  have p4 : ⟨3 * m + 1, 0, 6 * m, 2, 2⟩ [fm]⊢* ⟨m + 1, 0, 0, 6 * m + 2, 4 * m + 2⟩ := by
    have h := r3_r1x3_chain (2 * m) m 0 2 1
    rw [show m + 2 * m + 1 = 3 * m + 1 from by ring,
        show 0 + 3 * (2 * m) = 6 * m from by ring,
        show 2 + 3 * (2 * m) = 6 * m + 2 from by ring,
        show 1 + 2 * (2 * m) + 1 = 4 * m + 2 from by ring,
        show (1 + 1 : ℕ) = 2 from rfl] at h
    exact h
  -- Phase 5: (R3, R2x3): (m+1, 0, 0, 6m+2, 4m+2) -> (9m+5, 0, 0, 18m+8, 0)
  have p5 : ⟨m + 1, 0, 0, 6 * m + 2, 4 * m + 2⟩ [fm]⊢* ⟨9 * m + 5, 0, 0, 18 * m + 8, 0⟩ := by
    rw [show (4 * m + 2 : ℕ) = (4 * m + 1) + 1 from by ring]
    have := r3_r2x3_chain (4 * m + 1) m (6 * m + 2)
    rw [show m + 2 * (4 * m + 1) + 3 = 9 * m + 5 from by ring,
        show 6 * m + 2 + 3 * (4 * m + 1) + 3 = 18 * m + 8 from by ring] at this
    exact this
  -- p2 includes R5 which is a real step, so compose as:
  -- p1 (⊢*) then p2 starts with a step
  have p12 : ⟨3 * m + 2, 0, 0, 6 * m + 2, 0⟩ [fm]⊢* ⟨3 * m + 1, 2, 6 * m + 2, 0, 0⟩ :=
    stepStar_trans p1 p2
  have p123 : ⟨3 * m + 2, 0, 0, 6 * m + 2, 0⟩ [fm]⊢* ⟨3 * m + 1, 0, 6 * m, 2, 2⟩ :=
    stepStar_trans p12 p3
  have p1234 : ⟨3 * m + 2, 0, 0, 6 * m + 2, 0⟩ [fm]⊢* ⟨m + 1, 0, 0, 6 * m + 2, 4 * m + 2⟩ :=
    stepStar_trans p123 p4
  have p_all : ⟨3 * m + 2, 0, 0, 6 * m + 2, 0⟩ [fm]⊢* ⟨9 * m + 5, 0, 0, 18 * m + 8, 0⟩ :=
    stepStar_trans p1234 p5
  exact stepStar_stepPlus p_all (by simp [Q]; omega)

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨2, 0, 0, 2, 0⟩)
  · execute fm 3
  apply progress_nonhalt_simple (fm := fm) (A := ℕ)
    (fun m ↦ ⟨3 * m + 2, 0, 0, 6 * m + 2, 0⟩) 0
  intro m
  refine ⟨3 * m + 1, ?_⟩
  rw [show 3 * (3 * m + 1) + 2 = 9 * m + 5 from by ring,
      show 6 * (3 * m + 1) + 2 = 18 * m + 8 from by ring]
  exact main_trans m

end Sz22_2003_unofficial_1600
