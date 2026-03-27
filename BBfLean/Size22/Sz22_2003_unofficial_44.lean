import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #44: [1/15, 54/77, 7/3, 5/49, 363/2]

Vector representation:
```
 0 -1 -1  0  0
 1  3  0 -1 -1
 0 -1  0  1  0
 0  0  1 -2  0
-1  1  0  0  2
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_44

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a, b+1, c+1, d, e⟩ => some ⟨a, b, c, d, e⟩
  | ⟨a, b, c, d+1, e+1⟩ => some ⟨a+1, b+3, c, d, e⟩
  | ⟨a, b+1, c, d, e⟩ => some ⟨a, b, c, d+1, e⟩
  | ⟨a, b, c, d+2, e⟩ => some ⟨a, b, c+1, d, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b+1, c, d, e+2⟩
  | _ => none

-- Phase 1: Pump chain via alternating R3/R2 rounds.
theorem pump_chain : ∀ k, ∀ a b e,
    ⟨a, b + 1, 0, 0, k + e⟩ [fm]⊢* ⟨a + k, b + 2 * k + 1, 0, 0, e⟩ := by
  intro k; induction' k with k ih <;> intro a b e
  · ring_nf; exists 0
  rw [show (k + 1) + e = k + (e + 1) from by ring]
  step fm
  rw [show k + (e + 1) = (k + e) + 1 from by ring]
  step fm
  apply stepStar_trans (ih (a + 1) (b + 2) e)
  ring_nf; finish

-- Phase 2: Transfer b to d via R3 (c=0, e=0).
theorem b_to_d : ∀ k, ∀ a d,
    ⟨a, k, 0, d, 0⟩ [fm]⊢* ⟨a, 0, 0, d + k, 0⟩ := by
  intro k; induction' k with k ih <;> intro a d
  · exists 0
  step fm
  apply stepStar_trans (ih a (d + 1))
  ring_nf; finish

-- Phase 3: Transfer d to c via R4. d = 2k+1 → c += k, d → 1.
theorem d_to_c : ∀ k, ∀ a c,
    ⟨a, 0, c, 2 * k + 1, 0⟩ [fm]⊢* ⟨a, 0, c + k, 1, 0⟩ := by
  intro k; induction' k with k ih <;> intro a c
  · exists 0
  rw [show 2 * (k + 1) + 1 = (2 * k + 1) + 2 from by ring]
  step fm
  apply stepStar_trans (ih a (c + 1))
  ring_nf; finish

-- Phase 4b: Tail drain via (R5, R1) pairs.
theorem tail_drain : ∀ k, ∀ A E,
    ⟨A + k, 0, k, 0, E⟩ [fm]⊢* ⟨A, 0, 0, 0, E + 2 * k⟩ := by
  intro k; induction' k with k ih <;> intro A E
  · exists 0
  rw [show A + (k + 1) = (A + k) + 1 from by ring]
  step fm
  rw [show k + 1 = k + 1 from rfl]
  step fm
  apply stepStar_trans (ih A (E + 2))
  ring_nf; finish

-- Phase 4a: 6 fixed steps from (A, 0, C+5, 1, 0) → (A, 0, C+1, 0, 1).
-- Using C+5 ensures c >= 5 which is needed for the 3 R1 steps after R2.
theorem phase4a (A C : ℕ) :
    ⟨A + 1, 0, C + 5, 1, 0⟩ [fm]⊢* ⟨A + 1, 0, C + 1, 0, 1⟩ := by
  -- R5: (A+1, 0, C+5, 1, 0) → (A, 1, C+5, 1, 2)
  step fm
  -- R1: (A, 1, C+5, 1, 2) → (A, 0, C+4, 1, 2). b=1, c=C+5=(C+4)+1.
  rw [show C + 5 = (C + 4) + 1 from by ring]
  step fm
  -- R2: (A, 0, C+4, 1, 2) → (A+1, 3, C+4, 0, 1). d=1=(0+1), e=2=(1+1).
  step fm
  -- R1: (A+1, 3, C+4, 0, 1) → (A+1, 2, C+3, 0, 1). b=3=(2+1), c=C+4=(C+3)+1.
  rw [show C + 4 = (C + 3) + 1 from by ring]
  step fm
  -- R1: (A+1, 2, C+3, 0, 1) → (A+1, 1, C+2, 0, 1). b=2=(1+1), c=C+3=(C+2)+1.
  rw [show C + 3 = (C + 2) + 1 from by ring]
  step fm
  -- R1: (A+1, 1, C+2, 0, 1) → (A+1, 0, C+1, 0, 1). b=1=(0+1), c=C+2=(C+1)+1.
  rw [show C + 2 = (C + 1) + 1 from by ring]
  step fm
  finish

-- Main transition: (a+1, 0, 0, 0, f+3) →⁺ (a+4, 0, 0, 0, 2*f+3)
theorem main_trans (a f : ℕ) :
    ⟨a + 1, 0, 0, 0, f + 3⟩ [fm]⊢⁺ ⟨a + 4, 0, 0, 0, 2 * f + 3⟩ := by
  -- R5: (a+1, 0, 0, 0, f+3) → (a, 1, 0, 0, f+5)
  apply step_stepStar_stepPlus (c₂ := ⟨a, 0 + 1, 0, 0, f + 5⟩)
  · show fm ⟨a + 1, 0, 0, 0, f + 3⟩ = some ⟨a, 0 + 1, 0, 0, f + 5⟩; simp [fm]
  -- pump_chain k=f+5: (a, 1, 0, 0, f+5) → (a+f+5, 2f+11, 0, 0, 0)
  apply stepStar_trans (c₂ := ⟨a + (f + 5), 2 * (f + 5) + 1, 0, 0, 0⟩)
  · have h := pump_chain (f + 5) a 0 0
    rw [show (f + 5) + 0 = f + 5 from by ring,
        show 0 + 2 * (f + 5) + 1 = 2 * (f + 5) + 1 from by ring] at h
    exact h
  -- b_to_d: (a+f+5, 2f+11, 0, 0, 0) → (a+f+5, 0, 0, 2f+11, 0)
  apply stepStar_trans (c₂ := ⟨a + (f + 5), 0, 0, 2 * (f + 5) + 1, 0⟩)
  · have h := b_to_d (2 * (f + 5) + 1) (a + (f + 5)) 0
    rw [show 0 + (2 * (f + 5) + 1) = 2 * (f + 5) + 1 from by ring] at h
    exact h
  -- d_to_c k=f+5: → (a+f+5, 0, f+5, 1, 0)
  apply stepStar_trans (c₂ := ⟨a + (f + 5), 0, f + 5, 1, 0⟩)
  · have h := d_to_c (f + 5) (a + (f + 5)) 0
    rw [show 0 + (f + 5) = f + 5 from by ring] at h
    exact h
  -- Phase 4a: (a+f+5, 0, f+5, 1, 0) → (a+f+5, 0, f+1, 0, 1)
  -- f+5 = f + 5 = (f) + 5. Use phase4a with A = a+f+4, C = f.
  apply stepStar_trans (c₂ := ⟨a + (f + 5), 0, f + 1, 0, 1⟩)
  · have h := phase4a (a + (f + 4)) f
    rw [show a + (f + 4) + 1 = a + (f + 5) from by ring] at h
    exact h
  -- Phase 4b: tail_drain k=f+1: (a+f+5, 0, f+1, 0, 1) → (a+4, 0, 0, 0, 2f+3)
  have h := tail_drain (f + 1) (a + 4) 1
  rw [show a + 4 + (f + 1) = a + (f + 5) from by ring,
      show 1 + 2 * (f + 1) = 2 * f + 3 from by ring] at h
  exact h

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨1, 0, 0, 0, 4⟩) (by execute fm 28)
  apply progress_nonhalt_simple (fm := fm) (A := ℕ × ℕ)
    (fun ⟨a, f⟩ ↦ ⟨a + 1, 0, 0, 0, f + 3⟩) ⟨0, 1⟩
  intro ⟨a, f⟩; exact ⟨⟨a + 3, 2 * f⟩, main_trans a f⟩

end Sz22_2003_unofficial_44
