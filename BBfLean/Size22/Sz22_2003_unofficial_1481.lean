import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #1481: [7/15, 44/3, 99/14, 5/11, 33/2]

Vector representation:
```
 0 -1 -1  1  0
 2 -1  0  0  1
-1  2  0 -1  1
 0  0  1  0 -1
-1  1  0  0  1
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_1481

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a, b+1, c+1, d, e⟩ => some ⟨a, b, c, d+1, e⟩
  | ⟨a, b+1, c, d, e⟩ => some ⟨a+2, b, c, d, e+1⟩
  | ⟨a+1, b, c, d+1, e⟩ => some ⟨a, b+2, c, d, e+1⟩
  | ⟨a, b, c, d, e+1⟩ => some ⟨a, b, c+1, d, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b+1, c, d, e+1⟩
  | _ => none

theorem r4_chain : ∀ k, ∀ a c,
    ⟨a, 0, c, 0, k⟩ [fm]⊢* ⟨a, 0, c + k, 0, 0⟩ := by
  intro k; induction' k with k ih <;> intro a c
  · simp; finish
  · step fm
    apply stepStar_trans (ih a (c + 1))
    ring_nf; finish

theorem r3r2r2_chain : ∀ k, ∀ a e,
    ⟨a + 1, 0, 0, k, e⟩ [fm]⊢* ⟨a + 3 * k + 1, 0, 0, 0, e + 3 * k⟩ := by
  intro k; induction' k with k ih <;> intro a e
  · simp; finish
  · rw [show (k : ℕ) + 1 = k + 1 from rfl]
    step fm; step fm; step fm
    apply stepStar_trans (ih (a + 3) (e + 3))
    ring_nf; finish

theorem loop_chain : ∀ k, ∀ a c d e,
    ⟨a + k, 0, c + 2 * k, d + 1, e⟩ [fm]⊢* ⟨a, 0, c, d + k + 1, e + k⟩ := by
  intro k; induction' k with k ih <;> intro a c d e
  · simp; finish
  · rw [show a + (k + 1) = (a + k) + 1 from by ring,
        show c + 2 * (k + 1) = (c + 2 * k) + 1 + 1 from by ring]
    step fm; step fm; step fm
    apply stepStar_trans (ih a c (d + 1) (e + 1))
    ring_nf; finish

theorem exit_step (a d e : ℕ) :
    ⟨a + 1, 0, 1, d + 1, e⟩ [fm]⊢* ⟨a + 2, 0, 0, d + 1, e + 2⟩ := by
  step fm; step fm; step fm; finish

theorem main_trans (a c : ℕ) :
    ⟨a + c + 2, 0, 2 * c + 2, 0, 0⟩ [fm]⊢⁺ ⟨a + 3 * c + 5, 0, 4 * c + 6, 0, 0⟩ := by
  -- Phase 0: R5 + R1
  have h0 : ⟨a + c + 2, 0, 2 * c + 2, 0, 0⟩ [fm]⊢⁺ ⟨a + c + 1, 0, 2 * c + 1, 1, 1⟩ := by
    rw [show a + c + 2 = (a + c + 1) + 1 from by ring,
        show 2 * c + 2 = (2 * c + 1) + 1 from by ring]
    step fm; step fm; finish
  -- Phase 1: loop c rounds
  have h1 : ⟨a + c + 1, 0, 2 * c + 1, 1, 1⟩ [fm]⊢* ⟨a + 1, 0, 1, c + 1, c + 1⟩ := by
    have := loop_chain c (a + 1) 1 0 1
    simp only [Nat.zero_add] at this
    rw [show a + 1 + c = a + c + 1 from by ring,
        show 1 + 2 * c = 2 * c + 1 from by ring,
        show 1 + c = c + 1 from by ring] at this
    exact this
  -- Phase 2: exit step
  have h2 : ⟨a + 1, 0, 1, c + 1, c + 1⟩ [fm]⊢* ⟨a + 2, 0, 0, c + 1, c + 3⟩ := by
    have := exit_step a c (c + 1)
    rw [show c + 1 + 2 = c + 3 from by ring] at this
    exact this
  -- Phase 3: R3R2R2 chain (c+1 rounds)
  have h3 : ⟨a + 2, 0, 0, c + 1, c + 3⟩ [fm]⊢* ⟨a + 3 * c + 5, 0, 0, 0, 4 * c + 6⟩ := by
    have := r3r2r2_chain (c + 1) (a + 1) (c + 3)
    rw [show a + 1 + 1 = a + 2 from by ring,
        show a + 1 + 3 * (c + 1) + 1 = a + 3 * c + 5 from by ring,
        show c + 3 + 3 * (c + 1) = 4 * c + 6 from by ring] at this
    exact this
  -- Phase 4: R4 chain
  have h4 : ⟨a + 3 * c + 5, 0, 0, 0, 4 * c + 6⟩ [fm]⊢*
      ⟨a + 3 * c + 5, 0, 4 * c + 6, 0, 0⟩ := by
    have := r4_chain (4 * c + 6) (a + 3 * c + 5) 0
    rw [show 0 + (4 * c + 6) = 4 * c + 6 from by ring] at this
    exact this
  exact stepPlus_stepStar_stepPlus h0
    (stepStar_trans h1 (stepStar_trans h2 (stepStar_trans h3 h4)))

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨2, 0, 2, 0, 0⟩) (by execute fm 4)
  apply progress_nonhalt_simple (fm := fm) (A := ℕ × ℕ)
    (fun ⟨a, c⟩ ↦ ⟨a + c + 2, 0, 2 * c + 2, 0, 0⟩) ⟨0, 0⟩
  intro ⟨a, c⟩
  refine ⟨⟨a + c + 1, 2 * c + 2⟩, ?_⟩
  have := main_trans a c
  rw [show a + 3 * c + 5 = (a + c + 1) + (2 * c + 2) + 2 from by ring,
      show 4 * c + 6 = 2 * (2 * c + 2) + 2 from by ring] at this
  exact this
