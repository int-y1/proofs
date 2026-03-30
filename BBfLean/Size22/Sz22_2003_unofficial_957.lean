import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #957: [4/15, 33/14, 325/2, 7/11, 14/13]

Vector representation:
```
 2 -1 -1  0  0  0
-1  1  0 -1  1  0
-1  0  2  0  0  1
 0  0  0  1 -1  0
 1  0  0  1  0 -1
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_957

def Q := ℕ × ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a, b+1, c+1, d, e, f⟩ => some ⟨a+2, b, c, d, e, f⟩
  | ⟨a+1, b, c, d+1, e, f⟩ => some ⟨a, b+1, c, d, e+1, f⟩
  | ⟨a+1, b, c, d, e, f⟩ => some ⟨a, b, c+2, d, e, f+1⟩
  | ⟨a, b, c, d, e+1, f⟩ => some ⟨a, b, c, d+1, e, f⟩
  | ⟨a, b, c, d, e, f+1⟩ => some ⟨a+1, b, c, d+1, e, f⟩
  | _ => none

-- R1/R2 interleaved chain (same pattern as 928 but with 6 registers)
-- From (a, 1, c+d+1, d, e, f) to (a+d, 1, c+1, 0, e+d, f)
theorem r1r2_chain : ∀ d, ∀ a c e f,
    ⟨a, 1, c + d + 1, d, e, f⟩ [fm]⊢* ⟨a + d, 1, c + 1, 0, e + d, f⟩ := by
  intro d; induction' d with d ih <;> intro a c e f
  · ring_nf; finish
  · rw [show c + (d + 1) + 1 = (c + d + 1) + 1 from by ring,
        show (d : ℕ) + 1 = d + 1 from rfl]
    step fm; step fm
    apply stepStar_trans (ih (a + 1) c (e + 1) f); ring_nf; finish

-- R3 drain: (k, 0, c, 0, e, f) ⊢* (0, 0, c+2*k, 0, e, f+k)
theorem r3_drain : ∀ k, ∀ c e f,
    ⟨k, 0, c, 0, e, f⟩ [fm]⊢* ⟨0, 0, c + 2 * k, 0, e, f + k⟩ := by
  intro k; induction' k with k ih <;> intro c e f
  · ring_nf; finish
  · step fm; apply stepStar_trans (ih (c + 2) e (f + 1)); ring_nf; finish

-- R4 drain: (0, 0, c, d, k, f) ⊢* (0, 0, c, d+k, 0, f)
theorem r4_drain : ∀ k, ∀ c d f,
    ⟨0, 0, c, d, k, f⟩ [fm]⊢* ⟨0, 0, c, d + k, 0, f⟩ := by
  intro k; induction' k with k ih <;> intro c d f
  · ring_nf; finish
  · rw [show (k : ℕ) + 1 = k + 1 from rfl]
    step fm; apply stepStar_trans (ih c (d + 1) f); ring_nf; finish

-- Main transition: (0, 0, g+2*d+2, d, 0, g+1) ⊢⁺ (0, 0, g+3*d+5, d+1, 0, g+d+2)
-- Using g = f-1 to avoid natural number subtraction
theorem main_trans (d g : ℕ) :
    ⟨0, 0, g + 2 * d + 2, d, 0, g + 1⟩ [fm]⊢⁺ ⟨0, 0, g + 3 * d + 5, d + 1, 0, g + d + 2⟩ := by
  -- Phase 1: R5 kick
  have h1 : ⟨0, 0, g + 2 * d + 2, d, 0, g + 1⟩ [fm]⊢⁺
      ⟨1, 0, g + 2 * d + 2, d + 1, 0, g⟩ := by
    apply step_stepPlus
    show fm ⟨0, 0, g + 2 * d + 2, d, 0, g + 1⟩ = some ⟨1, 0, g + 2 * d + 2, d + 1, 0, g⟩
    unfold fm; simp only
  -- Phase 2: R2 kick
  have h2 : ⟨1, 0, g + 2 * d + 2, d + 1, 0, g⟩ [fm]⊢*
      ⟨0, 1, g + 2 * d + 2, d, 1, g⟩ := by
    rw [show d + 1 = d + 1 from rfl]
    apply step_stepStar
    show fm ⟨1, 0, g + 2 * d + 2, d + 1, 0, g⟩ = some ⟨0, 1, g + 2 * d + 2, d, 1, g⟩
    unfold fm; simp only
  -- Phase 3: R1/R2 chain
  have h3 : ⟨0, 1, g + 2 * d + 2, d, 1, g⟩ [fm]⊢*
      ⟨d, 1, g + d + 2, 0, d + 1, g⟩ := by
    have := r1r2_chain d 0 (g + d + 1) 1 g
    rw [show (g + d + 1) + d + 1 = g + 2 * d + 2 from by ring,
        show 0 + d = d from by ring,
        show 1 + d = d + 1 from by ring,
        show (g + d + 1) + 1 = g + d + 2 from by ring] at this
    exact this
  -- Phase 4: Last R1
  have h4 : ⟨d, 1, g + d + 2, 0, d + 1, g⟩ [fm]⊢*
      ⟨d + 2, 0, g + d + 1, 0, d + 1, g⟩ := by
    rw [show g + d + 2 = (g + d + 1) + 1 from by ring]
    apply step_stepStar
    show fm ⟨d, 1, (g + d + 1) + 1, 0, d + 1, g⟩ = some ⟨d + 2, 0, g + d + 1, 0, d + 1, g⟩
    unfold fm; simp only
  -- Phase 5: R3 drain
  have h5 : ⟨d + 2, 0, g + d + 1, 0, d + 1, g⟩ [fm]⊢*
      ⟨0, 0, g + 3 * d + 5, 0, d + 1, g + d + 2⟩ := by
    have := r3_drain (d + 2) (g + d + 1) (d + 1) g
    rw [show (g + d + 1) + 2 * (d + 2) = g + 3 * d + 5 from by ring,
        show g + (d + 2) = g + d + 2 from by ring] at this
    exact this
  -- Phase 6: R4 drain
  have h6 : ⟨0, 0, g + 3 * d + 5, 0, d + 1, g + d + 2⟩ [fm]⊢*
      ⟨0, 0, g + 3 * d + 5, d + 1, 0, g + d + 2⟩ := by
    have := r4_drain (d + 1) (g + 3 * d + 5) 0 (g + d + 2)
    rw [show 0 + (d + 1) = d + 1 from by ring] at this
    exact this
  -- Compose all phases
  exact stepPlus_stepStar_stepPlus h1
    (stepStar_trans h2 (stepStar_trans h3 (stepStar_trans h4 (stepStar_trans h5 h6))))

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨0, 0, 2, 0, 0, 1⟩) (by execute fm 1)
  apply progress_nonhalt_simple (fm := fm) (A := ℕ × ℕ)
    (fun ⟨d, g⟩ ↦ ⟨0, 0, g + 2 * d + 2, d, 0, g + 1⟩) ⟨0, 0⟩
  intro ⟨d, g⟩
  refine ⟨⟨d + 1, g + d + 1⟩, ?_⟩
  show ⟨0, 0, g + 2 * d + 2, d, 0, g + 1⟩ [fm]⊢⁺
    ⟨0, 0, (g + d + 1) + 2 * (d + 1) + 2, d + 1, 0, (g + d + 1) + 1⟩
  rw [show (g + d + 1) + 2 * (d + 1) + 2 = g + 3 * d + 5 from by ring,
      show (g + d + 1) + 1 = g + d + 2 from by ring]
  exact main_trans d g
