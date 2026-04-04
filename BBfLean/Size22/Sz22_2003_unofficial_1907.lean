import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #1907: [9/35, 65/33, 98/3, 11/13, 39/2]

Vector representation:
```
 0  2 -1 -1  0  0
 0 -1  1  0 -1  1
 1 -1  0  2  0  0
 0  0  0  0  1 -1
-1  1  0  0  0  1
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_1907

def Q := ℕ × ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a, b, c+1, d+1, e, f⟩ => some ⟨a, b+2, c, d, e, f⟩
  | ⟨a, b+1, c, d, e+1, f⟩ => some ⟨a, b, c+1, d, e, f+1⟩
  | ⟨a, b+1, c, d, e, f⟩ => some ⟨a+1, b, c, d+2, e, f⟩
  | ⟨a, b, c, d, e, f+1⟩ => some ⟨a, b, c, d, e+1, f⟩
  | ⟨a+1, b, c, d, e, f⟩ => some ⟨a, b+1, c, d, e, f+1⟩
  | _ => none

-- R4 chain: transfer f to e.
theorem f_to_e : ∀ k, ∀ a d e, ⟨a, 0, 0, d, e, k⟩ [fm]⊢* ⟨a, 0, 0, d, e + k, 0⟩ := by
  intro k; induction' k with k ih <;> intro a d e
  · exists 0
  · step fm
    apply stepStar_trans (ih a d (e + 1))
    ring_nf; finish

-- R2+R1 interleave.
theorem r2r1_chain : ∀ k, ∀ A b d e f, ⟨A, b + 1, 0, d + k, e + k, f⟩ [fm]⊢* ⟨A, b + k + 1, 0, d, e, f + k⟩ := by
  intro k; induction' k with k ih <;> intro A b d e f
  · exists 0
  · rw [show d + (k + 1) = (d + k) + 1 from by ring,
        show e + (k + 1) = (e + k) + 1 from by ring]
    step fm
    step fm
    rw [show b + 2 = (b + 1) + 1 from by ring]
    apply stepStar_trans (ih A (b + 1) d e (f + 1))
    ring_nf; finish

-- R3 chain: convert b to a and d.
theorem r3_chain : ∀ k, ∀ A b d f, ⟨A, b + k, 0, d, 0, f⟩ [fm]⊢* ⟨A + k, b, 0, d + 2 * k, 0, f⟩ := by
  intro k; induction' k with k ih <;> intro A b d f
  · exists 0
  · rw [show b + (k + 1) = (b + k) + 1 from by ring]
    step fm
    apply stepStar_trans (ih (A + 1) b (d + 2) f)
    ring_nf; finish

-- Main macro transition
theorem main_trans : ∀ A F, ⟨A + 1, 0, 0, A + 2 * F + 2, 0, F + 1⟩ [fm]⊢⁺
    ⟨A + F + 2, 0, 0, A + 3 * F + 5, 0, F + 2⟩ := by
  intro A F
  -- Phase 1: f→e transfer
  have h1 : ⟨A + 1, 0, 0, A + 2 * F + 2, 0, F + 1⟩ [fm]⊢*
      ⟨A + 1, 0, 0, A + 2 * F + 2, F + 1, 0⟩ := by
    have := f_to_e (F + 1) (A + 1) (A + 2 * F + 2) 0
    simpa using this
  -- Phase 2: R5 step
  have h2 : ⟨A + 1, 0, 0, A + 2 * F + 2, F + 1, 0⟩ [fm]⊢
      ⟨A, 1, 0, A + 2 * F + 2, F + 1, 1⟩ := by
    simp [fm]
  -- Phase 3: R2+R1 chain
  have h3 : ⟨A, 1, 0, A + 2 * F + 2, F + 1, 1⟩ [fm]⊢*
      ⟨A, F + 2, 0, A + F + 1, 0, F + 2⟩ := by
    have := r2r1_chain (F + 1) A 0 (A + F + 1) 0 1
    convert this using 2; ring_nf
  -- Phase 4: R3 chain
  have h4 : ⟨A, F + 2, 0, A + F + 1, 0, F + 2⟩ [fm]⊢*
      ⟨A + F + 2, 0, 0, A + 3 * F + 5, 0, F + 2⟩ := by
    have := r3_chain (F + 2) A 0 (A + F + 1) (F + 2)
    convert this using 2; ring_nf
  -- Compose
  apply stepStar_stepPlus_stepPlus h1
  apply step_stepStar_stepPlus h2
  exact stepStar_trans h3 h4

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨1, 0, 0, 2, 0, 1⟩)
  · execute fm 2
  apply progress_nonhalt_simple (fm := fm) (A := ℕ × ℕ)
    (fun ⟨A, F⟩ ↦ ⟨A + 1, 0, 0, A + 2 * F + 2, 0, F + 1⟩) ⟨0, 0⟩
  intro ⟨A, F⟩
  refine ⟨⟨A + F + 1, F + 1⟩, ?_⟩
  show ⟨A + 1, 0, 0, A + 2 * F + 2, 0, F + 1⟩ [fm]⊢⁺
    ⟨A + F + 1 + 1, 0, 0, A + F + 1 + 2 * (F + 1) + 2, 0, F + 1 + 1⟩
  have h := main_trans A F
  convert h using 2; ring_nf
