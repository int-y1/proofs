import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #1035: [45/2, 1/245, 26/55, 77/3, 5/91]

Vector representation:
```
-1  2  1  0  0  0
 0  0 -1 -2  0  0
 1  0 -1  0 -1  1
 0 -1  0  1  1  0
 0  0  1 -1  0 -1
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_1035

def Q := ℕ × ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a+1, b, c, d, e, f⟩ => some ⟨a, b+2, c+1, d, e, f⟩
  | ⟨a, b, c+1, d+2, e, f⟩ => some ⟨a, b, c, d, e, f⟩
  | ⟨a, b, c+1, d, e+1, f⟩ => some ⟨a+1, b, c, d, e, f+1⟩
  | ⟨a, b+1, c, d, e, f⟩ => some ⟨a, b, c, d+1, e+1, f⟩
  | ⟨a, b, c, d+1, e, f+1⟩ => some ⟨a, b, c+1, d, e, f⟩
  | _ => none

theorem r4_chain : ∀ k, ∀ d e f,
    ⟨(0 : ℕ), k, 0, d, e, f⟩ [fm]⊢* ⟨0, 0, 0, d + k, e + k, f⟩ := by
  intro k; induction' k with k ih <;> intro d e f
  · ring_nf; finish
  · rw [show d + (k + 1) = (d + 1) + k from by ring,
        show e + (k + 1) = (e + 1) + k from by ring]
    step fm
    apply stepStar_trans (ih (d + 1) (e + 1) f)
    ring_nf; finish

theorem r5r2_chain : ∀ k, ∀ d e f,
    ⟨(0 : ℕ), 0, 0, d + 3 * k, e, f + k⟩ [fm]⊢* ⟨0, 0, 0, d, e, f⟩ := by
  intro k; induction' k with k ih <;> intro d e f
  · ring_nf; finish
  · rw [show d + 3 * (k + 1) = (d + 3 * k) + 3 from by ring,
        show f + (k + 1) = (f + k) + 1 from by ring]
    step fm; step fm
    apply stepStar_trans (ih d e f)
    ring_nf; finish

theorem r1r3_chain : ∀ k, ∀ b f,
    ⟨(1 : ℕ), b, 0, 1, k, f⟩ [fm]⊢* ⟨1, b + 2 * k, 0, 1, 0, f + k⟩ := by
  intro k; induction' k with k ih <;> intro b f
  · ring_nf; finish
  · rw [show b + 2 * (k + 1) = (b + 2) + 2 * k from by ring,
        show f + (k + 1) = (f + 1) + k from by ring]
    step fm; step fm
    apply stepStar_trans (ih (b + 2) (f + 1))
    ring_nf; finish

theorem main_trans (n : ℕ) :
    ⟨(1 : ℕ), 3 * n + 1, 0, 1, 0, 2 * n + 1⟩ [fm]⊢⁺
    ⟨1, 6 * n + 4, 0, 1, 0, 4 * n + 3⟩ := by
  -- Phase 1+2: R1, R4, R2
  -- (1, 3n+1, 0, 1, 0, 2n+1) -> (0, 3n+3, 1, 1, 0, 2n+1)
  --   -> (0, 3n+2, 1, 2, 1, 2n+1) -> (0, 3n+2, 0, 0, 1, 2n+1)
  have h1 : ⟨(1 : ℕ), 3 * n + 1, 0, 1, 0, 2 * n + 1⟩ [fm]⊢⁺
      ⟨0, 3 * n + 2, 0, 0, 1, 2 * n + 1⟩ := by
    step fm; step fm; step fm; finish
  -- Phase 3: R4 chain (3n+2 steps)
  -- (0, 3n+2, 0, 0, 1, 2n+1) -> (0, 0, 0, 3n+2, 3n+3, 2n+1)
  have h2 : ⟨(0 : ℕ), 3 * n + 2, 0, 0, 1, 2 * n + 1⟩ [fm]⊢*
      ⟨0, 0, 0, 3 * n + 2, 3 * n + 3, 2 * n + 1⟩ := by
    have := r4_chain (3 * n + 2) 0 1 (2 * n + 1)
    convert this using 2; ring_nf
  -- Phase 4: R5+R2 chain (n steps)
  -- (0, 0, 0, 3n+2, 3n+3, 2n+1) -> (0, 0, 0, 2, 3n+3, n+1)
  have h3 : ⟨(0 : ℕ), 0, 0, 3 * n + 2, 3 * n + 3, 2 * n + 1⟩ [fm]⊢*
      ⟨0, 0, 0, 2, 3 * n + 3, n + 1⟩ := by
    have := r5r2_chain n 2 (3 * n + 3) (n + 1)
    convert this using 2; ring_nf
  -- Phase 5: R5 + R3
  -- (0, 0, 0, 2, 3n+3, n+1) -> (0, 0, 1, 1, 3n+3, n) -> (1, 0, 0, 1, 3n+2, n+1)
  have h4 : ⟨(0 : ℕ), 0, 0, 2, 3 * n + 3, n + 1⟩ [fm]⊢*
      ⟨1, 0, 0, 1, 3 * n + 2, n + 1⟩ := by
    step fm; step fm; finish
  -- Phase 6: R1+R3 chain (3n+2 steps)
  -- (1, 0, 0, 1, 3n+2, n+1) -> (1, 6n+4, 0, 1, 0, 4n+3)
  have h5 : ⟨(1 : ℕ), 0, 0, 1, 3 * n + 2, n + 1⟩ [fm]⊢*
      ⟨1, 6 * n + 4, 0, 1, 0, 4 * n + 3⟩ := by
    have := r1r3_chain (3 * n + 2) 0 (n + 1)
    convert this using 2; ring_nf
  exact stepPlus_stepStar_stepPlus h1
    (stepStar_trans h2
      (stepStar_trans h3
        (stepStar_trans h4 h5)))

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨1, 1, 0, 1, 0, 1⟩) (by execute fm 3)
  apply progress_nonhalt_simple (fm := fm) (A := ℕ)
    (fun n ↦ ⟨1, 3 * n + 1, 0, 1, 0, 2 * n + 1⟩) 0
  intro n
  exact ⟨2 * n + 1, by convert main_trans n using 2; ring_nf⟩

end Sz22_2003_unofficial_1035
