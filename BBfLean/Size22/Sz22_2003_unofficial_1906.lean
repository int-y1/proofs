import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #1906: [9/35, 65/33, 28/3, 11/13, 39/2]

Vector representation:
```
 0  2 -1 -1  0  0
 0 -1  1  0 -1  1
 2 -1  0  1  0  0
 0  0  0  0  1 -1
-1  1  0  0  0  1
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_1906

def Q := ℕ × ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a, b, c+1, d+1, e, f⟩ => some ⟨a, b+2, c, d, e, f⟩
  | ⟨a, b+1, c, d, e+1, f⟩ => some ⟨a, b, c+1, d, e, f+1⟩
  | ⟨a, b+1, c, d, e, f⟩ => some ⟨a+2, b, c, d+1, e, f⟩
  | ⟨a, b, c, d, e, f+1⟩ => some ⟨a, b, c, d, e+1, f⟩
  | ⟨a+1, b, c, d, e, f⟩ => some ⟨a, b+1, c, d, e, f+1⟩
  | _ => none

-- R4 repeated: move f to e.
theorem f_to_e : ∀ k, ∀ a d e, ⟨a, 0, 0, d, e, k⟩ [fm]⊢* ⟨a, 0, 0, d, e + k, 0⟩ := by
  intro k; induction' k with k ih <;> intro a d e
  · exists 0
  · rw [show (k + 1 : ℕ) = k + 1 from rfl]
    step fm
    apply stepStar_trans (ih a d (e + 1))
    ring_nf; finish

-- R2+R1 interleaved chain: each round reduces d and e by 1, increases b by 1, increases f by 1.
theorem interleave : ∀ k, ∀ a b g, ⟨a, b + 1, 0, k, k, g⟩ [fm]⊢* ⟨a, b + k + 1, 0, 0, 0, g + k⟩ := by
  intro k; induction' k with k ih <;> intro a b g
  · exists 0
  · step fm
    step fm
    rw [show b + 2 = (b + 1) + 1 from by ring]
    apply stepStar_trans (ih a (b + 1) (g + 1))
    ring_nf; finish

-- R3 repeated: drain b, adding 2 to a and 1 to d each time.
theorem b_drain : ∀ k, ∀ a d f, ⟨a, k, 0, d, 0, f⟩ [fm]⊢* ⟨a + 2 * k, 0, 0, d + k, 0, f⟩ := by
  intro k; induction' k with k ih <;> intro a d f
  · exists 0
  · rw [show (k + 1 : ℕ) = k + 1 from rfl]
    step fm
    apply stepStar_trans (ih (a + 2) (d + 1) f)
    ring_nf; finish

-- Main transition: (n^2+2n+2, 0, 0, n+1, 0, n+1) →⁺ (n^2+4n+5, 0, 0, n+2, 0, n+2)
theorem main_trans (n : ℕ) : ⟨n * n + 2 * n + 2, 0, 0, n + 1, 0, n + 1⟩ [fm]⊢⁺
    ⟨n * n + 4 * n + 5, 0, 0, n + 2, 0, n + 2⟩ := by
  -- Phase 1: f_to_e
  apply stepStar_stepPlus_stepPlus (f_to_e (n + 1) (n * n + 2 * n + 2) (n + 1) 0)
  -- Phase 2: R5
  rw [show 0 + (n + 1) = n + 1 from by ring]
  apply step_stepStar_stepPlus
  · show fm ⟨n * n + 2 * n + 2, 0, 0, n + 1, n + 1, 0⟩ = some ⟨n * n + 2 * n + 1, 1, 0, n + 1, n + 1, 1⟩
    simp [fm]
  -- Phase 3: interleave
  apply stepStar_trans (interleave (n + 1) (n * n + 2 * n + 1) 0 1)
  -- Phase 4: b_drain
  rw [show 0 + (n + 1) + 1 = n + 2 from by ring,
      show 1 + (n + 1) = n + 2 from by ring]
  apply stepStar_trans (b_drain (n + 2) (n * n + 2 * n + 1) 0 (n + 2))
  ring_nf; finish

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨2, 0, 0, 1, 0, 1⟩) (by execute fm 2)
  apply progress_nonhalt_simple (fm := fm) (A := ℕ)
    (fun n ↦ ⟨n * n + 2 * n + 2, 0, 0, n + 1, 0, n + 1⟩) 0
  intro n
  refine ⟨n + 1, ?_⟩
  show ⟨n * n + 2 * n + 2, 0, 0, n + 1, 0, n + 1⟩ [fm]⊢⁺
    ⟨(n + 1) * (n + 1) + 2 * (n + 1) + 2, 0, 0, (n + 1) + 1, 0, (n + 1) + 1⟩
  rw [show (n + 1) * (n + 1) + 2 * (n + 1) + 2 = n * n + 4 * n + 5 from by ring,
      show (n + 1) + 1 = n + 2 from by ring]
  exact main_trans n
