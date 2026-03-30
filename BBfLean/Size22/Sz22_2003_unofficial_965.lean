import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #965: [4/15, 33/14, 5/2, 7/11, 28/5]

Vector representation:
```
 2 -1 -1  0  0
-1  1  0 -1  1
-1  0  1  0  0
 0  0  0  1 -1
 2  0 -1  1  0
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_965

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a, b+1, c+1, d, e⟩ => some ⟨a+2, b, c, d, e⟩
  | ⟨a+1, b, c, d+1, e⟩ => some ⟨a, b+1, c, d, e+1⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b, c+1, d, e⟩
  | ⟨a, b, c, d, e+1⟩ => some ⟨a, b, c, d+1, e⟩
  | ⟨a, b, c+1, d, e⟩ => some ⟨a+2, b, c, d+1, e⟩
  | _ => none

-- Phase 1: R4 drain e to d: (0, 0, c, d, e+k) ⊢* (0, 0, c, d+k, e)
theorem r4_drain : ∀ k, ∀ c d e,
    ⟨0, 0, c, d, e + k⟩ [fm]⊢* ⟨0, 0, c, d + k, e⟩ := by
  intro k; induction' k with k ih <;> intro c d e
  · ring_nf; finish
  · rw [show e + (k + 1) = (e + k) + 1 from by ring]
    step fm; apply stepStar_trans (ih c (d + 1) e); ring_nf; finish

-- Phase 3: R2+R1 chain: (a+1, 0, c+k, d+k, e) ⊢* (a+1+k, 0, c, d, e+k)
-- Each round: R2 then R1
theorem r2r1_chain : ∀ k, ∀ a c d e,
    ⟨a + 1, 0, c + k, d + k, e⟩ [fm]⊢* ⟨a + 1 + k, 0, c, d, e + k⟩ := by
  intro k; induction' k with k ih <;> intro a c d e
  · ring_nf; finish
  · rw [show c + (k + 1) = (c + k) + 1 from by ring,
        show d + (k + 1) = (d + k) + 1 from by ring]
    step fm; step fm
    apply stepStar_trans (ih (a + 1) c d (e + 1)); ring_nf; finish

-- Phase 6: R3 drain: (k, 0, c, 0, e) ⊢* (0, 0, c+k, 0, e)
theorem r3_drain : ∀ k, ∀ c e,
    ⟨k, 0, c, 0, e⟩ [fm]⊢* ⟨0, 0, c + k, 0, e⟩ := by
  intro k; induction' k with k ih <;> intro c e
  · ring_nf; finish
  · step fm; apply stepStar_trans (ih (c + 1) e); ring_nf; finish

-- Main transition: (0, 0, n+1, 0, n) ⊢⁺ (0, 0, n+2, 0, n+1)
theorem main_trans (n : ℕ) :
    ⟨0, 0, n + 1, 0, n⟩ [fm]⊢⁺ ⟨0, 0, n + 2, 0, n + 1⟩ := by
  -- Phase 1: R4 drain e→d: (0, 0, n+1, 0, n) ⊢* (0, 0, n+1, n, 0)
  have h1 : ⟨0, 0, n + 1, 0, n⟩ [fm]⊢* ⟨0, 0, n + 1, n, 0⟩ := by
    have := r4_drain n (n + 1) 0 0
    simpa using this
  -- Phase 2: R5 step: (0, 0, n+1, n, 0) → (2, 0, n, n+1, 0)
  have h2 : ⟨0, 0, n + 1, n, 0⟩ [fm]⊢⁺ ⟨2, 0, n, n + 1, 0⟩ := by
    rw [show n + 1 = n + 1 from rfl]
    apply step_stepStar_stepPlus
    · show fm ⟨0, 0, n + 1, n, 0⟩ = some ⟨2, 0, n, n + 1, 0⟩
      unfold fm; simp only
    · finish
  -- Phase 3: R2+R1 chain: (2, 0, n, n+1, 0) ⊢* (n+2, 0, 0, 1, n)
  have h3 : ⟨2, 0, n, n + 1, 0⟩ [fm]⊢* ⟨n + 2, 0, 0, 1, n⟩ := by
    have := r2r1_chain n 1 0 1 0
    rw [show 1 + 1 = 2 from rfl] at this
    convert this using 2; ring_nf
  -- Phase 4: R2: (n+2, 0, 0, 1, n) → (n+1, 1, 0, 0, n+1)
  have h4 : ⟨n + 2, 0, 0, 1, n⟩ [fm]⊢* ⟨n + 1, 1, 0, 0, n + 1⟩ := by
    rw [show n + 2 = (n + 1) + 1 from by ring,
        show 1 = 0 + 1 from by ring]
    step fm; ring_nf; finish
  -- Phase 5: R3 then R1: (n+1, 1, 0, 0, n+1) → (n+2, 0, 0, 0, n+1)
  have h5 : ⟨n + 1, 1, 0, 0, n + 1⟩ [fm]⊢* ⟨n + 2, 0, 0, 0, n + 1⟩ := by
    rw [show n + 1 = n + 1 from rfl]
    step fm; step fm; ring_nf; finish
  -- Phase 6: R3 drain: (n+2, 0, 0, 0, n+1) ⊢* (0, 0, n+2, 0, n+1)
  have h6 : ⟨n + 2, 0, 0, 0, n + 1⟩ [fm]⊢* ⟨0, 0, n + 2, 0, n + 1⟩ := by
    have := r3_drain (n + 2) 0 (n + 1)
    rw [show 0 + (n + 2) = n + 2 from by ring] at this
    exact this
  -- Compose all phases
  exact stepStar_stepPlus_stepPlus h1
    (stepPlus_stepStar_stepPlus h2 (stepStar_trans h3 (stepStar_trans h4 (stepStar_trans h5 h6))))

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨0, 0, 1, 0, 0⟩) (by execute fm 1)
  apply progress_nonhalt_simple (fm := fm) (A := ℕ)
    (fun n ↦ ⟨0, 0, n + 1, 0, n⟩) 0
  intro n
  refine ⟨n + 1, ?_⟩
  exact main_trans n
