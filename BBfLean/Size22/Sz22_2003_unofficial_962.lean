import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #962: [4/15, 33/14, 3575/2, 7/11, 3/13]

Vector representation:
```
 2 -1 -1  0  0  0
-1  1  0 -1  1  0
-1  0  2  0  1  1
 0  0  0  1 -1  0
 0  1  0  0  0 -1
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_962

def Q := ℕ × ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a, b+1, c+1, d, e, f⟩ => some ⟨a+2, b, c, d, e, f⟩
  | ⟨a+1, b, c, d+1, e, f⟩ => some ⟨a, b+1, c, d, e+1, f⟩
  | ⟨a+1, b, c, d, e, f⟩ => some ⟨a, b, c+2, d, e+1, f+1⟩
  | ⟨a, b, c, d, e+1, f⟩ => some ⟨a, b, c, d+1, e, f⟩
  | ⟨a, b, c, d, e, f+1⟩ => some ⟨a, b+1, c, d, e, f⟩
  | _ => none

-- R4 drain: (0, 0, c, d, k, f) ⊢* (0, 0, c, d+k, 0, f)
theorem r4_drain : ∀ k, ∀ c d f,
    ⟨0, 0, c, d, k, f⟩ [fm]⊢* ⟨0, 0, c, d + k, 0, f⟩ := by
  intro k; induction' k with k ih <;> intro c d f
  · ring_nf; finish
  · rw [show (k : ℕ) + 1 = k + 1 from rfl]
    step fm; apply stepStar_trans (ih c (d + 1) f); ring_nf; finish

-- R2/R1 chain: (a+1, 0, d+k, d, e, f) ⊢* (a+1+d, 0, k, 0, e+d, f)
-- Each round: R2 then R1 (needs a+1 >= 1 for R2, and d+k >= d+1 >= 1 for R1 in each round)
theorem r2r1_chain : ∀ d, ∀ a k e f,
    ⟨a + 1, 0, d + k, d, e, f⟩ [fm]⊢* ⟨a + 1 + d, 0, k, 0, e + d, f⟩ := by
  intro d; induction' d with d ih <;> intro a k e f
  · ring_nf; finish
  · rw [show d + 1 + k = (d + k) + 1 from by ring,
        show (d : ℕ) + 1 = d + 1 from rfl]
    step fm; step fm
    apply stepStar_trans (ih (a + 1) k (e + 1) f); ring_nf; finish

-- R3 drain: (k, 0, c, 0, e, f) ⊢* (0, 0, c+2*k, 0, e+k, f+k)
theorem r3_drain : ∀ k, ∀ c e f,
    ⟨k, 0, c, 0, e, f⟩ [fm]⊢* ⟨0, 0, c + 2 * k, 0, e + k, f + k⟩ := by
  intro k; induction' k with k ih <;> intro c e f
  · ring_nf; finish
  · step fm; apply stepStar_trans (ih (c + 2) (e + 1) (f + 1)); ring_nf; finish

-- Canonical state: (0, 0, h+2*g+2, 0, h+g+1, h+1) parameterized by (h, g)
-- Transition: (h, g) → (2*h+g+2, g+1)
theorem main_trans (h g : ℕ) :
    ⟨0, 0, h + 2 * g + 2, 0, h + g + 1, h + 1⟩ [fm]⊢⁺
    ⟨0, 0, 2 * h + 3 * g + 6, 0, 2 * h + 2 * g + 4, 2 * h + g + 3⟩ := by
  -- Phase 1: R4 drain (h+g+1 steps)
  have h1 : ⟨0, 0, h + 2 * g + 2, 0, h + g + 1, h + 1⟩ [fm]⊢*
      ⟨0, 0, h + 2 * g + 2, h + g + 1, 0, h + 1⟩ := by
    have := r4_drain (h + g + 1) (h + 2 * g + 2) 0 (h + 1)
    rw [show 0 + (h + g + 1) = h + g + 1 from by ring] at this
    exact this
  -- Phase 2: R5 then R1 (two steps)
  have h2 : ⟨0, 0, h + 2 * g + 2, h + g + 1, 0, h + 1⟩ [fm]⊢⁺
      ⟨2, 0, h + 2 * g + 1, h + g + 1, 0, h⟩ := by
    rw [show h + 1 = h + 1 from rfl,
        show h + 2 * g + 2 = (h + 2 * g + 1) + 1 from by ring]
    apply step_stepStar_stepPlus
    · show fm ⟨0, 0, (h + 2 * g + 1) + 1, h + g + 1, 0, h + 1⟩ =
        some ⟨0, 1, (h + 2 * g + 1) + 1, h + g + 1, 0, h⟩
      unfold fm; simp only
    · apply step_stepStar
      show fm ⟨0, 1, (h + 2 * g + 1) + 1, h + g + 1, 0, h⟩ =
        some ⟨2, 0, h + 2 * g + 1, h + g + 1, 0, h⟩
      unfold fm; simp only
  -- Phase 3: R2/R1 chain (h+g+1 rounds)
  have h3 : ⟨2, 0, h + 2 * g + 1, h + g + 1, 0, h⟩ [fm]⊢*
      ⟨h + g + 3, 0, g, 0, h + g + 1, h⟩ := by
    have := r2r1_chain (h + g + 1) 1 g 0 h
    rw [show 1 + 1 = 2 from rfl,
        show (h + g + 1) + g = h + 2 * g + 1 from by ring,
        show 1 + 1 + (h + g + 1) = h + g + 3 from by ring,
        show 0 + (h + g + 1) = h + g + 1 from by ring] at this
    exact this
  -- Phase 4: R3 drain (h+g+3 steps)
  have h4 : ⟨h + g + 3, 0, g, 0, h + g + 1, h⟩ [fm]⊢*
      ⟨0, 0, 2 * h + 3 * g + 6, 0, 2 * h + 2 * g + 4, 2 * h + g + 3⟩ := by
    have := r3_drain (h + g + 3) g (h + g + 1) h
    rw [show g + 2 * (h + g + 3) = 2 * h + 3 * g + 6 from by ring,
        show (h + g + 1) + (h + g + 3) = 2 * h + 2 * g + 4 from by ring,
        show h + (h + g + 3) = 2 * h + g + 3 from by ring] at this
    exact this
  -- Compose all phases
  exact stepStar_stepPlus_stepPlus h1
    (stepPlus_stepStar_stepPlus h2 (stepStar_trans h3 h4))

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨0, 0, 2, 0, 1, 1⟩) (by execute fm 1)
  apply progress_nonhalt_simple (fm := fm) (A := ℕ × ℕ)
    (fun ⟨h, g⟩ ↦ ⟨0, 0, h + 2 * g + 2, 0, h + g + 1, h + 1⟩) ⟨0, 0⟩
  intro ⟨h, g⟩
  refine ⟨⟨2 * h + g + 2, g + 1⟩, ?_⟩
  show ⟨0, 0, h + 2 * g + 2, 0, h + g + 1, h + 1⟩ [fm]⊢⁺
    ⟨0, 0, (2 * h + g + 2) + 2 * (g + 1) + 2, 0, (2 * h + g + 2) + (g + 1) + 1, (2 * h + g + 2) + 1⟩
  rw [show (2 * h + g + 2) + 2 * (g + 1) + 2 = 2 * h + 3 * g + 6 from by ring,
      show (2 * h + g + 2) + (g + 1) + 1 = 2 * h + 2 * g + 4 from by ring,
      show (2 * h + g + 2) + 1 = 2 * h + g + 3 from by ring]
  exact main_trans h g
