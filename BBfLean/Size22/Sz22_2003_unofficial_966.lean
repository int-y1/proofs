import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #966: [4/15, 33/14, 5/2, 7/11, 308/5]

Vector representation:
```
 2 -1 -1  0  0
-1  1  0 -1  1
-1  0  1  0  0
 0  0  0  1 -1
 2  0 -1  1  1
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_966

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a, b+1, c+1, d, e⟩ => some ⟨a+2, b, c, d, e⟩
  | ⟨a+1, b, c, d+1, e⟩ => some ⟨a, b+1, c, d, e+1⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b, c+1, d, e⟩
  | ⟨a, b, c, d, e+1⟩ => some ⟨a, b, c, d+1, e⟩
  | ⟨a, b, c+1, d, e⟩ => some ⟨a+2, b, c, d+1, e+1⟩
  | _ => none

-- Phase 1a: R2-R1 chain. Each round: (a+1, 0, c+1, d+1, e) -> R2 -> R1 -> (a+2, 0, c, d, e+1)
-- k rounds: (a+1, 0, c+k, d+k, e) ⊢* (a+1+k, 0, c, d, e+k)
theorem r2r1_chain : ∀ k, ∀ a c d e,
    ⟨a + 1, 0, c + k, d + k, e⟩ [fm]⊢* ⟨a + 1 + k, 0, c, d, e + k⟩ := by
  intro k; induction' k with k ih <;> intro a c d e
  · ring_nf; finish
  · rw [show c + (k + 1) = (c + k) + 1 from by ring,
        show d + (k + 1) = (d + k) + 1 from by ring,
        show (k : ℕ) + 1 = k + 1 from rfl]
    step fm; step fm
    apply stepStar_trans (ih (a + 1) c d (e + 1)); ring_nf; finish

-- Phase 2: R2 drain. (a+k, b, 0, k, e) ⊢* (a, b+k, 0, 0, e+k)
-- k rounds: each step (a+1, b, 0, d+1, e) -> (a, b+1, 0, d, e+1)
theorem r2_drain : ∀ k, ∀ a b e,
    ⟨a + k, b, 0, k, e⟩ [fm]⊢* ⟨a, b + k, 0, 0, e + k⟩ := by
  intro k; induction' k with k ih <;> intro a b e
  · ring_nf; finish
  · rw [show a + (k + 1) = (a + k) + 1 from by ring,
        show (k : ℕ) + 1 = k + 1 from rfl]
    step fm
    apply stepStar_trans (ih a (b + 1) (e + 1)); ring_nf; finish

-- Phase 3: R3-R1 alternating chain.
-- Each round: (a+1, b+1, 0, 0, e) -> R3 -> (a, b+1, 1, 0, e) -> R1 -> (a+2, b, 0, 0, e)
-- Net: a += 1, b -= 1. But first step from (1, b+1, 0, 0, e):
-- R3: (0, b+1, 1, 0, e) -> R1: (2, b, 0, 0, e)
-- So from (a, b+1, 0, 0, e) with a >= 1: 2 steps to (a+1, b, 0, 0, e)
theorem r3r1_chain : ∀ k, ∀ a e,
    ⟨a + 1, k, 0, 0, e⟩ [fm]⊢* ⟨a + 1 + k, 0, 0, 0, e⟩ := by
  intro k; induction' k with k ih <;> intro a e
  · ring_nf; finish
  · rw [show (k : ℕ) + 1 = k + 1 from rfl]
    step fm; step fm
    apply stepStar_trans (ih (a + 1) e); ring_nf; finish

-- Phase 4: R3 drain. (k, 0, c, 0, e) ⊢* (0, 0, c+k, 0, e)
theorem r3_drain : ∀ k, ∀ c e,
    ⟨k, 0, c, 0, e⟩ [fm]⊢* ⟨0, 0, c + k, 0, e⟩ := by
  intro k; induction' k with k ih <;> intro c e
  · ring_nf; finish
  · step fm; apply stepStar_trans (ih (c + 1) e); ring_nf; finish

-- Phase 5: R4 drain. (0, 0, c, d, k) ⊢* (0, 0, c, d+k, 0)
theorem r4_drain : ∀ k, ∀ c d,
    ⟨0, 0, c, d, k⟩ [fm]⊢* ⟨0, 0, c, d + k, 0⟩ := by
  intro k; induction' k with k ih <;> intro c d
  · ring_nf; finish
  · rw [show (k : ℕ) + 1 = k + 1 from rfl]
    step fm; apply stepStar_trans (ih c (d + 1)); ring_nf; finish

-- Main transition: (0, 0, n+2, 2n+2, 0) ⊢⁺ (0, 0, n+3, 2n+4, 0)
theorem main_trans (n : ℕ) :
    ⟨0, 0, n + 2, 2 * n + 2, 0⟩ [fm]⊢⁺ ⟨0, 0, n + 3, 2 * n + 4, 0⟩ := by
  -- Phase 1a: R5 step. (0, 0, (n+1)+1, 2n+2, 0) -> (2, 0, n+1, 2n+3, 1)
  have h1 : ⟨0, 0, n + 2, 2 * n + 2, 0⟩ [fm]⊢⁺
      ⟨2, 0, n + 1, 2 * n + 3, 1⟩ := by
    rw [show n + 2 = (n + 1) + 1 from by ring]
    apply step_stepPlus
    show fm ⟨0, 0, (n + 1) + 1, 2 * n + 2, 0⟩ = some ⟨2, 0, n + 1, 2 * n + 3, 1⟩
    unfold fm; simp only
  -- Phase 1b: R2-R1 chain (n+1 rounds).
  -- (2, 0, n+1, 2n+3, 1) = (1+1, 0, 0+(n+1), (n+2)+(n+1), 1)
  -- ⊢* (1+1+(n+1), 0, 0, n+2, 1+(n+1)) = (n+3, 0, 0, n+2, n+2)
  have h2 : ⟨2, 0, n + 1, 2 * n + 3, 1⟩ [fm]⊢*
      ⟨n + 3, 0, 0, n + 2, n + 2⟩ := by
    have := r2r1_chain (n + 1) 1 0 (n + 2) 1
    rw [show 1 + 1 = 2 from rfl,
        show 0 + (n + 1) = n + 1 from by ring,
        show (n + 2) + (n + 1) = 2 * n + 3 from by ring,
        show 1 + 1 + (n + 1) = n + 3 from by ring,
        show 1 + (n + 1) = n + 2 from by ring] at this
    exact this
  -- Phase 2: R2 drain (n+2 steps).
  -- (n+3, 0, 0, n+2, n+2) = (1+(n+2), 0, 0, n+2, n+2)
  -- ⊢* (1, n+2, 0, 0, n+2+(n+2)) = (1, n+2, 0, 0, 2n+4)
  have h3 : ⟨n + 3, 0, 0, n + 2, n + 2⟩ [fm]⊢*
      ⟨1, n + 2, 0, 0, 2 * n + 4⟩ := by
    have := r2_drain (n + 2) 1 0 (n + 2)
    rw [show 1 + (n + 2) = n + 3 from by ring,
        show 0 + (n + 2) = n + 2 from by ring,
        show (n + 2) + (n + 2) = 2 * n + 4 from by ring] at this
    exact this
  -- Phase 3: R3-R1 chain (n+2 rounds).
  -- (1, n+2, 0, 0, 2n+4) = (0+1, n+2, 0, 0, 2n+4)
  -- ⊢* (0+1+(n+2), 0, 0, 0, 2n+4) = (n+3, 0, 0, 0, 2n+4)
  have h4 : ⟨1, n + 2, 0, 0, 2 * n + 4⟩ [fm]⊢*
      ⟨n + 3, 0, 0, 0, 2 * n + 4⟩ := by
    have := r3r1_chain (n + 2) 0 (2 * n + 4)
    rw [show 0 + 1 = 1 from by ring,
        show 0 + 1 + (n + 2) = n + 3 from by ring] at this
    exact this
  -- Phase 4: R3 drain (n+3 steps).
  -- (n+3, 0, 0, 0, 2n+4) ⊢* (0, 0, 0+(n+3), 0, 2n+4) = (0, 0, n+3, 0, 2n+4)
  have h5 : ⟨n + 3, 0, 0, 0, 2 * n + 4⟩ [fm]⊢*
      ⟨0, 0, n + 3, 0, 2 * n + 4⟩ := by
    have := r3_drain (n + 3) 0 (2 * n + 4)
    rw [show 0 + (n + 3) = n + 3 from by ring] at this
    exact this
  -- Phase 5: R4 drain (2n+4 steps).
  -- (0, 0, n+3, 0, 2n+4) ⊢* (0, 0, n+3, 0+(2n+4), 0) = (0, 0, n+3, 2n+4, 0)
  have h6 : ⟨0, 0, n + 3, 0, 2 * n + 4⟩ [fm]⊢*
      ⟨0, 0, n + 3, 2 * n + 4, 0⟩ := by
    have := r4_drain (2 * n + 4) (n + 3) 0
    rw [show 0 + (2 * n + 4) = 2 * n + 4 from by ring] at this
    exact this
  -- Compose all phases
  exact stepPlus_stepStar_stepPlus h1
    (stepStar_trans h2 (stepStar_trans h3 (stepStar_trans h4 (stepStar_trans h5 h6))))

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨0, 0, 2, 2, 0⟩) (by execute fm 9)
  apply progress_nonhalt_simple (fm := fm) (A := ℕ)
    (fun n ↦ ⟨0, 0, n + 2, 2 * n + 2, 0⟩) 0
  intro n
  refine ⟨n + 1, ?_⟩
  show ⟨0, 0, n + 2, 2 * n + 2, 0⟩ [fm]⊢⁺ ⟨0, 0, (n + 1) + 2, 2 * (n + 1) + 2, 0⟩
  rw [show (n + 1) + 2 = n + 3 from by ring,
      show 2 * (n + 1) + 2 = 2 * n + 4 from by ring]
  exact main_trans n
