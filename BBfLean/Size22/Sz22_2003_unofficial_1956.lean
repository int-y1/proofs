import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #1956: [9/70, 77/15, 22/3, 5/11, 9/2]

Vector representation:
```
-1  2 -1 -1  0
 0 -1 -1  1  1
 1 -1  0  0  1
 0  0  1  0 -1
-1  2  0  0  0
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_1956

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a+1, b, c+1, d+1, e⟩ => some ⟨a, b+2, c, d, e⟩
  | ⟨a, b+1, c+1, d, e⟩ => some ⟨a, b, c, d+1, e+1⟩
  | ⟨a, b+1, c, d, e⟩ => some ⟨a+1, b, c, d, e+1⟩
  | ⟨a, b, c, d, e+1⟩ => some ⟨a, b, c+1, d, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b+2, c, d, e⟩
  | _ => none

theorem e_to_c : ∀ k, ⟨a, 0, c, 0, e + k⟩ [fm]⊢* ⟨a, 0, c + k, 0, e⟩ := by
  intro k; induction' k with k ih generalizing a c e
  · exists 0
  · rw [show e + (k + 1) = (e + k) + 1 from by ring]
    step fm
    apply stepStar_trans (ih (c := c + 1))
    ring_nf; finish

theorem b_to_ae : ∀ k, ⟨a, b + k, 0, 0, e⟩ [fm]⊢* ⟨a + k, b, 0, 0, e + k⟩ := by
  intro k; induction' k with k ih generalizing a b e
  · exists 0
  · rw [show b + (k + 1) = (b + k) + 1 from by ring]
    step fm
    apply stepStar_trans (ih (a := a + 1) (e := e + 1))
    ring_nf; finish

theorem r2r1_chain : ∀ k, ⟨a + k, b + 1, c + 2 * k, 0, e⟩ [fm]⊢* ⟨a, b + k + 1, c, 0, e + k⟩ := by
  intro k; induction' k with k ih generalizing a b c e
  · exists 0
  · rw [show a + (k + 1) = (a + k) + 1 from by ring,
        show c + 2 * (k + 1) = (c + 2 * k) + 1 + 1 from by ring]
    step fm
    step fm
    apply stepStar_trans (ih (b := b + 1) (e := e + 1))
    ring_nf; finish

-- R5 step for symbolic c: (a+1, 0, c, 0, 0) → (a, 2, c, 0, 0)
theorem r5_step : ⟨a + 1, 0, c, 0, 0⟩ [fm]⊢ ⟨a, 2, c, 0, 0⟩ := by
  simp [fm]

theorem main_trans : ⟨n + 2, 0, 0, 0, 2 * n + 2⟩ [fm]⊢⁺ ⟨n + 3, 0, 0, 0, 2 * n + 4⟩ := by
  -- Phase 1: R4 chain: (n+2, 0, 0, 0, 2n+2) →* (n+2, 0, 2n+2, 0, 0)
  rw [show 2 * n + 2 = 0 + (2 * n + 2) from by ring]
  apply stepStar_stepPlus_stepPlus (e_to_c (2 * n + 2) (a := n + 2) (c := 0) (e := 0))
  -- Phase 2: R5: (n+2, 0, 2n+2, 0, 0) → (n+1, 2, 2n+2, 0, 0)
  rw [show 0 + (2 * n + 2) = 2 * n + 2 from by ring,
      show n + 2 = (n + 1) + 1 from by ring]
  apply step_stepStar_stepPlus (r5_step (a := n + 1) (c := 2 * n + 2))
  -- Phase 3: R2+R1 interleave: n+1 rounds
  -- State: (n+1, 2, 2n+2, 0, 0)
  -- Need to show: (n+1, 2, 2n+2, 0, 0) ⊢* (n+3, 0, 0, 0, 2n+4)
  -- r2r1_chain with a=0, k=n+1, b=1, c=0, e=0:
  --   (0+(n+1), 1+1, 0+2*(n+1), 0, 0) ⊢* (0, 1+(n+1)+1, 0, 0, 0+(n+1))
  rw [show n + 1 = 0 + (n + 1) from by ring,
      show (2 : ℕ) = 1 + 1 from by ring,
      show 2 * n + 2 = 0 + 2 * (n + 1) from by ring]
  apply stepStar_trans (r2r1_chain (n + 1) (a := 0) (b := 1) (c := 0) (e := 0))
  -- Phase 4: R3 chain: (0, n+3, 0, 0, n+1) →* (n+3, 0, 0, 0, 2n+4)
  rw [show 1 + (n + 1) + 1 = 0 + (n + 3) from by ring,
      show 0 + (n + 1) = n + 1 from by ring]
  apply stepStar_trans (b_to_ae (n + 3) (a := 0) (b := 0) (e := n + 1))
  ring_nf; finish

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨2, 0, 0, 0, 2⟩) (by execute fm 3)
  apply progress_nonhalt_simple (fm := fm) (A := ℕ)
    (fun n ↦ ⟨n + 2, 0, 0, 0, 2 * n + 2⟩) 0
  intro n; exact ⟨n + 1, main_trans⟩
