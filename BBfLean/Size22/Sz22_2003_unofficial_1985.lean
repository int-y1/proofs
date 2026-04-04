import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #1985: [99/35, 4/5, 5/6, 7/11, 165/2]

Vector representation:
```
 0  2 -1 -1  1
 2  0 -1  0  0
-1 -1  1  0  0
 0  0  0  1 -1
-1  1  1  0  1
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_1985

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a, b, c+1, d+1, e⟩ => some ⟨a, b+2, c, d, e+1⟩
  | ⟨a, b, c+1, d, e⟩ => some ⟨a+2, b, c, d, e⟩
  | ⟨a+1, b+1, c, d, e⟩ => some ⟨a, b, c+1, d, e⟩
  | ⟨a, b, c, d, e+1⟩ => some ⟨a, b, c, d+1, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b+1, c+1, d, e+1⟩
  | _ => none

-- R4 chain: move e to d
theorem e_to_d : ∀ k, ⟨a, 0, 0, d, e + k⟩ [fm]⊢* ⟨a, 0, 0, d + k, e⟩ := by
  intro k; induction' k with k ih generalizing d e
  · exists 0
  · rw [show e + (k + 1) = (e + k) + 1 from by ring]
    step fm
    apply stepStar_trans (ih (d := d + 1) (e := e))
    ring_nf; finish

-- R1+R3 interleave: k rounds
theorem r1r3_chain : ∀ k, ⟨a + k, b, 1, d + k, e⟩ [fm]⊢* ⟨a, b + k, 1, d, e + k⟩ := by
  intro k; induction' k with k ih generalizing a b d e
  · exists 0
  · rw [show a + (k + 1) = (a + k) + 1 from by ring,
        show d + (k + 1) = (d + k) + 1 from by ring]
    step fm
    step fm
    apply stepStar_trans (ih (a := a) (b := b + 1) (d := d) (e := e + 1))
    ring_nf; finish

-- R3+R2 drain: each pair does a+=1, b-=1
theorem r3r2_drain : ∀ k, ⟨a + 1, b + k, 0, 0, e⟩ [fm]⊢* ⟨a + 1 + k, b, 0, 0, e⟩ := by
  intro k; induction' k with k ih generalizing a b e
  · exists 0
  · rw [show b + (k + 1) = (b + k) + 1 from by ring]
    step fm
    step fm
    apply stepStar_trans (ih (a := a + 1) (b := b) (e := e))
    ring_nf; finish

-- Main transition: (2n+3, 0, 0, 0, n+1) ⊢⁺ (2n+5, 0, 0, 0, n+2)
theorem main_trans : ⟨2 * n + 3, 0, 0, 0, n + 1⟩ [fm]⊢⁺ ⟨2 * n + 5, 0, 0, 0, n + 2⟩ := by
  -- Phase 1: e_to_d
  rw [show (n + 1 : ℕ) = 0 + (n + 1) from by ring]
  apply stepStar_stepPlus_stepPlus (e_to_d (n + 1) (a := 2 * n + 3) (d := 0) (e := 0))
  -- State: (2n+3, 0, 0, n+1, 0)
  -- Phase 2: R5
  rw [show 2 * n + 3 = (2 * n + 2) + 1 from by ring]
  apply step_stepStar_stepPlus
  · show fm ⟨(2 * n + 2) + 1, 0, 0, 0 + (n + 1), 0⟩ = some ⟨2 * n + 2, 1, 1, 0 + (n + 1), 1⟩
    simp [fm]
  -- State: (2n+2, 1, 1, n+1, 1)
  -- Phase 3: R1+R3 interleave, n rounds
  show ⟨2 * n + 2, 1, 1, 0 + (n + 1), 1⟩ [fm]⊢* ⟨2 * n + 5, 0, 0, 0, n + 2⟩
  rw [show 2 * n + 2 = (n + 2) + n from by ring,
      show (0 : ℕ) + (n + 1) = 1 + n from by ring]
  apply stepStar_trans (r1r3_chain n (a := n + 2) (b := 1) (d := 1) (e := 1))
  -- State: (n+2, 1+n, 1, 1, 1+n)
  -- Final R1: c=1, d=1
  rw [show (1 : ℕ) + n = n + 1 from by ring]
  step fm
  -- State: (n+2, n+3, 0, 0, n+2)
  -- Phase 4: R3+R2 drain
  rw [show n + 2 = (n + 1) + 1 from by ring,
      show n + 3 = 0 + (n + 3) from by ring]
  apply stepStar_trans (r3r2_drain (n + 3) (a := n + 1) (b := 0) (e := n + 2))
  ring_nf; finish

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨3, 0, 0, 0, 1⟩) (by execute fm 4)
  apply progress_nonhalt_simple (fm := fm) (A := ℕ)
    (fun n ↦ ⟨2 * n + 3, 0, 0, 0, n + 1⟩) 0
  intro n; exists n + 1; exact main_trans
