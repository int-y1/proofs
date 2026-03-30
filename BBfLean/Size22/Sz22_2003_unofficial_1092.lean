import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #1092: [5/6, 3/385, 28/5, 121/2, 15/11]

Vector representation:
```
-1 -1  1  0  0
 0  1 -1 -1 -1
 2  0 -1  1  0
-1  0  0  0  2
 0  1  1  0 -1
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_1092

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a+1, b+1, c, d, e⟩ => some ⟨a, b, c+1, d, e⟩
  | ⟨a, b, c+1, d+1, e+1⟩ => some ⟨a, b+1, c, d, e⟩
  | ⟨a, b, c+1, d, e⟩ => some ⟨a+2, b, c, d+1, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b, c, d, e+2⟩
  | ⟨a, b, c, d, e+1⟩ => some ⟨a, b+1, c+1, d, e⟩
  | _ => none

-- Phase 1: R4 drain. (k, 0, 0, d, e) →* (0, 0, 0, d, e + 2*k)
theorem r4_drain : ∀ k, ⟨k, 0, 0, d, e⟩ [fm]⊢* ⟨0, 0, 0, d, e + 2 * k⟩ := by
  intro k; induction' k with k ih generalizing d e
  · exists 0
  · step fm
    apply stepStar_trans (ih (e := e + 2))
    ring_nf; finish

-- Phase 2: R5+R2 drain. (0, b, 0, k, e + 2*k) →* (0, b + 2*k, 0, 0, e)
theorem r5r2_drain : ∀ k, ⟨0, b, 0, k, e + 2 * k⟩ [fm]⊢* ⟨0, b + 2 * k, 0, 0, e⟩ := by
  intro k; induction' k with k ih generalizing b e
  · exists 0
  · rw [show e + 2 * (k + 1) = (e + 2 * k) + 2 from by ring]
    rw [show (k : ℕ) + 1 = k + 1 from rfl]
    step fm
    step fm
    apply stepStar_trans (ih (b := b + 2) (e := e))
    ring_nf; finish

-- Phase 3: Bridge. (0, b+2, 0, 0, 2) →* (2, b+2, 0, 1, 0)
theorem bridge : ⟨0, b + 2, 0, 0, 2⟩ [fm]⊢* ⟨2, b + 2, 0, 1, 0⟩ := by
  step fm  -- R5: (0, b+3, 1, 0, 1)
  step fm  -- R3: (2, b+3, 0, 1, 1)
  step fm  -- R1: (1, b+2, 1, 1, 1)
  step fm  -- R1: (0, b+1, 2, 1, 1)
  step fm  -- R2: (0, b+2, 1, 0, 0)
  step fm  -- R3: (2, b+2, 0, 1, 0)
  finish

-- Phase 4: R1,R1,R3 chain. (2, 2*k, c, d, 0) →* (2, 0, c+k, d+k, 0)
theorem r1r1r3_chain : ∀ k, ⟨2, 2 * k, c, d, 0⟩ [fm]⊢* ⟨2, 0, c + k, d + k, 0⟩ := by
  intro k; induction' k with k ih generalizing c d
  · exists 0
  · rw [show 2 * (k + 1) = 2 * k + 2 from by ring]
    step fm  -- R1: (1, 2*k+1, c+1, d, 0)
    step fm  -- R1: (0, 2*k, c+2, d, 0)
    step fm  -- R3: (2, 2*k, c+1, d+1, 0)
    apply stepStar_trans (ih (c := c + 1) (d := d + 1))
    ring_nf; finish

-- Phase 5: R3 chain. (a, 0, k, d, 0) →* (a + 2*k, 0, 0, d + k, 0)
theorem r3_chain : ∀ k, ⟨a, 0, k, d, 0⟩ [fm]⊢* ⟨a + 2 * k, 0, 0, d + k, 0⟩ := by
  intro k; induction' k with k ih generalizing a d
  · exists 0
  · rw [show (k : ℕ) + 1 = k + 1 from rfl]
    step fm  -- R3: (a+2, 0, k, d+1, 0)
    apply stepStar_trans (ih (a := a + 2) (d := d + 1))
    ring_nf; finish

-- Main transition: (n+2, 0, 0, n+1, 0) ⊢⁺ (2*n+4, 0, 0, 2*n+3, 0)
theorem main_trans (n : ℕ) : ⟨n + 2, 0, 0, n + 1, 0⟩ [fm]⊢⁺ ⟨2 * n + 4, 0, 0, 2 * n + 3, 0⟩ := by
  -- First R4 step to establish ⊢⁺
  step fm
  -- Remaining R4 drain
  apply stepStar_trans (r4_drain (n + 1) (d := n + 1) (e := 2))
  -- R5+R2 drain
  apply stepStar_trans (r5r2_drain (n + 1) (b := 0) (e := 2))
  show ⟨0, 0 + 2 * (n + 1), 0, 0, 2⟩ [fm]⊢* ⟨2 * n + 4, 0, 0, 2 * n + 3, 0⟩
  rw [show 0 + 2 * (n + 1) = (n + n) + 2 from by ring]
  -- Bridge
  apply stepStar_trans (bridge (b := n + n))
  -- R1,R1,R3 chain
  rw [show (n + n) + 2 = 2 * (n + 1) from by ring]
  apply stepStar_trans (r1r1r3_chain (n + 1) (c := 0) (d := 1))
  show ⟨2, 0, 0 + (n + 1), 1 + (n + 1), 0⟩ [fm]⊢* ⟨2 * n + 4, 0, 0, 2 * n + 3, 0⟩
  rw [show 0 + (n + 1) = n + 1 from by ring, show 1 + (n + 1) = n + 2 from by ring]
  -- R3 chain
  apply stepStar_trans (r3_chain (n + 1) (a := 2) (d := n + 2))
  ring_nf; finish

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨2, 0, 0, 1, 0⟩) (by execute fm 7)
  apply progress_nonhalt_simple (fm := fm) (A := ℕ)
    (fun n ↦ ⟨n + 2, 0, 0, n + 1, 0⟩) 0
  intro n; exact ⟨2 * n + 2, main_trans n⟩

end Sz22_2003_unofficial_1092
