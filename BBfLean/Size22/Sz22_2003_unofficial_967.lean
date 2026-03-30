import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #967: [4/15, 33/14, 5/2, 7/11, 44/5]

Vector representation:
```
 2 -1 -1  0  0
-1  1  0 -1  1
-1  0  1  0  0
 0  0  0  1 -1
 2  0 -1  0  1
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_967

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a, b+1, c+1, d, e⟩ => some ⟨a+2, b, c, d, e⟩
  | ⟨a+1, b, c, d+1, e⟩ => some ⟨a, b+1, c, d, e+1⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b, c+1, d, e⟩
  | ⟨a, b, c, d, e+1⟩ => some ⟨a, b, c, d+1, e⟩
  | ⟨a, b, c+1, d, e⟩ => some ⟨a+2, b, c, d, e+1⟩
  | _ => none

-- R3 chain: (a+k, 0, c, 0, e) →* (a, 0, c+k, 0, e)
theorem a_to_c : ∀ k, ⟨a + k, 0, c, 0, e⟩ [fm]⊢* ⟨a, 0, c + k, 0, e⟩ := by
  intro k; induction' k with k ih generalizing a c
  · exists 0
  · rw [Nat.add_succ a k]
    step fm
    apply stepStar_trans (ih (a := a) (c := c + 1))
    ring_nf; finish

-- R4 chain: (0, 0, c, d, k) →* (0, 0, c, d+k, 0)
theorem e_to_d : ∀ k, ∀ d, ⟨0, 0, c, d, k⟩ [fm]⊢* ⟨0, 0, c, d + k, 0⟩ := by
  intro k; induction' k with k ih <;> intro d
  · exists 0
  · step fm
    apply stepStar_trans (ih (d + 1))
    ring_nf; finish

-- R2+R1 chain: (a+2, 0, k, k, e) →* (a+k+2, 0, 0, 0, e+k)
theorem r2r1_chain : ∀ k, ⟨a + 2, 0, k, k, e⟩ [fm]⊢* ⟨a + k + 2, 0, 0, 0, e + k⟩ := by
  intro k; induction' k with k ih generalizing a e
  · exists 0
  · step fm
    step fm
    rw [show a + 3 = (a + 1) + 2 from by ring]
    apply stepStar_trans (ih (a := a + 1) (e := e + 1))
    ring_nf; finish

-- Main transition: (n+1, 0, 0, 0, n) →⁺ (n+2, 0, 0, 0, n+1)
theorem main_trans : ⟨n + 1, 0, 0, 0, n⟩ [fm]⊢⁺ ⟨n + 2, 0, 0, 0, n + 1⟩ := by
  -- Phase 1: R3 x (n+1)
  apply stepStar_stepPlus_stepPlus
  · rw [show n + 1 = 0 + (n + 1) from by ring]
    exact a_to_c (n + 1) (a := 0) (c := 0) (e := n)
  -- Phase 2: R4 x n
  apply stepStar_stepPlus_stepPlus
  · rw [show 0 + (n + 1) = n + 1 from by ring]
    apply stepStar_trans (e_to_d n (c := n + 1) 0)
    rw [show 0 + n = n from by ring]; finish
  -- Phase 3: R5
  apply step_stepStar_stepPlus
  · show fm ⟨0, 0, n + 1, n, 0⟩ = some ⟨2, 0, n, n, 1⟩
    simp [fm]
  -- Phase 4: R2+R1 x n
  · rw [show (2 : ℕ) = 0 + 2 from by ring]
    apply stepStar_trans (r2r1_chain n (a := 0) (e := 1))
    ring_nf; finish

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨3, 0, 0, 0, 2⟩) (by execute fm 8)
  apply progress_nonhalt_simple (fm := fm) (A := ℕ)
    (fun n ↦ ⟨n + 1, 0, 0, 0, n⟩) 2
  intro n; exists n + 1; exact main_trans
