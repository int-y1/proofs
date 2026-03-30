import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #969: [4/15, 33/14, 5/2, 7/11, 56/5]

Vector representation:
```
 2 -1 -1  0  0
-1  1  0 -1  1
-1  0  1  0  0
 0  0  0  1 -1
 3  0 -1  1  0
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_969

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a, b+1, c+1, d, e⟩ => some ⟨a+2, b, c, d, e⟩
  | ⟨a+1, b, c, d+1, e⟩ => some ⟨a, b+1, c, d, e+1⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b, c+1, d, e⟩
  | ⟨a, b, c, d, e+1⟩ => some ⟨a, b, c, d+1, e⟩
  | ⟨a, b, c+1, d, e⟩ => some ⟨a+3, b, c, d+1, e⟩
  | _ => none

theorem a_to_c : ∀ k, ⟨a + k, 0, c, 0, e⟩ [fm]⊢* ⟨a, 0, c + k, 0, e⟩ := by
  intro k; induction' k with k ih generalizing a c
  · exists 0
  · rw [Nat.add_succ a k]
    step fm
    apply stepStar_trans (ih (a := a) (c := c + 1))
    ring_nf; finish

theorem e_to_d : ∀ k, ∀ d, ⟨0, 0, c, d, k⟩ [fm]⊢* ⟨0, 0, c, d + k, 0⟩ := by
  intro k; induction' k with k ih <;> intro d
  · exists 0
  · step fm
    apply stepStar_trans (ih (d + 1))
    ring_nf; finish

theorem r2r1_chain : ∀ k a e c₁, ⟨a + 1, 0, c₁ + k, k, e⟩ [fm]⊢* ⟨a + k + 1, 0, c₁, 0, e + k⟩ := by
  intro k; induction' k with k ih <;> intro a e c₁
  · exists 0
  · step fm
    step fm
    rw [show a + 2 = (a + 1) + 1 from by ring]
    apply stepStar_trans (ih (a + 1) (e + 1) c₁)
    ring_nf; finish

theorem main_trans : ⟨n + 5, 0, n, 0, n + 2⟩ [fm]⊢⁺ ⟨n + 6, 0, n + 1, 0, n + 3⟩ := by
  -- Phase 1: R3 x(n+5)
  apply stepStar_stepPlus_stepPlus
  · rw [show n + 5 = 0 + (n + 5) from by ring]
    exact a_to_c (n + 5) (a := 0) (c := n) (e := n + 2)
  -- Phase 2: R4 x(n+2)
  apply stepStar_stepPlus_stepPlus
  · apply stepStar_trans (e_to_d (n + 2) (c := n + (n + 5)) 0)
    ring_nf; finish
  -- Phase 3: R5 step
  apply step_stepStar_stepPlus
  · rw [show 5 + n * 2 = (4 + n * 2) + 1 from by ring]
    show fm ⟨0, 0, (4 + n * 2) + 1, 2 + n, 0⟩ = some ⟨3, 0, 4 + n * 2, 2 + n + 1, 0⟩
    simp [fm]
  -- Phase 4: R2/R1 x(n+3)
  · rw [show (3 : ℕ) = 2 + 1 from by ring,
        show 4 + n * 2 = (n + 1) + (n + 3) from by ring,
        show 2 + n + 1 = n + 3 from by ring]
    apply stepStar_trans (r2r1_chain (n + 3) 2 0 (n + 1))
    ring_nf; finish

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨5, 0, 0, 0, 2⟩) (by execute fm 14)
  apply progress_nonhalt_simple (fm := fm) (A := ℕ)
    (fun n ↦ ⟨n + 5, 0, n, 0, n + 2⟩) 0
  intro n; exists n + 1; exact main_trans
