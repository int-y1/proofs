import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #388: [2/15, 99/14, 25/2, 7/11, 66/5]

Vector representation:
```
 1 -1 -1  0  0
-1  2  0 -1  1
-1  0  2  0  0
 0  0  0  1 -1
 1  1 -1  0  1
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_388

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a, b+1, c+1, d, e⟩ => some ⟨a+1, b, c, d, e⟩
  | ⟨a+1, b, c, d+1, e⟩ => some ⟨a, b+2, c, d, e+1⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b, c+2, d, e⟩
  | ⟨a, b, c, d, e+1⟩ => some ⟨a, b, c, d+1, e⟩
  | ⟨a, b, c+1, d, e⟩ => some ⟨a+1, b+1, c, d, e+1⟩
  | _ => none

-- Rule 3 repeated: decrease a, increase c by 2
theorem a_to_c : ∀ k c, ⟨a+k, 0, c, 0, e⟩ [fm]⊢* ⟨a, 0, c+2*k, 0, e⟩ := by
  intro k; induction k with
  | zero => intro c; exists 0
  | succ k ih =>
    intro c
    rw [show a + (k + 1) = (a + k) + 1 from by ring]
    step fm
    apply stepStar_trans (ih _)
    ring_nf; finish

-- Rule 4 repeated: decrease e, increase d
theorem e_to_d : ∀ k d, ⟨0, 0, c, d, e+k⟩ [fm]⊢* ⟨0, 0, c, d+k, e⟩ := by
  intro k; induction k with
  | zero => intro d; exists 0
  | succ k ih =>
    intro d
    rw [show e + (k + 1) = e + k + 1 from by ring]
    step fm
    apply stepStar_trans (ih _)
    ring_nf; finish

-- Rule 5 + Rule 1: start consuming c
theorem start_consume : ⟨0, 0, c+2, n, 0⟩ [fm]⊢⁺ ⟨2, 0, c, n, 1⟩ := by
  step fm; step fm; finish

-- Inner loop: 3 steps (rule 2, rule 1, rule 1)
theorem inner_loop : ⟨k+2, 0, c+2, d+1, e⟩ [fm]⊢⁺ ⟨k+3, 0, c, d, e+1⟩ := by
  step fm; step fm; step fm
  ring_nf; finish

-- Inner loop repeated
theorem inner_loop_rep : ∀ k e, ⟨k+2, 0, 2*j, j, e⟩ [fm]⊢* ⟨k+j+2, 0, 0, 0, e+j⟩ := by
  induction j with
  | zero => intro k e; simp; exists 0
  | succ j ih =>
    intro k e
    rw [show 2 * (j + 1) = 2 * j + 2 from by ring]
    apply stepStar_trans (stepPlus_stepStar inner_loop)
    rw [show k + 3 = (k + 1) + 2 from by ring]
    apply stepStar_trans (ih (k+1) (e+1))
    ring_nf; finish

-- Phases 1+2: (n+1, 0, 0, 0, n) ->* (0, 0, 2*n+2, n, 0)
theorem phases12 : ⟨n+1, 0, 0, 0, n⟩ [fm]⊢* ⟨0, 0, 2*n+2, n, 0⟩ := by
  have h1 := a_to_c (a := 0) (e := n) (n+1) 0
  simp only [Nat.zero_add] at h1
  apply stepStar_trans h1
  have h2 := e_to_d (c := 0 + 2 * (n + 1)) (e := 0) n 0
  simp only [Nat.zero_add] at h2
  apply stepStar_trans h2
  ring_nf; finish

-- Full cycle: (n+1, 0, 0, 0, n) ⊢⁺ (n+2, 0, 0, 0, n+1)
theorem cycle : ⟨n+1, 0, 0, 0, n⟩ [fm]⊢⁺ ⟨n+2, 0, 0, 0, n+1⟩ := by
  apply stepStar_stepPlus_stepPlus phases12
  rw [show 2 * n + 2 = 2 * n + 2 from rfl]
  apply stepPlus_stepStar_stepPlus (start_consume (c := 2*n) (n := n))
  rw [show (2 : ℕ) = 0 + 2 from by ring]
  apply stepStar_trans (inner_loop_rep (j := n) 0 1)
  ring_nf; finish

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨1, 0, 0, 0, 0⟩)
  · finish
  exact progress_nonhalt_simple (fm := fm) (fun n ↦ ⟨n+1, 0, 0, 0, n⟩) 0
    (fun n ↦ ⟨n+1, cycle⟩)
