import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #2001: [99/35, 8/5, 5/6, 7/11, 55/2]

Vector representation:
```
 0  2 -1 -1  1
 3  0 -1  0  0
-1 -1  1  0  0
 0  0  0  1 -1
-1  0  1  0  1
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_2001

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a, b, c+1, d+1, e⟩ => some ⟨a, b+2, c, d, e+1⟩
  | ⟨a, b, c+1, d, e⟩ => some ⟨a+3, b, c, d, e⟩
  | ⟨a+1, b+1, c, d, e⟩ => some ⟨a, b, c+1, d, e⟩
  | ⟨a, b, c, d, e+1⟩ => some ⟨a, b, c, d+1, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b, c+1, d, e+1⟩
  | _ => none

theorem e_to_d : ∀ k d, ⟨a, 0, 0, d, k⟩ [fm]⊢* ⟨a, 0, 0, d + k, 0⟩ := by
  intro k; induction k generalizing a with
  | zero => intro d; exists 0
  | succ k ih =>
    intro d; step fm
    apply stepStar_trans (ih (a := a) (d + 1))
    rw [show d + 1 + k = d + (k + 1) from by ring]
    finish

theorem r1_r3_loop : ∀ k, ∀ A B E, ⟨A + k, B, 1, k + 1, E⟩ [fm]⊢* ⟨A, B + k + 2, 0, 0, E + k + 1⟩ := by
  intro k; induction k with
  | zero =>
    intro A B E
    step fm
    ring_nf; finish
  | succ k ih =>
    intro A B E
    rw [show A + (k + 1) = (A + k) + 1 from by ring,
        show (k + 1) + 1 = k + 1 + 1 from by ring]
    step fm
    step fm
    apply stepStar_trans (ih A (B + 1) (E + 1))
    ring_nf; finish

theorem r2_r3_drain : ∀ k, ∀ A E, ⟨A, k, 1, 0, E⟩ [fm]⊢* ⟨A + 2 * k + 3, 0, 0, 0, E⟩ := by
  intro k; induction k with
  | zero =>
    intro A E
    step fm
    ring_nf; finish
  | succ k ih =>
    intro A E
    step fm
    step fm
    apply stepStar_trans (ih (A + 2) E)
    ring_nf; finish

theorem main_trans : ∀ a n, ⟨a + n + 2, 0, 0, 0, n + 1⟩ [fm]⊢⁺ ⟨a + 2 * n + 5, 0, 0, 0, n + 2⟩ := by
  intro a n
  -- Phase 1: e to d
  apply stepStar_stepPlus_stepPlus
  · rw [show (0 : ℕ) = 0 from rfl]
    apply stepStar_trans (e_to_d (n + 1) 0 (a := a + n + 2))
    ring_nf; finish
  -- Phase 2: R5
  rw [show 2 + a + n = (a + n + 1) + 1 from by ring,
      show 1 + n = n + 1 from by ring]
  step fm
  -- Phase 3: R1+R3 loop
  rw [show a + n + 1 = (a + 1) + n from by ring]
  apply stepStar_trans (r1_r3_loop n (a + 1) 0 1)
  -- Phase 4: R3 + Phase 5: drain
  rw [show 0 + n + 2 = n + 2 from by ring,
      show 1 + n + 1 = n + 2 from by ring]
  step fm
  apply stepStar_trans (r2_r3_drain (n + 1) a (n + 2))
  ring_nf; finish

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨3, 0, 0, 0, 1⟩) (by execute fm 2)
  apply progress_nonhalt_simple (fm := fm) (A := ℕ × ℕ)
    (fun ⟨a, n⟩ ↦ ⟨a + n + 2, 0, 0, 0, n + 1⟩) ⟨1, 0⟩
  intro ⟨a, n⟩
  refine ⟨⟨a + n + 2, n + 1⟩, ?_⟩
  show ⟨a + n + 2, 0, 0, 0, n + 1⟩ [fm]⊢⁺ ⟨a + n + 2 + (n + 1) + 2, 0, 0, 0, n + 1 + 1⟩
  rw [show a + n + 2 + (n + 1) + 2 = a + 2 * n + 5 from by ring,
      show n + 1 + 1 = n + 2 from by ring]
  exact main_trans a n
