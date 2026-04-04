import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #1824: [9/10, 55/21, 44/3, 7/11, 3/2]

Vector representation:
```
-1  2 -1  0  0
 0 -1  1 -1  1
 2 -1  0  0  1
 0  0  0  1 -1
-1  1  0  0  0
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_1824

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a+1, b, c+1, d, e⟩ => some ⟨a, b+2, c, d, e⟩
  | ⟨a, b+1, c, d+1, e⟩ => some ⟨a, b, c+1, d, e+1⟩
  | ⟨a, b+1, c, d, e⟩ => some ⟨a+2, b, c, d, e+1⟩
  | ⟨a, b, c, d, e+1⟩ => some ⟨a, b, c, d+1, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b+1, c, d, e⟩
  | _ => none

-- R4 chain: transfer e to d
theorem e_to_d : ∀ k, ⟨a, 0, 0, d, e + k⟩ [fm]⊢* ⟨a, 0, 0, d + k, e⟩ := by
  intro k; induction' k with k ih generalizing a d e
  · exists 0
  · rw [show e + (k + 1) = (e + k) + 1 from by ring]
    step fm
    rw [show d + 1 = (d + 1) from rfl]
    apply stepStar_trans (ih (d := d + 1))
    ring_nf; finish

-- R2+R1 loop: k rounds of R2 then R1
theorem r2r1_loop : ∀ k, ⟨k, b + 1, 0, k, e⟩ [fm]⊢* ⟨0, b + k + 1, 0, 0, e + k⟩ := by
  intro k; induction' k with k ih generalizing b e
  · exists 0
  · step fm
    step fm
    apply stepStar_trans (ih (b := b + 1) (e := e + 1))
    ring_nf; finish

-- R3 chain: drain b when d=0
theorem r3_chain : ∀ k, ⟨a, b + k, 0, 0, e⟩ [fm]⊢* ⟨a + 2 * k, b, 0, 0, e + k⟩ := by
  intro k; induction' k with k ih generalizing a b e
  · exists 0
  · rw [show b + (k + 1) = (b + k) + 1 from by ring]
    step fm
    apply stepStar_trans (ih (a := a + 2) (b := b))
    ring_nf; finish

-- R5 then R2+R1 loop then R3 chain
theorem spiral : ⟨d + 1, 0, 0, d, 0⟩ [fm]⊢⁺ ⟨2 * d + 2, 0, 0, 0, 2 * d + 1⟩ := by
  step fm
  apply stepStar_trans (r2r1_loop d (b := 0) (e := 0))
  rw [show 0 + d + 1 = 0 + (d + 1) from by ring,
      show (0 : ℕ) + d = d from by ring]
  apply stepStar_trans (r3_chain (d + 1) (a := 0) (b := 0) (e := d))
  ring_nf; finish

-- Compose spiral with e_to_d
theorem main_trans : ⟨n + 1, 0, 0, n, 0⟩ [fm]⊢⁺ ⟨2 * n + 2, 0, 0, 2 * n + 1, 0⟩ := by
  apply stepPlus_stepStar_stepPlus spiral
  rw [show (0 : ℕ) = 0 + 0 from by ring,
      show 2 * n + 1 = 0 + (2 * n + 1) from by ring]
  apply stepStar_trans (e_to_d (2 * n + 1) (a := 2 * n + 2) (d := 0) (e := 0))
  ring_nf; finish

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨2, 0, 0, 1, 0⟩) (by execute fm 3)
  apply progress_nonhalt_simple (fm := fm) (A := ℕ)
    (fun n ↦ ⟨n + 2, 0, 0, n + 1, 0⟩) 0
  intro n; exists 2 * n + 2
  show ⟨n + 2, 0, 0, n + 1, 0⟩ [fm]⊢⁺ ⟨2 * n + 2 + 2, 0, 0, 2 * n + 2 + 1, 0⟩
  have h := @main_trans (n + 1)
  rw [show n + 1 + 1 = n + 2 from by ring,
      show 2 * (n + 1) + 2 = 2 * n + 2 + 2 from by ring,
      show 2 * (n + 1) + 1 = 2 * n + 2 + 1 from by ring] at h
  exact h

end Sz22_2003_unofficial_1824
