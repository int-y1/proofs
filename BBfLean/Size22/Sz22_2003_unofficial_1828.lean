import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #1828: [9/10, 55/21, 8/3, 7/11, 33/2]

Vector representation:
```
-1  2 -1  0  0
 0 -1  1 -1  1
 3 -1  0  0  0
 0  0  0  1 -1
-1  1  0  0  1
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_1828

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a+1, b, c+1, d, e⟩ => some ⟨a, b+2, c, d, e⟩
  | ⟨a, b+1, c, d+1, e⟩ => some ⟨a, b, c+1, d, e+1⟩
  | ⟨a, b+1, c, d, e⟩ => some ⟨a+3, b, c, d, e⟩
  | ⟨a, b, c, d, e+1⟩ => some ⟨a, b, c, d+1, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b+1, c, d, e+1⟩
  | _ => none

-- R4 repeated: move e to d.
theorem e_to_d : ∀ k, ⟨a, 0, 0, d, e + k⟩ [fm]⊢* ⟨a, 0, 0, d + k, e⟩ := by
  intro k; induction' k with k ih generalizing d e
  · exists 0
  · rw [show e + (k + 1) = (e + k) + 1 from by ring]
    step fm
    apply stepStar_trans (ih (d := d + 1))
    ring_nf; finish

-- R3 repeated: convert b to a (multiply by 3).
theorem r3_drain : ∀ k, ⟨a, b + k, 0, 0, e⟩ [fm]⊢* ⟨a + 3 * k, b, 0, 0, e⟩ := by
  intro k; induction' k with k ih generalizing a b
  · exists 0
  · rw [show b + (k + 1) = (b + k) + 1 from by ring]
    step fm
    apply stepStar_trans (ih (a := a + 3))
    ring_nf; finish

-- R2-R1 spiral: k rounds of R2+R1.
theorem spiral : ∀ k, ⟨a + k, b + 1, 0, k, b + 1⟩ [fm]⊢* ⟨a, b + k + 1, 0, 0, b + k + 1⟩ := by
  intro k; induction' k with k ih generalizing a b
  · exists 0
  · rw [show a + (k + 1) = (a + k) + 1 from by ring,
        show (k + 1 : ℕ) = k + 1 from rfl]
    step fm
    step fm
    rw [show b + 1 + 1 = (b + 1) + 1 from by ring]
    apply stepStar_trans (ih (a := a) (b := b + 1))
    ring_nf; finish

-- Compose: R3 drain then e_to_d.
theorem r3_then_e2d (N : ℕ) :
    ⟨N * N + 2 * N + 1, N + 2, 0, 0, N + 2⟩ [fm]⊢*
    ⟨N * N + 5 * N + 7, 0, 0, N + 2, 0⟩ := by
  rw [show (N + 2 : ℕ) = 0 + (N + 2) from by omega]
  apply stepStar_trans (r3_drain (N + 2) (a := N * N + 2 * N + 1) (b := 0) (e := 0 + (N + 2)))
  rw [show N * N + 2 * N + 1 + 3 * (N + 2) = N * N + 5 * N + 7 from by ring]
  apply stepStar_trans (e_to_d (N + 2) (a := N * N + 5 * N + 7) (d := 0) (e := 0))
  ring_nf; finish

-- Main transition: C(N) = (N*N+3*N+3, 0, 0, N+1, 0) to C(N+1)
theorem main_trans (N : ℕ) :
    ⟨N * N + 3 * N + 3, 0, 0, N + 1, 0⟩ [fm]⊢⁺
    ⟨N * N + 5 * N + 7, 0, 0, N + 2, 0⟩ := by
  rw [show N * N + 3 * N + 3 = (N * N + 3 * N + 2) + 1 from by ring]
  step fm
  rw [show N * N + 3 * N + 2 = (N * N + 2 * N + 1) + (N + 1) from by ring,
      show (1 : ℕ) = 0 + 1 from by ring]
  apply stepStar_trans (spiral (N + 1) (a := N * N + 2 * N + 1) (b := 0))
  rw [show 0 + (N + 1) + 1 = N + 2 from by ring]
  exact r3_then_e2d N

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨3, 0, 0, 1, 0⟩) (by execute fm 3)
  apply progress_nonhalt_simple (fm := fm) (A := ℕ)
    (fun N ↦ ⟨N * N + 3 * N + 3, 0, 0, N + 1, 0⟩) 0
  intro N; refine ⟨N + 1, ?_⟩
  show ⟨N * N + 3 * N + 3, 0, 0, N + 1, 0⟩ [fm]⊢⁺
    ⟨(N + 1) * (N + 1) + 3 * (N + 1) + 3, 0, 0, (N + 1) + 1, 0⟩
  rw [show (N + 1) * (N + 1) + 3 * (N + 1) + 3 = N * N + 5 * N + 7 from by ring,
      show (N + 1) + 1 = N + 2 from by ring]
  exact main_trans N
