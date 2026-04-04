import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #1978: [99/35, 25/6, 4/5, 7/11, 55/2]

Vector representation:
```
 0  2 -1 -1  1
-1 -1  2  0  0
 2  0 -1  0  0
 0  0  0  1 -1
-1  0  1  0  1
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_1978

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a, b, c+1, d+1, e⟩ => some ⟨a, b+2, c, d, e+1⟩
  | ⟨a+1, b+1, c, d, e⟩ => some ⟨a, b, c+2, d, e⟩
  | ⟨a, b, c+1, d, e⟩ => some ⟨a+2, b, c, d, e⟩
  | ⟨a, b, c, d, e+1⟩ => some ⟨a, b, c, d+1, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b, c+1, d, e+1⟩
  | _ => none

theorem e_to_d : ∀ e, ⟨a, 0, 0, d, e⟩ [fm]⊢* ⟨a, 0, 0, d + e, 0⟩ := by
  intro e; induction' e with e ih generalizing d
  · exists 0
  · rw [show d + (e + 1) = (d + 1) + e from by ring]
    step fm
    exact ih (d := d + 1)

theorem c_to_a : ∀ k, ⟨a, 0, k, 0, e⟩ [fm]⊢* ⟨a + 2 * k, 0, 0, 0, e⟩ := by
  intro k; induction' k with k ih generalizing a
  · exists 0
  · step fm
    apply stepStar_trans (ih (a := a + 2))
    ring_nf; finish

theorem r2_drain : ∀ k, ⟨a + k, k, c, 0, e⟩ [fm]⊢* ⟨a, 0, c + 2 * k, 0, e⟩ := by
  intro k; induction' k with k ih generalizing a c
  · exists 0
  · rw [show a + (k + 1) = (a + k) + 1 from by ring]
    step fm
    apply stepStar_trans (ih (a := a) (c := c + 2))
    ring_nf; finish

theorem spiral_rounds : ∀ k, ⟨a + k, b + 1, 0, d + 2 * k, e⟩ [fm]⊢*
    ⟨a, b + 1 + 3 * k, 0, d, e + 2 * k⟩ := by
  intro k; induction' k with k ih generalizing a b d e
  · exists 0
  · rw [show a + (k + 1) = (a + k) + 1 from by ring,
        show d + 2 * (k + 1) = (d + 2 * k) + 1 + 1 from by ring]
    step fm
    step fm
    step fm
    rw [show b + 1 + 3 * (k + 1) = (b + 3) + 1 + 3 * k from by ring,
        show e + 2 * (k + 1) = (e + 2) + 2 * k from by ring]
    exact ih (a := a) (b := b + 3) (d := d) (e := e + 2)

theorem middle_gen : ∀ D, ∀ A B E,
    ⟨A + B + 1 + 2 * D, B + 1, 0, D, E⟩ [fm]⊢* ⟨A, 0, 2 * B + 2 + 3 * D, 0, E + D⟩ := by
  intro D; induction' D using Nat.strongRecOn with D ih; intro A B E
  rcases D with _ | _ | D
  · rw [show A + B + 1 + 2 * 0 = A + (B + 1) from by ring,
        show 2 * B + 2 + 3 * 0 = 0 + 2 * (B + 1) from by ring,
        show E + 0 = E from by ring]
    exact r2_drain (B + 1) (a := A) (c := 0) (e := E)
  · rw [show A + B + 1 + 2 * 1 = (A + B + 2) + 1 from by ring,
        show 2 * B + 2 + 3 * 1 = 1 + 2 * (B + 2) from by ring]
    step fm
    step fm
    show ⟨A + B + 2, B + 2, 1, 0, E + 1⟩ [fm]⊢* ⟨A, 0, 1 + 2 * (B + 2), 0, E + 1⟩
    exact r2_drain (B + 2) (a := A) (c := 1) (e := E + 1)
  · rw [show A + B + 1 + 2 * (D + 2) = (A + (B + 3) + 1 + 2 * D) + 1 from by ring,
        show D + 2 = D + 1 + 1 from by ring]
    step fm
    step fm
    step fm
    rw [show 2 * B + 2 + 3 * (D + 2) = 2 * (B + 3) + 2 + 3 * D from by ring,
        show E + (D + 2) = (E + 2) + D from by ring]
    show ⟨A + (B + 3) + 1 + 2 * D, (B + 3) + 1, 0, D, E + 2⟩ [fm]⊢*
         ⟨A, 0, 2 * (B + 3) + 2 + 3 * D, 0, (E + 2) + D⟩
    exact ih D (by omega) A (B + 3) (E + 2)

theorem main_trans : ∀ n,
    ⟨2 * n ^ 2 + 7 * n + 7, 0, 0, 0, n + 2⟩ [fm]⊢⁺
    ⟨2 * n ^ 2 + 11 * n + 16, 0, 0, 0, n + 3⟩ := by
  intro n
  apply stepStar_stepPlus_stepPlus (c₂ := ⟨2 * n ^ 2 + 7 * n + 7, 0, 0, n + 2, 0⟩)
  · apply stepStar_trans (e_to_d (n + 2) (a := 2 * n ^ 2 + 7 * n + 7) (d := 0))
    ring_nf; finish
  · rw [show 2 * n ^ 2 + 7 * n + 7 = (2 * n ^ 2 + 7 * n + 6) + 1 from by ring]
    apply step_stepStar_stepPlus
    · show fm ⟨(2 * n ^ 2 + 7 * n + 6) + 1, 0, 0, n + 2, 0⟩ =
          some ⟨2 * n ^ 2 + 7 * n + 6, 0, 1, n + 2, 1⟩
      rfl
    · rw [show n + 2 = (n + 1) + 1 from by ring]
      step fm
      show ⟨2 * n ^ 2 + 7 * n + 6, 2, 0, n + 1, 2⟩ [fm]⊢*
           ⟨2 * n ^ 2 + 11 * n + 16, 0, 0, 0, n + 3⟩
      rw [show (2 : ℕ) = 1 + 1 from by ring,
          show 2 * n ^ 2 + 7 * n + 6 = (2 * n ^ 2 + 5 * n + 2) + 1 + 1 + 2 * (n + 1) from by ring]
      apply stepStar_trans (middle_gen (n + 1) (2 * n ^ 2 + 5 * n + 2) 1 2)
      rw [show 2 * 1 + 2 + 3 * (n + 1) = 3 * n + 7 from by ring,
          show 2 + (n + 1) = n + 3 from by ring]
      apply stepStar_trans (c_to_a (3 * n + 7) (a := 2 * n ^ 2 + 5 * n + 2) (e := n + 3))
      ring_nf; finish

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨7, 0, 0, 0, 2⟩) (by execute fm 11)
  show ¬halts fm (2 * 0 ^ 2 + 7 * 0 + 7, 0, 0, 0, 0 + 2)
  apply progress_nonhalt_simple (fm := fm) (A := ℕ)
    (fun n ↦ ⟨2 * n ^ 2 + 7 * n + 7, 0, 0, 0, n + 2⟩) 0
  intro n
  refine ⟨n + 1, ?_⟩
  show ⟨2 * n ^ 2 + 7 * n + 7, 0, 0, 0, n + 2⟩ [fm]⊢⁺
       ⟨2 * (n + 1) ^ 2 + 7 * (n + 1) + 7, 0, 0, 0, (n + 1) + 2⟩
  rw [show 2 * (n + 1) ^ 2 + 7 * (n + 1) + 7 = 2 * n ^ 2 + 11 * n + 16 from by ring,
      show (n + 1) + 2 = n + 3 from by ring]
  exact main_trans n
