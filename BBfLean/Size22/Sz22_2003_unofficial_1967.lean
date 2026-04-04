import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #1967: [99/35, 12/5, 25/22, 7/3, 5/2]

Vector representation:
```
 0  2 -1 -1  1
 2  1 -1  0  0
-1  0  2  0 -1
 0 -1  0  1  0
-1  0  1  0  0
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_1967

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a, b, c+1, d+1, e⟩ => some ⟨a, b+2, c, d, e+1⟩
  | ⟨a, b, c+1, d, e⟩ => some ⟨a+2, b+1, c, d, e⟩
  | ⟨a+1, b, c, d, e+1⟩ => some ⟨a, b, c+2, d, e⟩
  | ⟨a, b+1, c, d, e⟩ => some ⟨a, b, c, d+1, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b, c+1, d, e⟩
  | _ => none

theorem b_to_d : ∀ k, ⟨a, b + k, 0, d, 0⟩ [fm]⊢* ⟨a, b, 0, d + k, 0⟩ := by
  intro k; induction' k with k ih generalizing a b d
  · exists 0
  · rw [show b + (k + 1) = (b + k) + 1 from by ring]
    step fm
    apply stepStar_trans (ih (b := b) (d := d + 1))
    ring_nf; finish

theorem unwind : ∀ E, ∀ A B, ⟨A + 1, B, 0, 0, E⟩ [fm]⊢* ⟨A + 3 * E + 1, B + 2 * E, 0, 0, 0⟩ := by
  intro E; induction' E with E ih <;> intro A B
  · exists 0
  · step fm; step fm; step fm
    show ⟨A + 2 + 2, B + 1 + 1, 0, 0, E⟩ [fm]⊢* _
    rw [show A + 2 + 2 = (A + 3) + 1 from by ring,
        show B + 1 + 1 = B + 2 from by ring,
        show A + 3 * (E + 1) + 1 = (A + 3) + 3 * E + 1 from by ring,
        show B + 2 * (E + 1) = (B + 2) + 2 * E from by ring]
    exact ih (A + 3) (B + 2)

theorem core : ∀ D, ∀ A B E, 2 * A + 1 ≥ D →
    ⟨A, B, 2, D, E⟩ [fm]⊢* ⟨A + D + 3 * E + 4, B + 3 * D + 2 * E + 2, 0, 0, 0⟩ := by
  intro D; induction' D using Nat.strongRecOn with D ih; intro A B E hA
  rcases D with _ | _ | D
  · -- D = 0: R2, R2 -> (A+4, B+2, 0, 0, E) -> unwind
    step fm; step fm
    show ⟨A + 2 + 2, B + 1 + 1, 0, 0, E⟩ [fm]⊢* _
    rw [show A + 2 + 2 = (A + 3) + 1 from by ring,
        show B + 1 + 1 = B + 2 from by ring,
        show A + 0 + 3 * E + 4 = (A + 3) + 3 * E + 1 from by ring,
        show B + 3 * 0 + 2 * E + 2 = (B + 2) + 2 * E from by ring]
    exact unwind E (A + 3) (B + 2)
  · -- D = 1: R1, R2 -> (A+2, B+3, 0, 0, E+1) -> unwind
    step fm; step fm
    show ⟨A + 2, B + 2 + 1, 0, 0, E + 1⟩ [fm]⊢* _
    rw [show A + 2 = (A + 1) + 1 from by ring,
        show B + 2 + 1 = B + 3 from by ring,
        show A + 1 + 3 * E + 4 = (A + 1) + 3 * (E + 1) + 1 from by ring,
        show B + 3 * 1 + 2 * E + 2 = (B + 3) + 2 * (E + 1) from by ring]
    exact unwind (E + 1) (A + 1) (B + 3)
  · -- D + 2: R1, R1 -> (A, B+4, 0, D, E+2) -> R3 -> (A-1, B+4, 2, D, E+1) -> IH
    step fm; step fm
    -- State: (A, B+4, 0, D, E+2). R3 needs A >= 1 and E+2 >= 1.
    show ⟨A, B + 2 + 2, 0, D, E + 1 + 1⟩ [fm]⊢* _
    rw [show B + 2 + 2 = B + 4 from by ring,
        show E + 1 + 1 = E + 2 from by ring,
        show A = (A - 1) + 1 from by omega,
        show E + 2 = (E + 1) + 1 from by ring]
    step fm
    show ⟨A - 1, B + 4, 0 + 2, D, E + 1⟩ [fm]⊢*
         ⟨A - 1 + 1 + (D + 1 + 1) + 3 * E + 4, B + 3 * (D + 1 + 1) + 2 * E + 2, 0, 0, 0⟩
    rw [show (0 : ℕ) + 2 = 2 from by ring,
        show A - 1 + 1 + (D + 1 + 1) + 3 * E + 4 = (A - 1) + D + 3 * (E + 1) + 4 from by omega,
        show B + 3 * (D + 1 + 1) + 2 * E + 2 = (B + 4) + 3 * D + 2 * (E + 1) + 2 from by ring]
    exact ih D (by omega) (A - 1) (B + 4) (E + 1) (by omega)

theorem main_trans : ∀ d a, 2 * a ≥ d + 2 →
    ⟨a, 0, 0, d, 0⟩ [fm]⊢⁺ ⟨a + d + 1, 0, 0, 3 * d + 1, 0⟩ := by
  intro d a ha
  rcases d with _ | d
  · -- d = 0
    obtain ⟨A, rfl⟩ : ∃ A, a = A + 1 := ⟨a - 1, by omega⟩
    execute fm 3
  · -- d + 1
    obtain ⟨A, rfl⟩ : ∃ A, a = A + 1 := ⟨a - 1, by omega⟩
    -- R5, R1, R3: (A+1, 0, 0, d+1, 0) -> (A, 0, 1, d+1, 0) -> (A, 2, 0, d, 1) -> (A-1, 2, 2, d, 0)
    step fm; step fm
    -- State: (A, 2, 0, d, 1). Need R3: A >= 1 and 1 >= 1.
    rw [show A = (A - 1) + 1 from by omega]
    step fm
    -- After R3: state is (A - 1, 2, 2, d, 0)
    show ⟨A - 1, 2, 0 + 2, d, 0⟩ [fm]⊢*
         ⟨A - 1 + 1 + 1 + (d + 1) + 1, 0, 0, 3 * (d + 1) + 1, 0⟩
    rw [show (0 : ℕ) + 2 = 2 from by ring]
    have hcore : 2 * (A - 1) + 1 ≥ d := by omega
    apply stepStar_trans (core d (A - 1) 2 0 hcore)
    rw [show A - 1 + d + 3 * 0 + 4 = A + d + 3 from by omega,
        show 2 + 3 * d + 2 * 0 + 2 = 3 * d + 4 from by ring,
        show A - 1 + 1 + 1 + (d + 1) + 1 = A + d + 3 from by omega,
        show 3 * (d + 1) + 1 = 3 * d + 4 from by ring,
        show 3 * d + 4 = 0 + (3 * d + 4) from by ring]
    exact b_to_d (3 * d + 4) (a := A + d + 3) (b := 0) (d := 0)

theorem nonhalt : ¬halts fm c₀ := by
  apply progress_nonhalt (fm := fm)
    (P := fun q ↦ ∃ a d, q = ⟨a, 0, 0, d, 0⟩ ∧ 2 * a ≥ d + 2)
  · intro c ⟨a, d, hq, ha⟩; subst hq
    exact ⟨⟨a + d + 1, 0, 0, 3 * d + 1, 0⟩,
      ⟨a + d + 1, 3 * d + 1, rfl, by omega⟩,
      main_trans d a ha⟩
  · exact ⟨1, 0, rfl, by omega⟩
