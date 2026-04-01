import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #1421: [7/15, 18/77, 121/3, 125/2, 3/5]

Vector representation:
```
 0 -1 -1  1  0
 1  2  0 -1 -1
 0 -1  0  0  2
-1  0  3  0  0
 0  1 -1  0  0
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_1421

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a, b+1, c+1, d, e⟩ => some ⟨a, b, c, d+1, e⟩
  | ⟨a, b, c, d+1, e+1⟩ => some ⟨a+1, b+2, c, d, e⟩
  | ⟨a, b+1, c, d, e⟩ => some ⟨a, b, c, d, e+2⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b, c+3, d, e⟩
  | ⟨a, b, c+1, d, e⟩ => some ⟨a, b+1, c, d, e⟩
  | _ => none

theorem r4_chain : ∀ a, ⟨a, 0, c, 0, e⟩ [fm]⊢* ⟨0, 0, c + 3 * a, 0, e⟩ := by
  intro a; induction' a with a ih generalizing c
  · exists 0
  · step fm
    apply stepStar_trans (ih (c := c + 3))
    ring_nf; finish

theorem r3_chain : ∀ k, ⟨a, b + k, 0, 0, e⟩ [fm]⊢* ⟨a, b, 0, 0, e + 2 * k⟩ := by
  intro k; induction' k with k ih generalizing b e
  · exists 0
  · rw [show b + (k + 1) = (b + k) + 1 from by ring]
    step fm
    apply stepStar_trans (ih (b := b) (e := e + 2))
    ring_nf; finish

theorem cycle : ∀ k, ⟨A, 2, C + 2 * k, D, E + k⟩ [fm]⊢* ⟨A + k, 2, C, D + k, E⟩ := by
  intro k; induction' k with k ih generalizing A C D E
  · exists 0
  · rw [show C + 2 * (k + 1) = (C + 2 * k) + 1 + 1 from by ring,
        show E + (k + 1) = (E + k) + 1 from by ring]
    step fm; step fm; step fm
    apply stepStar_trans (ih (A := A + 1) (D := D + 1))
    ring_nf; finish

theorem drain : ∀ D, ⟨A, B + 1, 0, D, E⟩ [fm]⊢* ⟨A + D, 0, 0, 0, E + 3 * D + 2 * B + 2⟩ := by
  intro D; induction' D with D ih generalizing A B E
  · show ⟨A, B + 1, 0, 0, E⟩ [fm]⊢* ⟨A, 0, 0, 0, E + 2 * B + 2⟩
    have h := r3_chain (B + 1) (a := A) (b := 0) (e := E)
    rw [show 0 + (B + 1) = B + 1 from by ring,
        show E + 2 * (B + 1) = E + 2 * B + 2 from by ring] at h
    exact h
  · rcases E with _ | E
    · step fm; step fm
      rw [show B + 2 = (B + 1) + 1 from by ring]
      apply stepStar_trans (ih (A := A + 1) (B := B + 1) (E := 1))
      ring_nf; finish
    · step fm
      rw [show B + 3 = (B + 2) + 1 from by ring]
      apply stepStar_trans (ih (A := A + 1) (B := B + 2) (E := E))
      ring_nf; finish

-- Opening: R5+R1+R2 from (0, 0, C+3, 0, E+1) to (1, 2, C+1, 0, E).
theorem opening : ⟨0, 0, C + 3, 0, E + 1⟩ [fm]⊢⁺ ⟨1, 2, C + 1, 0, E⟩ := by
  step fm; step fm; step fm; finish

-- Even case: a = 2*(j+1), initial e written as E + 3*j + 3.
theorem even_trans (j : ℕ) :
    ⟨2 * j + 2, 0, 0, 0, E + 3 * j + 3⟩ [fm]⊢⁺
    ⟨6 * j + 5, 0, 0, 0, E + 9 * j + 10⟩ := by
  -- Step 1: R4 chain (⊢*) + opening (⊢⁺) = ⊢⁺
  apply stepStar_stepPlus_stepPlus
  · -- R4 chain
    apply stepStar_trans (r4_chain (2 * j + 2) (c := 0) (e := E + 3 * j + 3))
    rw [show 0 + 3 * (2 * j + 2) = (6 * j + 3) + 3 from by ring,
        show E + 3 * j + 3 = (E + 3 * j + 2) + 1 from by ring]
    finish
  -- Now at (0, 0, (6j+3)+3, 0, (E+3j+2)+1). Opening fires.
  apply stepPlus_stepStar_stepPlus (opening (C := 6 * j + 3) (E := E + 3 * j + 2))
  -- After opening: (1, 2, 6j+4, 0, E+3j+2)
  rw [show 6 * j + 3 + 1 = 6 * j + 4 from by ring]
  -- Step 2: Cycle (⊢*)
  rw [show 6 * j + 4 = 0 + 2 * (3 * j + 2) from by ring,
      show E + 3 * j + 2 = E + (3 * j + 2) from by ring]
  apply stepStar_trans (cycle (3 * j + 2) (A := 1) (C := 0) (D := 0) (E := E))
  -- After cycle: (3j+3, 2, 0, 3j+2, E)
  rw [show 1 + (3 * j + 2) = 3 * j + 3 from by ring,
      show 0 + (3 * j + 2) = 3 * j + 2 from by ring,
      show (2 : ℕ) = 1 + 1 from by ring]
  -- Step 3: Drain (⊢*)
  apply stepStar_trans (drain (3 * j + 2) (A := 3 * j + 3) (B := 1) (E := E))
  ring_nf; finish

-- Odd case: a = 2*j+1, initial e written as E + 3*j + 1.
-- After opening, cycle 3j rounds, then R1, then drain.
theorem odd_trans (j : ℕ) :
    ⟨2 * j + 1, 0, 0, 0, E + 3 * j + 1⟩ [fm]⊢⁺
    ⟨6 * j + 2, 0, 0, 0, E + 9 * j + 5⟩ := by
  -- R4 chain + opening
  apply stepStar_stepPlus_stepPlus
  · apply stepStar_trans (r4_chain (2 * j + 1) (c := 0) (e := E + 3 * j + 1))
    rw [show 0 + 3 * (2 * j + 1) = (6 * j) + 3 from by ring,
        show E + 3 * j + 1 = (E + 3 * j) + 1 from by ring]
    finish
  apply stepPlus_stepStar_stepPlus (opening (C := 6 * j) (E := E + 3 * j))
  -- After opening: (1, 2, 6j+1, 0, E+3j)
  rw [show 6 * j + 1 = 1 + 2 * (3 * j) from by ring,
      show E + 3 * j = E + (3 * j) from by ring]
  -- Cycle 3j rounds
  apply stepStar_trans (cycle (3 * j) (A := 1) (C := 1) (D := 0) (E := E))
  -- After cycle: (3j+1, 2, 1, 3j, E)
  rw [show 1 + 3 * j = 3 * j + 1 from by ring,
      show 0 + 3 * j = 3 * j from by ring]
  -- R1: (3j+1, 1, 0, 3j+1, E)
  step fm
  -- Drain
  rw [show (1 : ℕ) = 0 + 1 from by ring]
  apply stepStar_trans (drain (3 * j + 1) (A := 3 * j + 1) (B := 0) (E := E))
  ring_nf; finish

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨1, 0, 0, 0, 5⟩) (by execute fm 8)
  apply progress_nonhalt (fm := fm)
    (P := fun q ↦ ∃ a e, q = ⟨a, 0, 0, 0, e⟩ ∧ a ≥ 1 ∧ 2 * e ≥ 3 * a + 1)
  · intro c ⟨a, e, hq, ha, he⟩; subst hq
    rcases Nat.even_or_odd a with ⟨j, hj⟩ | ⟨j, hj⟩
    · rw [show j + j = 2 * j from by ring] at hj; subst hj
      obtain ⟨j, rfl⟩ : ∃ j', j = j' + 1 := ⟨j - 1, by omega⟩
      obtain ⟨E, rfl⟩ : ∃ E, e = E + (3 * j + 3) := ⟨e - (3 * j + 3), by omega⟩
      exact ⟨⟨6 * j + 5, 0, 0, 0, E + 9 * j + 10⟩,
        ⟨6 * j + 5, E + 9 * j + 10, rfl, by omega, by omega⟩,
        even_trans j⟩
    · subst hj
      obtain ⟨E, rfl⟩ : ∃ E, e = E + (3 * j + 1) := ⟨e - (3 * j + 1), by omega⟩
      exact ⟨⟨6 * j + 2, 0, 0, 0, E + 9 * j + 5⟩,
        ⟨6 * j + 2, E + 9 * j + 5, rfl, by omega, by omega⟩,
        odd_trans j⟩
  · exact ⟨1, 5, rfl, by omega, by omega⟩
