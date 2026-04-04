import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #1635: [77/15, 26/3, 9/91, 5/11, 45/2]

Vector representation:
```
 0 -1 -1  1  1  0
 1 -1  0  0  0  1
 0  2  0 -1  0 -1
 0  0  1  0 -1  0
-1  2  1  0  0  0
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_1635

def Q := ℕ × ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a, b+1, c+1, d, e, f⟩ => some ⟨a, b, c, d+1, e+1, f⟩
  | ⟨a, b+1, c, d, e, f⟩ => some ⟨a+1, b, c, d, e, f+1⟩
  | ⟨a, b, c, d+1, e, f+1⟩ => some ⟨a, b+2, c, d, e, f⟩
  | ⟨a, b, c, d, e+1, f⟩ => some ⟨a, b, c+1, d, e, f⟩
  | ⟨a+1, b, c, d, e, f⟩ => some ⟨a, b+2, c+1, d, e, f⟩
  | _ => none

theorem e_to_c : ∀ k, ∀ a c f,
    ⟨a, 0, c, 0, k, f⟩ [fm]⊢* ⟨a, 0, c + k, 0, 0, f⟩ := by
  intro k; induction' k with k ih <;> intro a c f
  · exists 0
  rw [show (k + 1) = k + 1 from rfl]
  step fm
  apply stepStar_trans (ih a (c + 1) f)
  ring_nf; finish

theorem r1r1r3_chain : ∀ k, ∀ α c d e f,
    ⟨α, 2, c + 2 * k, d + 1, e, f + k + 1⟩ [fm]⊢*
    ⟨α, 2, c, d + k + 1, e + 2 * k, f + 1⟩ := by
  intro k; induction' k with k ih <;> intro α c d e f
  · simp; exists 0
  rw [show c + 2 * (k + 1) = (c + 2 * k) + 1 + 1 from by ring,
      show f + (k + 1) + 1 = (f + k + 1) + 1 from by ring]
  step fm; step fm; step fm
  apply stepStar_trans (ih α c (d + 1) (e + 2) f)
  ring_nf; finish

theorem drain_chain : ∀ k, ∀ a d e f,
    ⟨a, 0, 0, d + k, e, f + 1⟩ [fm]⊢* ⟨a + 2 * k, 0, 0, d, e, f + k + 1⟩ := by
  intro k; induction' k with k ih <;> intro a d e f
  · simp; exists 0
  rw [show d + (k + 1) = (d + k) + 1 from by ring]
  step fm; step fm; step fm
  rw [show a + 1 + 1 = a + 2 from by ring,
      show f + 1 + 1 = (f + 1) + 1 from by ring]
  apply stepStar_trans (ih (a + 2) d e (f + 1))
  ring_nf; finish

theorem main_trans_zero (A : ℕ) :
    ⟨A + 1, 0, 0, 0, 0, 0⟩ [fm]⊢⁺ ⟨A + 3, 0, 0, 0, 1, 2⟩ := by
  -- R5: (A, 2, 1, 0, 0, 0)
  -- R1: (A, 1, 0, 1, 1, 0)
  -- R2: (A+1, 0, 0, 1, 1, 1)
  -- R3: (A+1, 2, 0, 0, 1, 0)
  -- R2: (A+2, 1, 0, 0, 1, 1)
  -- R2: (A+3, 0, 0, 0, 1, 2)
  step fm; step fm; step fm; step fm; step fm; step fm; ring_nf; finish

theorem main_trans_n_odd (m A : ℕ) :
    ⟨A + 1, 0, 0, 0, 2 * m + 1, 4 * m + 2⟩ [fm]⊢⁺
    ⟨A + 2 * m + 4, 0, 0, 0, 2 * m + 2, 4 * m + 4⟩ := by
  -- Phase 1: R4 drain e to c
  have p1 : ⟨A + 1, 0, 0, 0, 2 * m + 1, 4 * m + 2⟩ [fm]⊢*
      ⟨A + 1, 0, 2 * m + 1, 0, 0, 4 * m + 2⟩ := by
    have := e_to_c (2 * m + 1) (A + 1) 0 (4 * m + 2)
    simp only [Nat.zero_add] at this; exact this
  -- Phase 2: R5, R1, R1, R3
  have p2 : ⟨A + 1, 0, 2 * m + 1, 0, 0, 4 * m + 2⟩ [fm]⊢⁺
      ⟨A, 2, 2 * m, 1, 2, 4 * m + 1⟩ := by
    rw [show A + 1 = A + 1 from rfl,
        show 2 * m + 1 = (2 * m) + 1 from by ring]
    step fm; step fm; step fm; step fm
    ring_nf; finish
  -- Phase 3: R1R1R3 chain
  have p3 : ⟨A, 2, 2 * m, 1, 2, 4 * m + 1⟩ [fm]⊢*
      ⟨A, 2, 0, m + 1, 2 * m + 2, 3 * m + 1⟩ := by
    have h := r1r1r3_chain m A 0 0 2 (3 * m)
    rw [show 0 + 2 * m = 2 * m from by ring,
        show 3 * m + m + 1 = 4 * m + 1 from by ring,
        show 0 + m + 1 = m + 1 from by ring,
        show 2 + 2 * m = 2 * m + 2 from by ring] at h
    exact h
  -- Phase 4: R2, R2
  have p4 : ⟨A, 2, 0, m + 1, 2 * m + 2, 3 * m + 1⟩ [fm]⊢*
      ⟨A + 2, 0, 0, m + 1, 2 * m + 2, 3 * m + 3⟩ := by
    step fm; step fm; ring_nf; finish
  -- Phase 5: drain
  have p5 : ⟨A + 2, 0, 0, m + 1, 2 * m + 2, 3 * m + 3⟩ [fm]⊢*
      ⟨A + 2 * m + 4, 0, 0, 0, 2 * m + 2, 4 * m + 4⟩ := by
    have h := drain_chain (m + 1) (A + 2) 0 (2 * m + 2) (3 * m + 2)
    rw [show 0 + (m + 1) = m + 1 from by ring,
        show 3 * m + 2 + 1 = 3 * m + 3 from by ring,
        show A + 2 + 2 * (m + 1) = A + 2 * m + 4 from by ring,
        show 3 * m + 2 + (m + 1) + 1 = 4 * m + 4 from by ring] at h
    exact h
  exact stepStar_stepPlus_stepPlus p1
    (stepPlus_stepStar_stepPlus p2
      (stepStar_trans p3 (stepStar_trans p4 p5)))

theorem main_trans_n_even (m A : ℕ) :
    ⟨A + 1, 0, 0, 0, 2 * m + 2, 4 * m + 4⟩ [fm]⊢⁺
    ⟨A + 2 * m + 5, 0, 0, 0, 2 * m + 3, 4 * m + 6⟩ := by
  -- Phase 1: R4 drain e to c
  have p1 : ⟨A + 1, 0, 0, 0, 2 * m + 2, 4 * m + 4⟩ [fm]⊢*
      ⟨A + 1, 0, 2 * m + 2, 0, 0, 4 * m + 4⟩ := by
    have := e_to_c (2 * m + 2) (A + 1) 0 (4 * m + 4)
    simp only [Nat.zero_add] at this; exact this
  -- Phase 2: R5, R1, R1, R3
  have p2 : ⟨A + 1, 0, 2 * m + 2, 0, 0, 4 * m + 4⟩ [fm]⊢⁺
      ⟨A, 2, 2 * m + 1, 1, 2, 4 * m + 3⟩ := by
    rw [show A + 1 = A + 1 from rfl,
        show 2 * m + 2 = (2 * m + 1) + 1 from by ring,
        show 4 * m + 4 = (4 * m + 3) + 1 from by ring]
    step fm; step fm; step fm; step fm
    ring_nf; finish
  -- Phase 3: R1R1R3 chain
  have p3 : ⟨A, 2, 2 * m + 1, 1, 2, 4 * m + 3⟩ [fm]⊢*
      ⟨A, 2, 1, m + 1, 2 * m + 2, 3 * m + 3⟩ := by
    have h := r1r1r3_chain m A 1 0 2 (3 * m + 2)
    rw [show 1 + 2 * m = 2 * m + 1 from by ring,
        show 3 * m + 2 + m + 1 = 4 * m + 3 from by ring,
        show 0 + m + 1 = m + 1 from by ring,
        show 2 + 2 * m = 2 * m + 2 from by ring,
        show 3 * m + 2 + 1 = 3 * m + 3 from by ring] at h
    exact h
  -- Phase 3b: R1, R2
  have p3b : ⟨A, 2, 1, m + 1, 2 * m + 2, 3 * m + 3⟩ [fm]⊢*
      ⟨A + 1, 0, 0, m + 2, 2 * m + 3, 3 * m + 4⟩ := by
    rw [show (1 : ℕ) = 0 + 1 from by ring,
        show m + 1 = m + 1 from rfl,
        show 3 * m + 3 = (3 * m + 2) + 1 from by ring]
    step fm
    rw [show m + 1 + 1 = m + 2 from by ring,
        show 2 * m + 2 + 1 = 2 * m + 3 from by ring]
    step fm
    ring_nf; finish
  -- Phase 4: drain
  have p4 : ⟨A + 1, 0, 0, m + 2, 2 * m + 3, 3 * m + 4⟩ [fm]⊢*
      ⟨A + 2 * m + 5, 0, 0, 0, 2 * m + 3, 4 * m + 6⟩ := by
    have h := drain_chain (m + 2) (A + 1) 0 (2 * m + 3) (3 * m + 3)
    rw [show 0 + (m + 2) = m + 2 from by ring,
        show 3 * m + 3 + 1 = 3 * m + 4 from by ring,
        show A + 1 + 2 * (m + 2) = A + 2 * m + 5 from by ring,
        show 3 * m + 3 + (m + 2) + 1 = 4 * m + 6 from by ring] at h
    exact h
  exact stepStar_stepPlus_stepPlus p1
    (stepPlus_stepStar_stepPlus p2
      (stepStar_trans p3 (stepStar_trans p3b p4)))

theorem main_trans (A N : ℕ) :
    ⟨A + 1, 0, 0, 0, N, 2 * N⟩ [fm]⊢⁺ ⟨A + N + 3, 0, 0, 0, N + 1, 2 * N + 2⟩ := by
  rcases N with _ | N
  · exact main_trans_zero A
  rcases Nat.even_or_odd N with ⟨m, hm⟩ | ⟨m, hm⟩
  · subst hm
    have h := main_trans_n_odd m A
    rw [show 2 * m + 1 = m + m + 1 from by ring,
        show 4 * m + 2 = 2 * (m + m + 1) from by ring,
        show A + 2 * m + 4 = A + (m + m + 1) + 3 from by ring,
        show 2 * m + 2 = (m + m + 1) + 1 from by ring,
        show 4 * m + 4 = 2 * ((m + m + 1) + 1) from by ring] at h
    convert h using 2
  · subst hm
    have h := main_trans_n_even m A
    rw [show 2 * m + 2 = 2 * m + 1 + 1 from by ring,
        show 4 * m + 4 = 2 * (2 * m + 1 + 1) from by ring,
        show A + 2 * m + 5 = A + (2 * m + 1 + 1) + 3 from by ring,
        show 2 * m + 3 = (2 * m + 1 + 1) + 1 from by ring,
        show 4 * m + 6 = 2 * ((2 * m + 1 + 1) + 1) from by ring] at h
    convert h using 2

theorem nonhalt : ¬halts fm c₀ := by
  apply progress_nonhalt_simple (fm := fm) (A := ℕ × ℕ)
    (fun ⟨A, N⟩ ↦ ⟨A + 1, 0, 0, 0, N, 2 * N⟩) ⟨0, 0⟩
  intro ⟨A, N⟩; exact ⟨⟨A + N + 2, N + 1⟩, main_trans A N⟩

end Sz22_2003_unofficial_1635
