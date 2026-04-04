import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #1989: [99/35, 44/5, 25/6, 7/11, 5/2]

Vector representation:
```
 0  2 -1 -1  1
 2  0 -1  0  1
-1 -1  2  0  0
 0  0  0  1 -1
-1  0  1  0  0
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_1989

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a, b, c+1, d+1, e⟩ => some ⟨a, b+2, c, d, e+1⟩
  | ⟨a, b, c+1, d, e⟩ => some ⟨a+2, b, c, d, e+1⟩
  | ⟨a+1, b+1, c, d, e⟩ => some ⟨a, b, c+2, d, e⟩
  | ⟨a, b, c, d, e+1⟩ => some ⟨a, b, c, d+1, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b, c+1, d, e⟩
  | _ => none

-- R4 chain: move e to d
theorem e_to_d : ∀ k, ⟨a, 0, 0, d, k⟩ [fm]⊢* ⟨a, 0, 0, d + k, 0⟩ := by
  intro k; induction' k with k ih generalizing d
  · exists 0
  · rw [show d + (k + 1) = (d + 1) + k from by ring]
    step fm
    exact ih (d := d + 1)

-- R3-R2-R2 chain: drain b, grow a and e
theorem r3r2r2 : ∀ k, ⟨a + 1, k, 0, 0, e⟩ [fm]⊢* ⟨a + 3 * k + 1, 0, 0, 0, e + 2 * k⟩ := by
  intro k; induction' k with k ih generalizing a e
  · exists 0
  · step fm; step fm; step fm
    rw [show a + 3 + 1 = (a + 3) + 1 from by ring]
    apply stepStar_trans (ih (a := a + 3) (e := e + 2))
    ring_nf; finish

-- One round of R1-R1-R3: reduces d by 2
theorem round22 : ⟨a + 1, b, 2, d + 2, e⟩ [fm]⊢* ⟨a, b + 3, 2, d, e + 2⟩ := by
  step fm; step fm; step fm; finish

-- Chain of round22
theorem round22_chain : ∀ k, ⟨a + k, b, 2, d + 2 * k, e⟩ [fm]⊢* ⟨a, b + 3 * k, 2, d, e + 2 * k⟩ := by
  intro k; induction' k with k ih generalizing a b d e
  · exists 0
  · rw [show a + (k + 1) = (a + 1) + k from by ring,
        show d + 2 * (k + 1) = (d + 2) + 2 * k from by ring]
    apply stepStar_trans (ih (a := a + 1) (d := d + 2))
    rw [show a + 1 = a + 1 from rfl]
    apply stepStar_trans round22
    ring_nf; finish

-- Tail for d=0: R2, R2, then r3r2r2
theorem tail0 : ⟨a, b, 2, 0, e⟩ [fm]⊢* ⟨a + 3 * b + 4, 0, 0, 0, e + 2 * b + 2⟩ := by
  step fm; step fm
  show ⟨(a + 3) + 1, b, 0, 0, e + 1 + 1⟩ [fm]⊢* _
  apply stepStar_trans (r3r2r2 b (a := a + 3) (e := e + 1 + 1))
  ring_nf; finish

-- Tail for d=1: R1, R2, then r3r2r2
theorem tail1 : ⟨a, b, 2, 1, e⟩ [fm]⊢* ⟨a + 3 * b + 8, 0, 0, 0, e + 2 * b + 6⟩ := by
  step fm; step fm
  show ⟨(a + 1) + 1, b + 2, 0, 0, e + 1 + 1⟩ [fm]⊢* _
  apply stepStar_trans (r3r2r2 (b + 2) (a := a + 1) (e := e + 1 + 1))
  ring_nf; finish

-- Main transition for d=0
theorem main_d0 : ⟨F + 1, 0, 0, 0, 0⟩ [fm]⊢⁺ ⟨F + 2, 0, 0, 1, 0⟩ := by
  step fm; step fm; step fm; finish

-- Main transition for d >= 1 with d' even (d = 2k+1)
theorem main_odd :
    ⟨F + 2 * k + 2, 0, 0, 2 * k + 1, 0⟩ [fm]⊢⁺ ⟨F + 10 * k + 7, 0, 0, 8 * k + 5, 0⟩ := by
  step fm; step fm; step fm
  show ⟨F + 2 * k, 1, 2, 2 * k, 1⟩ [fm]⊢* ⟨F + 10 * k + 7, 0, 0, 8 * k + 5, 0⟩
  rw [show F + 2 * k = (F + k) + k from by ring,
      show (2 * k : ℕ) = 0 + 2 * k from by ring]
  apply stepStar_trans (round22_chain k (a := F + k) (b := 1) (d := 0) (e := 1))
  rw [show 1 + 3 * k = 3 * k + 1 from by ring,
      show 1 + 2 * k = 2 * k + 1 from by ring]
  apply stepStar_trans (tail0 (a := F + k) (b := 3 * k + 1) (e := 2 * k + 1))
  rw [show F + k + 3 * (3 * k + 1) + 4 = F + 10 * k + 7 from by ring,
      show 2 * k + 1 + 2 * (3 * k + 1) + 2 = 8 * k + 5 from by ring]
  have := e_to_d (8 * k + 5) (a := F + 10 * k + 7) (d := 0)
  simpa using this

-- Main transition for d >= 1 with d' odd (d = 2k+2)
theorem main_even :
    ⟨F + 2 * k + 3, 0, 0, 2 * k + 2, 0⟩ [fm]⊢⁺ ⟨F + 10 * k + 12, 0, 0, 8 * k + 9, 0⟩ := by
  step fm; step fm; step fm
  show ⟨F + 2 * k + 1, 1, 2, 2 * k + 1, 1⟩ [fm]⊢* ⟨F + 10 * k + 12, 0, 0, 8 * k + 9, 0⟩
  rw [show F + 2 * k + 1 = (F + k + 1) + k from by ring,
      show 2 * k + 1 = 1 + 2 * k from by ring]
  apply stepStar_trans (round22_chain k (a := F + k + 1) (b := 1) (d := 1) (e := 1))
  rw [show 1 + 3 * k = 3 * k + 1 from by ring,
      show 1 + 2 * k = 2 * k + 1 from by ring]
  apply stepStar_trans (tail1 (a := F + k + 1) (b := 3 * k + 1) (e := 2 * k + 1))
  rw [show F + k + 1 + 3 * (3 * k + 1) + 8 = F + 10 * k + 12 from by ring,
      show 2 * k + 1 + 2 * (3 * k + 1) + 6 = 8 * k + 9 from by ring]
  have := e_to_d (8 * k + 9) (a := F + 10 * k + 12) (d := 0)
  simpa using this

-- Main transition combining all cases
theorem main_trans :
    ⟨F + d + 1, 0, 0, d, 0⟩ [fm]⊢⁺ ⟨F + 5 * d + 2, 0, 0, 4 * d + 1, 0⟩ := by
  rcases d with _ | d'
  · -- d = 0
    show ⟨F + 1, 0, 0, 0, 0⟩ [fm]⊢⁺ ⟨F + 2, 0, 0, 1, 0⟩
    exact main_d0
  · -- d = d' + 1
    rcases Nat.even_or_odd d' with ⟨k, hk⟩ | ⟨k, hk⟩
    · -- d' = 2k, d = 2k + 1
      subst hk; rw [show k + k + 1 = 2 * k + 1 from by ring]
      rw [show F + (2 * k + 1) + 1 = F + 2 * k + 2 from by ring,
          show F + 5 * (2 * k + 1) + 2 = F + 10 * k + 7 from by ring,
          show 4 * (2 * k + 1) + 1 = 8 * k + 5 from by ring]
      exact main_odd
    · -- d' = 2k + 1, d = 2k + 2
      subst hk; rw [show 2 * k + 1 + 1 = 2 * k + 2 from by ring]
      rw [show F + (2 * k + 2) + 1 = F + 2 * k + 3 from by ring,
          show F + 5 * (2 * k + 2) + 2 = F + 10 * k + 12 from by ring,
          show 4 * (2 * k + 2) + 1 = 8 * k + 9 from by ring]
      exact main_even

theorem nonhalt : ¬halts fm c₀ := by
  apply progress_nonhalt_simple (fm := fm) (A := ℕ × ℕ)
    (fun ⟨F, d⟩ ↦ ⟨F + d + 1, 0, 0, d, 0⟩) ⟨0, 0⟩
  intro ⟨F, d⟩
  refine ⟨⟨F + d, 4 * d + 1⟩, ?_⟩
  show ⟨F + d + 1, 0, 0, d, 0⟩ [fm]⊢⁺ ⟨(F + d) + (4 * d + 1) + 1, 0, 0, 4 * d + 1, 0⟩
  rw [show (F + d) + (4 * d + 1) + 1 = F + 5 * d + 2 from by ring]
  exact main_trans
