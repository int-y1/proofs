import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #1130: [5/6, 44/35, 49/2, 3/11, 1/5, 5/7]

Vector representation:
```
-1 -1  1  0  0
 2  0 -1 -1  1
-1  0  0  2  0
 0  1  0  0 -1
 0  0 -1  0  0
 0  0  1 -1  0
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_1130

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a+1, b+1, c, d, e⟩ => some ⟨a, b, c+1, d, e⟩
  | ⟨a, b, c+1, d+1, e⟩ => some ⟨a+2, b, c, d, e+1⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b, c, d+2, e⟩
  | ⟨a, b, c, d, e+1⟩ => some ⟨a, b+1, c, d, e⟩
  | ⟨a, b, c+1, d, e⟩ => some ⟨a, b, c, d, e⟩
  | ⟨a, b, c, d+1, e⟩ => some ⟨a, b, c+1, d, e⟩
  | _ => none

theorem e_to_b : ∀ k, ⟨0, b, 0, d, e + k⟩ [fm]⊢* ⟨0, b + k, 0, d, e⟩ := by
  intro k; induction' k with k ih generalizing b
  · exists 0
  · rw [show e + (k + 1) = (e + k) + 1 from by ring]
    step fm
    apply stepStar_trans (ih (b := b + 1))
    ring_nf; finish

theorem a_to_d : ∀ k, ⟨a + k, 0, 0, d, e⟩ [fm]⊢* ⟨a, 0, 0, d + 2 * k, e⟩ := by
  intro k; induction' k with k ih generalizing d
  · exists 0
  · rw [show a + (k + 1) = (a + k) + 1 from by ring]
    step fm
    apply stepStar_trans (ih (d := d + 2))
    ring_nf; finish

theorem r2_chain : ∀ k, ⟨a, 0, c + k, D + k, e⟩ [fm]⊢* ⟨a + 2 * k, 0, c, D, e + k⟩ := by
  intro k; induction' k with k ih generalizing a e
  · exists 0
  · rw [show c + (k + 1) = (c + k) + 1 from by ring,
        show D + (k + 1) = (D + k) + 1 from by ring]
    step fm
    apply stepStar_trans (ih (a := a + 2) (e := e + 1))
    ring_nf; finish

theorem inner_spiral : ∀ b, ∀ c D e,
    ⟨2, b, c, D + b + c, e⟩ [fm]⊢* ⟨b + 2 * c + 2, 0, 0, D, e + b + c⟩ := by
  intro b; induction' b using Nat.strongRecOn with b ih; intro c D e
  rcases b with _ | _ | b
  · -- b = 0: just r2_chain
    show ⟨2, 0, c, D + 0 + c, e⟩ [fm]⊢* ⟨0 + 2 * c + 2, 0, 0, D, e + 0 + c⟩
    rw [show D + 0 + c = D + c from by ring]
    have h := r2_chain c (a := 2) (c := 0) (D := D) (e := e)
    simp only [Nat.zero_add] at h
    apply stepStar_trans h
    ring_nf; finish
  · -- b = 1: R1, then r2_chain
    show ⟨2, 0 + 1, c, D + (0 + 1) + c, e⟩ [fm]⊢* ⟨0 + 1 + 2 * c + 2, 0, 0, D, e + (0 + 1) + c⟩
    rw [show D + (0 + 1) + c = D + (c + 1) from by ring]
    step fm
    have h := r2_chain (c + 1) (a := 1) (c := 0) (D := D) (e := e)
    simp only [Nat.zero_add] at h
    apply stepStar_trans h
    ring_nf; finish
  · -- b+2: R1, R1, R2, then IH(b)
    show ⟨2, b + 1 + 1, c, D + (b + 1 + 1) + c, e⟩ [fm]⊢*
      ⟨b + 1 + 1 + 2 * c + 2, 0, 0, D, e + (b + 1 + 1) + c⟩
    rw [show D + (b + 1 + 1) + c = (D + b + c) + 1 + 1 from by ring]
    step fm
    step fm
    rw [show c + 2 = (c + 1) + 1 from by ring,
        show D + b + c + 2 = (D + b + (c + 1)) + 1 from by ring]
    step fm
    show ⟨2, b, c + 1, D + b + (c + 1), e + 1⟩ [fm]⊢* _
    apply stepStar_trans (ih b (by omega) (c + 1) D (e + 1))
    ring_nf; finish

theorem main_trans_star (D E : ℕ) :
    ⟨0, E + 1, 0, D + E + 3, 0⟩ [fm]⊢⁺ ⟨0, 0, 0, D + 2 * E + 6, E + 2⟩ := by
  -- R6: (0, E+1, 0, D+E+3, 0) → (0, E+1, 1, D+E+2, 0)
  apply step_stepStar_stepPlus
  · show fm ⟨0, E + 1, 0, D + E + 3, 0⟩ = some ⟨0, E + 1, 1, D + E + 2, 0⟩
    rw [show D + E + 3 = (D + E + 2) + 1 from by ring]
    simp [fm]
  -- R2: (0, E+1, 1, D+E+2, 0) → (2, E+1, 0, D+E+1, 1)
  rw [show (1 : ℕ) = 0 + 1 from by omega,
      show D + E + 2 = (D + E + 1) + 1 from by ring]
  step fm
  -- Inner spiral: (2, E+1, 0, D+(E+1)+0, 1) →* (E+3, 0, 0, D, E+2)
  rw [show D + E + 1 = D + (E + 1) + 0 from by ring]
  apply stepStar_trans (inner_spiral (E + 1) 0 D 1)
  -- a_to_d: (E+3, 0, 0, D, E+2) →* (0, 0, 0, D+2*(E+3), E+2)
  rw [show E + 1 + 2 * 0 + 2 = E + 3 from by ring,
      show 1 + (E + 1) + 0 = E + 2 from by ring,
      show (E + 3 : ℕ) = 0 + (E + 3) from by ring]
  apply stepStar_trans (a_to_d (E + 3) (a := 0) (d := D) (e := E + 2))
  ring_nf; finish

theorem main_trans (D E : ℕ) :
    ⟨0, 0, 0, D + E + 3, E + 1⟩ [fm]⊢⁺ ⟨0, 0, 0, D + 2 * E + 6, E + 2⟩ := by
  -- R4 chain: (0, 0, 0, D+E+3, E+1) →* (0, E+1, 0, D+E+3, 0)
  apply stepStar_stepPlus_stepPlus
  · rw [show (E + 1 : ℕ) = 0 + (E + 1) from by ring]
    exact e_to_b (E + 1) (b := 0) (d := D + E + 3) (e := 0)
  · rw [show (0 : ℕ) + (E + 1) = E + 1 from by ring]
    exact main_trans_star D E

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨0, 0, 0, 4, 1⟩)
  · execute fm 5
  apply progress_nonhalt_simple (fm := fm) (A := ℕ × ℕ)
    (fun ⟨D, E⟩ ↦ ⟨0, 0, 0, D + E + 3, E + 1⟩) ⟨1, 0⟩
  intro ⟨D, E⟩
  refine ⟨⟨D + E + 2, E + 1⟩, ?_⟩
  show ⟨0, 0, 0, D + E + 3, E + 1⟩ [fm]⊢⁺ ⟨0, 0, 0, (D + E + 2) + (E + 1) + 3, (E + 1) + 1⟩
  rw [show (D + E + 2) + (E + 1) + 3 = D + 2 * E + 6 from by ring,
      show (E + 1) + 1 = E + 2 from by ring]
  exact main_trans D E
