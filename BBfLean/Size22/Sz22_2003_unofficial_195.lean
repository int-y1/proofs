import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #195: [1/6, 275/21, 9/11, 4/5, 147/2]

Vector representation:
```
-1 -1  0  0  0
 0 -1  2 -1  1
 0  2  0  0 -1
 2  0 -1  0  0
-1  1  0  2  0
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6 (1M context)
-/

namespace Sz22_2003_unofficial_195

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a+1, b+1, c, d, e⟩ => some ⟨a, b, c, d, e⟩
  | ⟨a, b+1, c, d+1, e⟩ => some ⟨a, b, c+2, d, e+1⟩
  | ⟨a, b, c, d, e+1⟩ => some ⟨a, b+2, c, d, e⟩
  | ⟨a, b, c+1, d, e⟩ => some ⟨a+2, b, c, d, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b+1, c, d+2, e⟩
  | _ => none

theorem bd_drain : ∀ k c d e, ⟨0, 1, c, 2*k+d, e⟩ [fm]⊢* ⟨0, 1, c+4*k, d, e+k⟩ := by
  intro k; induction' k with k ih <;> intro c d e
  · simp; finish
  rw [show 2 * (k + 1) + d = (2 * k + d) + 2 from by ring]
  step fm; step fm; step fm
  apply stepStar_trans (ih (c + 4) d (e + 1))
  ring_nf; finish

theorem e_drain : ∀ k b c, ⟨0, b, c, 0, k⟩ [fm]⊢* ⟨0, b+2*k, c, 0, 0⟩ := by
  intro k; induction' k with k ih <;> intro b c
  · simp; finish
  rw [show (k + 1) = k + 1 from rfl]
  step fm
  apply stepStar_trans (ih (b + 2) c)
  ring_nf; finish

theorem cb_drain : ∀ k b c, ⟨0, b+2*k, c+k, 0, 0⟩ [fm]⊢* ⟨0, b, c, 0, 0⟩ := by
  intro k; induction' k with k ih <;> intro b c
  · simp; finish
  rw [show b + 2 * (k + 1) = (b + 2) + 2 * k from by ring,
      show c + (k + 1) = (c + 1) + k from by ring]
  apply stepStar_trans (ih (b + 2) (c + 1))
  step fm; step fm; step fm; finish

theorem c_to_a_even : ∀ k a, ⟨a, 0, k, 0, 0⟩ [fm]⊢* ⟨a+2*k, 0, 0, 0, 0⟩ := by
  intro k; induction' k with k ih <;> intro a
  · simp; finish
  step fm
  apply stepStar_trans (ih (a + 2))
  ring_nf; finish

theorem a_drain : ∀ m d, ⟨2*m+1, 0, 0, d, 0⟩ [fm]⊢* ⟨0, 1, 0, d+2*m+2, 0⟩ := by
  intro m; induction' m with m ih <;> intro d
  · step fm; finish
  rw [show 2 * (m + 1) + 1 = (2 * m + 1) + 2 from by ring]
  step fm; step fm
  apply stepStar_trans (ih (d + 2))
  ring_nf; finish

theorem main_trans (k : ℕ) :
    ⟨0, 1, 0, 2*(k+1), 0⟩ [fm]⊢⁺ ⟨0, 1, 0, 6*(k+1), 0⟩ := by
  apply stepStar_stepPlus_stepPlus
  · have h := bd_drain (k+1) 0 0 0; simp only [Nat.zero_add] at h; exact h
  apply stepStar_stepPlus_stepPlus
  · have h := e_drain (k+1) 1 (4*(k+1))
    simp only [show 1 + 2 * (k + 1) = 2 * (k + 1) + 1 from by ring] at h; exact h
  apply stepStar_stepPlus_stepPlus
  · have h := cb_drain (k+1) 1 (3*(k+1))
    simp only [show 1 + 2 * (k + 1) = 2 * (k + 1) + 1 from by ring,
               show 3 * (k + 1) + (k + 1) = 4 * (k + 1) from by ring] at h; exact h
  step fm; step fm
  apply stepStar_trans
  · have h := c_to_a_even (3*k+2) 1
    simp only [show 1 + 2 * (3 * k + 2) = 6 * k + 5 from by ring] at h; exact h
  have h := a_drain (3*k+2) 0
  simp only [Nat.zero_add,
             show 2 * (3 * k + 2) + 1 = 6 * k + 5 from by ring,
             show 2 * (3 * k + 2) + 2 = 6 * (k + 1) from by ring] at h
  exact h

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨0, 1, 0, 2, 0⟩) (by execute fm 1)
  apply progress_nonhalt_simple (fm := fm) (A := ℕ)
    (fun k ↦ ⟨0, 1, 0, 2*(k+1), 0⟩) 0
  intro k
  refine ⟨3*k+2, ?_⟩
  show ⟨0, 1, 0, 2*(k+1), 0⟩ [fm]⊢⁺ ⟨0, 1, 0, 2*(3*k+2+1), 0⟩
  simp only [show 2 * (3 * k + 2 + 1) = 6 * (k + 1) from by ring]
  exact main_trans k

end Sz22_2003_unofficial_195
