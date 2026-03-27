import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #216: [1/9, 20/3, 3/14, 11/2, 7/55, 3/11]

Vector representation:
```
 0 -2  0  0  0
 2 -1  1  0  0
-1  1  0 -1  0
-1  0  0  0  1
 0  0 -1  1 -1
 0  1  0  0 -1
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_216

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a, b+2, c, d, e⟩ => some ⟨a, b, c, d, e⟩
  | ⟨a, b+1, c, d, e⟩ => some ⟨a+2, b, c+1, d, e⟩
  | ⟨a+1, b, c, d+1, e⟩ => some ⟨a, b+1, c, d, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b, c, d, e+1⟩
  | ⟨a, b, c+1, d, e+1⟩ => some ⟨a, b, c, d+1, e⟩
  | ⟨a, b, c, d, e+1⟩ => some ⟨a, b+1, c, d, e⟩
  | _ => none

theorem a_to_e : ∀ k a c e, ⟨a+k, 0, c, 0, e⟩ [fm]⊢* ⟨a, 0, c, 0, e+k⟩ := by
  intro k; induction' k with k h <;> intro a c e
  · exists 0
  rw [show a + (k + 1) = (a + k) + 1 from by ring]
  step fm
  apply stepStar_trans (h _ _ _)
  ring_nf; finish

theorem ce_to_d : ∀ k c d e, ⟨0, 0, c+k, d, e+k⟩ [fm]⊢* ⟨0, 0, c, d+k, e⟩ := by
  intro k; induction' k with k h <;> intro c d e
  · exists 0
  rw [show c + (k + 1) = (c + k) + 1 from by ring,
      show e + (k + 1) = (e + k) + 1 from by ring]
  step fm
  apply stepStar_trans (h _ _ _)
  ring_nf; finish

theorem r3r2_chain : ∀ k j c d, ⟨j+1, 0, c, d+k, 0⟩ [fm]⊢* ⟨j+k+1, 0, c+k, d, 0⟩ := by
  intro k; induction' k with k h <;> intro j c d
  · exists 0
  rw [show d + (k + 1) = (d + k) + 1 from by ring,
      show j + 1 = j + 1 from rfl]
  step fm
  step fm
  apply stepStar_trans (h _ _ _)
  ring_nf; finish

theorem r6_step (n : ℕ) : ⟨0, 0, 0, n, 1⟩ [fm]⊢ ⟨0, 1, 0, n, 0⟩ := by
  unfold fm; cases n <;> rfl

theorem r2_step (n : ℕ) : ⟨0, 1, 0, n, 0⟩ [fm]⊢ ⟨2, 0, 1, n, 0⟩ := by
  unfold fm; cases n <;> rfl

theorem main_cycle (n : ℕ) : ⟨n+1, 0, n, 0, 0⟩ [fm]⊢⁺ ⟨n+2, 0, n+1, 0, 0⟩ := by
  apply step_stepStar_stepPlus
  · show fm ⟨n+1, 0, n, 0, 0⟩ = some ⟨n, 0, n, 0, 1⟩; rfl
  apply stepStar_trans
  · have h := a_to_e n 0 n 1
    simp only [Nat.zero_add] at h; exact h
  apply stepStar_trans
  · have h := ce_to_d n 0 0 1
    simp only [Nat.zero_add] at h; exact h
  apply stepStar_trans
  · exact step_stepStar (r6_step n)
  apply stepStar_trans
  · exact step_stepStar (r2_step n)
  have h := r3r2_chain n 1 1 0
  simp only [Nat.zero_add] at h
  rw [show 1 + n + 1 = n + 2 from by omega, show 1 + n = n + 1 from by omega] at h
  exact h

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨2, 0, 1, 0, 0⟩) (by execute fm 3)
  apply progress_nonhalt_simple (fm := fm) (A := ℕ) (fun n ↦ ⟨n+2, 0, n+1, 0, 0⟩) 0
  intro n
  exists n + 1
  exact main_cycle (n + 1)

end Sz22_2003_unofficial_216
