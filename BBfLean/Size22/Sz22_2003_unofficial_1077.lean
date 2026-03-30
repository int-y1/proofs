import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #1077: [5/6, 196/55, 121/2, 3/7, 5/11]

Vector representation:
```
-1 -1  1  0  0
 2  0 -1  2 -1
-1  0  0  0  2
 0  1  0 -1  0
 0  0  1  0 -1
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_1077

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a+1, b+1, c, d, e⟩ => some ⟨a, b, c+1, d, e⟩
  | ⟨a, b, c+1, d, e+1⟩ => some ⟨a+2, b, c, d+2, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b, c, d, e+2⟩
  | ⟨a, b, c, d+1, e⟩ => some ⟨a, b+1, c, d, e⟩
  | ⟨a, b, c, d, e+1⟩ => some ⟨a, b, c+1, d, e⟩
  | _ => none

private theorem r3_drain : ∀ k, ∀ d e,
    ⟨k, (0 : ℕ), 0, d, e⟩ [fm]⊢* ⟨0, 0, 0, d, e + 2 * k⟩ := by
  intro k; induction' k with k ih <;> intro d e
  · ring_nf; finish
  · rw [show e + 2 * (k + 1) = (e + 2) + 2 * k from by ring]
    step fm; exact ih d (e + 2)

private theorem r4_drain : ∀ k, ∀ b d e,
    ⟨(0 : ℕ), b, 0, d + k, e⟩ [fm]⊢* ⟨0, b + k, 0, d, e⟩ := by
  intro k; induction' k with k ih <;> intro b d e
  · ring_nf; finish
  · rw [show d + (k + 1) = (d + k) + 1 from by ring,
        show b + (k + 1) = (b + 1) + k from by ring]
    step fm; exact ih (b + 1) d e

private theorem r2_chain : ∀ k, ∀ a d e,
    ⟨a, (0 : ℕ), k, d, e + k⟩ [fm]⊢* ⟨a + 2 * k, 0, 0, d + 2 * k, e⟩ := by
  intro k; induction' k with k ih <;> intro a d e
  · ring_nf; finish
  · rw [show e + (k + 1) = (e + k) + 1 from by ring,
        show a + 2 * (k + 1) = (a + 2) + 2 * k from by ring,
        show d + 2 * (k + 1) = (d + 2) + 2 * k from by ring]
    step fm; exact ih (a + 2) (d + 2) e

private theorem interleave : ∀ b, ∀ a c d e,
    ⟨a + 1, b, c + 1, d, e + b + c + 1⟩ [fm]⊢*
    ⟨a + b + 2 * c + 3, 0, 0, d + 2 * b + 2 * c + 2, e⟩ := by
  intro b; induction' b with b ih <;> intro a c d e
  · have h := r2_chain (c + 1) (a + 1) d e
    convert h using 2; all_goals ring_nf
  · rcases a with _ | a'
    · rw [show e + (b + 1) + c + 1 = (e + b + c + 1) + 1 from by ring]
      step fm
      rw [show c + 1 + 1 = (c + 1) + 1 from by ring]
      step fm
      have h := ih 1 c (d + 2) e
      convert h using 2; all_goals ring_nf
    · rw [show e + (b + 1) + c + 1 = (e + b + c + 1) + 1 from by ring]
      step fm
      rw [show c + 1 + 1 = (c + 1) + 1 from by ring,
          show e + b + c + 1 + 1 = e + b + (c + 1) + 1 from by ring]
      have h := ih a' (c + 1) d e
      convert h using 2; all_goals ring_nf

private theorem main_trans_zero :
    ⟨(1 : ℕ), 0, 0, 0, 0⟩ [fm]⊢⁺ ⟨2, 0, 0, 2, 0⟩ := by
  execute fm 3

private theorem main_trans_succ (m : ℕ) :
    ⟨m + 2, (0 : ℕ), 0, 2 * m + 2, 0⟩ [fm]⊢⁺ ⟨2 * m + 4, 0, 0, 4 * m + 6, 0⟩ := by
  apply stepStar_stepPlus_stepPlus (r3_drain (m + 2) (2 * m + 2) 0)
  rw [show (0 : ℕ) + 2 * (m + 2) = 2 * m + 4 from by ring,
      show 2 * m + 2 = 0 + (2 * m + 2) from by ring]
  apply stepStar_stepPlus_stepPlus (r4_drain (2 * m + 2) 0 0 (2 * m + 4))
  rw [show (0 : ℕ) + (2 * m + 2) = 2 * m + 2 from by ring,
      show 2 * m + 4 = (2 * m + 3) + 1 from by ring]
  apply step_stepStar_stepPlus
  · show fm ⟨(0 : ℕ), 2 * m + 2, 0, 0, (2 * m + 3) + 1⟩ =
         some ⟨0, 2 * m + 2, 1, 0, 2 * m + 3⟩; rfl
  rw [show 2 * m + 3 = (2 * m + 2) + 1 from by ring]
  step fm
  rw [show 2 * m + 2 = (2 * m + 1) + 1 from by ring]
  step fm
  rw [show 2 * m + 1 + 1 = (2 * m + 1) + 1 from by ring,
      show 2 * m + 2 = 0 + (2 * m + 1) + 0 + 1 from by ring]
  have h := interleave (2 * m + 1) 0 0 2 0
  apply stepStar_trans
  · convert h using 2
  ring_nf; finish

theorem nonhalt : ¬halts fm c₀ := by
  apply progress_nonhalt_simple (fm := fm) (A := ℕ)
    (fun n ↦ ⟨n + 1, 0, 0, 2 * n, 0⟩) 0
  intro n; rcases n with _ | m
  · exists 1; exact main_trans_zero
  · exists 2 * m + 3
    show ⟨m + 2, (0 : ℕ), 0, 2 * (m + 1), 0⟩ [fm]⊢⁺
         ⟨2 * (m + 1) + 1 + 1, 0, 0, 2 * (2 * (m + 1) + 1), 0⟩
    have h := main_trans_succ m
    convert h using 2; all_goals ring_nf

end Sz22_2003_unofficial_1077
