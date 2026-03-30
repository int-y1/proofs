import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #1072: [5/6, 196/55, 121/2, 3/7, 10/11]

Vector representation:
```
-1 -1  1  0  0
 2  0 -1  2 -1
-1  0  0  0  2
 0  1  0 -1  0
 1  0  1  0 -1
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_1072

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a+1, b+1, c, d, e⟩ => some ⟨a, b, c+1, d, e⟩
  | ⟨a, b, c+1, d, e+1⟩ => some ⟨a+2, b, c, d+2, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b, c, d, e+2⟩
  | ⟨a, b, c, d+1, e⟩ => some ⟨a, b+1, c, d, e⟩
  | ⟨a, b, c, d, e+1⟩ => some ⟨a+1, b, c+1, d, e⟩
  | _ => none

private theorem r4_drain : ∀ k, ∀ b d e,
    ⟨(0 : ℕ), b, 0, d + k, e⟩ [fm]⊢* ⟨0, b + k, 0, d, e⟩ := by
  intro k; induction' k with k ih <;> intro b d e
  · ring_nf; finish
  · rw [show d + (k + 1) = (d + k) + 1 from by ring,
        show b + (k + 1) = (b + 1) + k from by ring]
    step fm; exact ih (b + 1) d e

private theorem r3_drain : ∀ k, ∀ d e,
    ⟨k, (0 : ℕ), 0, d, e⟩ [fm]⊢* ⟨0, 0, 0, d, e + 2 * k⟩ := by
  intro k; induction' k with k ih <;> intro d e
  · ring_nf; finish
  · rw [show e + 2 * (k + 1) = (e + 2) + 2 * k from by ring]
    step fm; exact ih d (e + 2)

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
      rw [show c + 1 + 1 = (c + 1) + 1 from by ring,
          show e + b + c + 1 + 1 = (e + b + c + 1) + 1 from by ring]
      step fm
      have h := ih 1 c (d + 2) e
      convert h using 2; all_goals ring_nf
    · rw [show e + (b + 1) + c + 1 = (e + b + c + 1) + 1 from by ring]
      step fm
      rw [show c + 1 + 1 = (c + 1) + 1 from by ring,
          show e + b + c + 1 + 1 = e + b + (c + 1) + 1 from by ring]
      have h := ih a' (c + 1) d e
      convert h using 2; all_goals ring_nf

private theorem main_trans_zero (e : ℕ) :
    ⟨(0 : ℕ), 0, 0, 0, e + 2⟩ [fm]⊢⁺ ⟨0, 0, 0, 2, e + 6⟩ := by
  rw [show e + 2 = (e + 1) + 1 from by ring]
  apply step_stepStar_stepPlus
  · show fm ⟨(0 : ℕ), 0, 0, 0, (e + 1) + 1⟩ = some ⟨1, 0, 1, 0, e + 1⟩; rfl
  apply stepStar_trans
  · have h := interleave 0 0 0 0 e
    convert h using 2
  have h := r3_drain 3 2 e
  convert h using 2

private theorem main_trans_succ (d e : ℕ) :
    ⟨(0 : ℕ), 0, 0, d + 1, e + d + 3⟩ [fm]⊢⁺ ⟨0, 0, 0, 2 * d + 4, e + 2 * d + 8⟩ := by
  rw [show d + 1 = 0 + (d + 1) from by ring]
  apply stepStar_stepPlus_stepPlus (r4_drain (d + 1) 0 0 (e + d + 3))
  rw [show (0 : ℕ) + (d + 1) = d + 1 from by ring,
      show e + d + 3 = (e + d + 2) + 1 from by ring]
  apply step_stepStar_stepPlus
  · show fm ⟨(0 : ℕ), d + 1, 0, 0, (e + d + 2) + 1⟩ =
         some ⟨1, d + 1, 1, 0, e + d + 2⟩; rfl
  apply stepStar_trans
  · have h := interleave (d + 1) 0 0 0 e
    convert h using 2
  have h := r3_drain (d + 4) (2 * d + 4) e
  convert h using 2; all_goals ring_nf

private theorem main_trans (d e : ℕ) :
    ⟨(0 : ℕ), 0, 0, d, e + d + 2⟩ [fm]⊢⁺ ⟨0, 0, 0, 2 * d + 2, e + 2 * d + 6⟩ := by
  rcases d with _ | d'
  · exact main_trans_zero e
  · have h := main_trans_succ d' e
    convert h using 2

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨0, 0, 0, 0, 2⟩) (by execute fm 1)
  apply progress_nonhalt_simple (fm := fm) (A := ℕ × ℕ)
    (fun ⟨d, e⟩ ↦ ⟨0, 0, 0, d, e + d + 2⟩) ⟨0, 0⟩
  intro ⟨d, e⟩; exists ⟨2 * d + 2, e + 2⟩
  show ⟨(0 : ℕ), 0, 0, d, e + d + 2⟩ [fm]⊢⁺ ⟨0, 0, 0, 2 * d + 2, e + 2 + (2 * d + 2) + 2⟩
  have h := main_trans d e
  convert h using 2; all_goals ring_nf

end Sz22_2003_unofficial_1072
