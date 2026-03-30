import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #1065: [5/3, 66/35, 1/5, 343/2, 1/77, 5/7]

Vector representation:
```
 0 -1  1  0  0
 1  1 -1 -1  1
 0  0 -1  0  0
-1  0  0  3  0
 0  0  0 -1 -1
 0  0  1 -1  0
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_1065

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a, b+1, c, d, e⟩ => some ⟨a, b, c+1, d, e⟩
  | ⟨a, b, c+1, d+1, e⟩ => some ⟨a+1, b+1, c, d, e+1⟩
  | ⟨a, b, c+1, d, e⟩ => some ⟨a, b, c, d, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b, c, d+3, e⟩
  | ⟨a, b, c, d+1, e+1⟩ => some ⟨a, b, c, d, e⟩
  | ⟨a, b, c, d+1, e⟩ => some ⟨a, b, c+1, d, e⟩
  | _ => none

private theorem r2r1_chain : ∀ k, ∀ a d e,
    ⟨a, (0 : ℕ), 1, d + k, e⟩ [fm]⊢* ⟨a + k, 0, 1, d, e + k⟩ := by
  intro k; induction' k with k ih <;> intro a d e
  · ring_nf; finish
  · rw [show d + (k + 1) = (d + k) + 1 from by ring,
        show a + (k + 1) = (a + 1) + k from by ring,
        show e + (k + 1) = (e + 1) + k from by ring]
    step fm; step fm
    exact ih (a + 1) d (e + 1)

private theorem r4_drain : ∀ k, ∀ d e,
    ⟨k, (0 : ℕ), 0, d, e⟩ [fm]⊢* ⟨0, 0, 0, d + 3 * k, e⟩ := by
  intro k; induction' k with k ih <;> intro d e
  · ring_nf; finish
  · rw [show d + 3 * (k + 1) = (d + 3) + 3 * k from by ring]
    step fm; exact ih (d + 3) e

private theorem r5_drain : ∀ k, ∀ d,
    ⟨(0 : ℕ), 0, 0, d + k, k⟩ [fm]⊢* ⟨0, 0, 0, d, 0⟩ := by
  intro k; induction' k with k ih <;> intro d
  · ring_nf; finish
  · have h : fm ⟨(0 : ℕ), 0, 0, (d + k) + 1, k + 1⟩ = some ⟨0, 0, 0, d + k, k⟩ := by
      simp only [fm]
    rw [show d + (k + 1) = (d + k) + 1 from by ring]
    exact stepStar_trans ⟨1, h⟩ (ih d)

private theorem r3_step (a e : ℕ) :
    ⟨a, (0 : ℕ), 1, 0, e⟩ [fm]⊢* ⟨a, 0, 0, 0, e⟩ := by
  refine ⟨1, ?_⟩
  show fm ⟨a, 0, 1, 0, e⟩ = some ⟨a, 0, 0, 0, e⟩
  simp only [fm]

private theorem r6_r2r1_r3 (d : ℕ) :
    ⟨(0 : ℕ), 0, 0, d + 1, 0⟩ [fm]⊢⁺ ⟨d, 0, 0, 0, d⟩ := by
  apply step_stepStar_stepPlus
  · show fm ⟨0, 0, 0, d + 1, 0⟩ = some ⟨0, 0, 1, d, 0⟩; simp only [fm]
  rw [show d = 0 + d from by ring]
  apply stepStar_trans (r2r1_chain d 0 0 0)
  exact r3_step (0 + d) (0 + d)

private theorem main_trans (d : ℕ) :
    ⟨(0 : ℕ), 0, 0, d + 3, 0⟩ [fm]⊢⁺ ⟨0, 0, 0, 2 * d + 4, 0⟩ := by
  rw [show d + 3 = (d + 2) + 1 from by ring]
  apply stepPlus_stepStar_stepPlus (r6_r2r1_r3 (d + 2))
  apply stepStar_trans (r4_drain (d + 2) 0 (d + 2))
  rw [show 0 + 3 * (d + 2) = 2 * (d + 2) + (d + 2) from by ring]
  apply stepStar_trans (r5_drain (d + 2) (2 * (d + 2)))
  rw [show 2 * (d + 2) = 2 * d + 4 from by ring]
  finish

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨0, 0, 0, 3, 0⟩) (by execute fm 1)
  apply progress_nonhalt_simple (fm := fm) (A := ℕ)
    (fun d ↦ ⟨0, 0, 0, d + 3, 0⟩) 0
  intro d; exists 2 * d + 1
  rw [show 2 * d + 1 + 3 = 2 * d + 4 from by ring]
  exact main_trans d

end Sz22_2003_unofficial_1065
