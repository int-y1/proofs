import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #713: [35/6, 4/55, 121/2, 9/7, 15/11]

Vector representation:
```
-1 -1  1  1  0
 2  0 -1  0 -1
-1  0  0  0  2
 0  2  0 -1  0
 0  1  1  0 -1
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_713

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a+1, b+1, c, d, e⟩ => some ⟨a, b, c+1, d+1, e⟩
  | ⟨a, b, c+1, d, e+1⟩ => some ⟨a+2, b, c, d, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b, c, d, e+2⟩
  | ⟨a, b, c, d+1, e⟩ => some ⟨a, b+2, c, d, e⟩
  | ⟨a, b, c, d, e+1⟩ => some ⟨a, b+1, c+1, d, e⟩
  | _ => none

theorem r4_chain : ∀ k, ∀ b d e, ⟨0, b, 0, d + k, e⟩ [fm]⊢* ⟨0, b + 2 * k, 0, d, e⟩ := by
  intro k; induction' k with k ih <;> intro b d e
  · exists 0
  · rw [show d + (k + 1) = (d + k) + 1 from by ring]
    step fm
    apply stepStar_trans (ih (b + 2) d e)
    ring_nf; finish

theorem r5r2 (b e : ℕ) : ⟨0, b, 0, 0, e + 2⟩ [fm]⊢* ⟨2, b + 1, 0, 0, e⟩ := by
  step fm; step fm; finish

theorem r112_chain : ∀ k, ∀ c d e, ⟨2, 2 * k + 1, c, d, e + k⟩ [fm]⊢* ⟨2, 1, c + k, d + 2 * k, e⟩ := by
  intro k; induction' k with k ih <;> intro c d e
  · exists 0
  · rw [show 2 * (k + 1) + 1 = (2 * k + 1) + 2 from by ring,
        show e + (k + 1) = (e + k) + 1 from by ring]
    step fm; step fm; step fm
    apply stepStar_trans (ih (c + 1) (d + 2) e)
    ring_nf; finish

theorem r2_drain : ∀ k, ∀ a d e, ⟨a, 0, k, d, e + k⟩ [fm]⊢* ⟨a + 2 * k, 0, 0, d, e⟩ := by
  intro k; induction' k with k ih <;> intro a d e
  · exists 0
  · rw [show e + (k + 1) = (e + k) + 1 from by ring]
    step fm
    apply stepStar_trans (ih (a + 2) d e)
    ring_nf; finish

theorem r3_drain : ∀ k, ∀ d e, ⟨k, 0, 0, d, e⟩ [fm]⊢* ⟨0, 0, 0, d, e + 2 * k⟩ := by
  intro k; induction' k with k ih <;> intro d e
  · exists 0
  · step fm
    apply stepStar_trans (ih d (e + 2))
    ring_nf; finish

theorem main_trans (d f : ℕ) :
    ⟨0, 0, 0, d + 1, 2 * d + 5 + f⟩ [fm]⊢⁺ ⟨0, 0, 0, 2 * d + 3, 4 * d + 10 + f⟩ := by
  rw [show d + 1 = 0 + (d + 1) from by ring]
  apply step_stepStar_stepPlus
  · show fm ⟨0, 0, 0, 0 + (d + 1), 2 * d + 5 + f⟩ = some ⟨0, 2, 0, 0 + d, 2 * d + 5 + f⟩
    simp [fm]
  apply stepStar_trans (r4_chain d 2 0 (2 * d + 5 + f))
  rw [show 2 + 2 * d = 2 * d + 2 from by ring,
      show 2 * d + 5 + f = (2 * d + 3 + f) + 2 from by ring]
  apply stepStar_trans (r5r2 (2 * d + 2) (2 * d + 3 + f))
  rw [show 2 * d + 2 + 1 = 2 * (d + 1) + 1 from by ring,
      show 2 * (d + 1) + 1 + f = (d + 2 + f) + (d + 1) from by ring]
  apply stepStar_trans (r112_chain (d + 1) 0 0 (d + 2 + f))
  rw [show 0 + (d + 1) = d + 1 from by ring,
      show 0 + 2 * (d + 1) = 2 * d + 2 from by ring]
  step fm
  rw [show d + 2 + f = f + (d + 2) from by ring,
      show 2 * d + 2 + 1 = 2 * d + 3 from by ring]
  apply stepStar_trans (r2_drain (d + 2) 1 (2 * d + 3) f)
  rw [show 1 + 2 * (d + 2) = 2 * d + 5 from by ring]
  apply stepStar_trans (r3_drain (2 * d + 5) (2 * d + 3) f)
  ring_nf; finish

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨0, 0, 0, 1, 5⟩) (by execute fm 8)
  apply progress_nonhalt_simple (fm := fm) (A := ℕ × ℕ)
    (fun ⟨d, f⟩ ↦ ⟨0, 0, 0, d + 1, 2 * d + 5 + f⟩) ⟨0, 0⟩
  intro ⟨d, f⟩
  refine ⟨⟨2 * d + 2, f + 1⟩, ?_⟩
  convert main_trans d f using 2
  · ring_nf

end Sz22_2003_unofficial_713
