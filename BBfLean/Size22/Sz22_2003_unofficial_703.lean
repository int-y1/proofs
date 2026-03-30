import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #703: [35/6, 4/55, 121/2, 3/7, 245/11]

Vector representation:
```
-1 -1  1  1  0
 2  0 -1  0 -1
-1  0  0  0  2
 0  1  0 -1  0
 0  0  1  2 -1
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_703

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a+1, b+1, c, d, e⟩ => some ⟨a, b, c+1, d+1, e⟩
  | ⟨a, b, c+1, d, e+1⟩ => some ⟨a+2, b, c, d, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b, c, d, e+2⟩
  | ⟨a, b, c, d+1, e⟩ => some ⟨a, b+1, c, d, e⟩
  | ⟨a, b, c, d, e+1⟩ => some ⟨a, b, c+1, d+2, e⟩
  | _ => none

theorem r4_chain : ∀ k, ∀ b d e, ⟨0, b, 0, d + k, e⟩ [fm]⊢* ⟨0, b + k, 0, d, e⟩ := by
  intro k; induction' k with k ih <;> intro b d e
  · exists 0
  · rw [show d + (k + 1) = (d + k) + 1 from by ring]
    step fm
    apply stepStar_trans (ih (b + 1) d e)
    ring_nf; finish

theorem r3_chain : ∀ k, ∀ a d e, ⟨a + k, 0, 0, d, e⟩ [fm]⊢* ⟨a, 0, 0, d, e + 2 * k⟩ := by
  intro k; induction' k with k ih <;> intro a d e
  · exists 0
  · rw [show a + (k + 1) = (a + k) + 1 from by ring]
    step fm
    apply stepStar_trans (ih a d (e + 2))
    ring_nf; finish

theorem r2_chain : ∀ k, ∀ a c d e, ⟨a, 0, c + k, d, e + k⟩ [fm]⊢* ⟨a + 2 * k, 0, c, d, e⟩ := by
  intro k; induction' k with k ih <;> intro a c d e
  · exists 0
  · rw [show c + (k + 1) = (c + k) + 1 from by ring,
        show e + (k + 1) = (e + k) + 1 from by ring]
    step fm
    apply stepStar_trans (ih (a + 2) c d e)
    ring_nf; finish

theorem r2r1r1_chain : ∀ k, ∀ c d e, ⟨0, 2 * k, c + 1, d, e + k⟩ [fm]⊢* ⟨0, 0, c + k + 1, d + 2 * k, e⟩ := by
  intro k; induction' k with k ih <;> intro c d e
  · exists 0
  · rw [show 2 * (k + 1) = (2 * k + 1) + 1 from by ring,
        show e + (k + 1) = (e + k) + 1 from by ring]
    step fm
    rw [show 2 * k + 1 = (2 * k) + 1 from by ring]
    step fm; step fm
    apply stepStar_trans (ih (c + 1) (d + 2) e)
    ring_nf; finish

theorem main_trans (n : ℕ) :
    ⟨0, 0, 0, 2 * n + 2, n * n + 3 * n + 4⟩ [fm]⊢⁺ ⟨0, 0, 0, 2 * n + 4, n * n + 5 * n + 8⟩ := by
  rw [show 2 * n + 2 = 0 + (2 * n + 2) from by ring]
  apply step_stepStar_stepPlus
  · show fm ⟨0, 0, 0, 0 + (2 * n + 2), n * n + 3 * n + 4⟩ = some ⟨0, 1, 0, 0 + (2 * n + 1), n * n + 3 * n + 4⟩
    simp [fm]
  apply stepStar_trans (r4_chain (2 * n + 1) 1 0 (n * n + 3 * n + 4))
  rw [show 1 + (2 * n + 1) = 2 * (n + 1) from by ring,
      show n * n + 3 * n + 4 = (n * n + 3 * n + 3) + 1 from by ring]
  step fm
  rw [show n * n + 3 * n + 3 = (n * n + 2 * n + 2) + (n + 1) from by ring]
  apply stepStar_trans (r2r1r1_chain (n + 1) 0 2 (n * n + 2 * n + 2))
  rw [show 0 + (n + 1) + 1 = 0 + (n + 2) from by ring,
      show 2 + 2 * (n + 1) = 2 * n + 4 from by ring,
      show n * n + 2 * n + 2 = (n * n + n) + (n + 2) from by ring]
  apply stepStar_trans (r2_chain (n + 2) 0 0 (2 * n + 4) (n * n + n))
  rw [show 0 + 2 * (n + 2) = 0 + (2 * n + 4) from by ring]
  apply stepStar_trans (r3_chain (2 * n + 4) 0 (2 * n + 4) (n * n + n))
  rw [show n * n + n + 2 * (2 * n + 4) = n * n + 5 * n + 8 from by ring]
  finish

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨0, 0, 0, 2, 4⟩) (by execute fm 5)
  apply progress_nonhalt_simple (fm := fm) (A := ℕ)
    (fun n ↦ ⟨0, 0, 0, 2 * n + 2, n * n + 3 * n + 4⟩) 0
  intro n; refine ⟨n + 1, ?_⟩
  convert main_trans n using 2
  ring_nf

end Sz22_2003_unofficial_703
