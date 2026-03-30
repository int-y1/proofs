import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #727: [35/6, 4/55, 143/2, 3/7, 18/13]

Vector representation:
```
-1 -1  1  1  0  0
 2  0 -1  0 -1  0
-1  0  0  0  1  1
 0  1  0 -1  0  0
 1  2  0  0  0 -1
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_727

def Q := ℕ × ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a+1, b+1, c, d, e, f⟩ => some ⟨a, b, c+1, d+1, e, f⟩
  | ⟨a, b, c+1, d, e+1, f⟩ => some ⟨a+2, b, c, d, e, f⟩
  | ⟨a+1, b, c, d, e, f⟩ => some ⟨a, b, c, d, e+1, f+1⟩
  | ⟨a, b, c, d+1, e, f⟩ => some ⟨a, b+1, c, d, e, f⟩
  | ⟨a, b, c, d, e, f+1⟩ => some ⟨a+1, b+2, c, d, e, f⟩
  | _ => none

theorem r4_chain : ∀ k, ∀ b e f, ⟨0, b, 0, k, e, f⟩ [fm]⊢* ⟨0, b + k, 0, 0, e, f⟩ := by
  intro k; induction' k with k ih <;> intro b e f
  · exists 0
  · step fm
    apply stepStar_trans (ih (b + 1) e f)
    ring_nf; finish

theorem r3_drain : ∀ k, ∀ d e f, ⟨k, 0, 0, d, e, f⟩ [fm]⊢* ⟨0, 0, 0, d, e + k, f + k⟩ := by
  intro k; induction' k with k ih <;> intro d e f
  · exists 0
  · step fm
    apply stepStar_trans (ih d (e + 1) (f + 1))
    ring_nf; finish

theorem r2r1r1_chain : ∀ k, ∀ c d f,
    ⟨0, 2 * k + 1, c + 1, d, k + 1, f⟩ [fm]⊢*
    ⟨1, 0, c + k + 1, d + 2 * k + 1, 0, f⟩ := by
  intro k; induction' k with k ih <;> intro c d f
  · step fm; step fm; finish
  · rw [show 2 * (k + 1) + 1 = (2 * k + 1) + 2 from by ring,
        show (k + 1) + 1 = (k + 1) + 1 from rfl]
    step fm; step fm; step fm
    apply stepStar_trans (ih (c + 1) (d + 2) f)
    ring_nf; finish

theorem r3r2_chain : ∀ k, ∀ a d f,
    ⟨a + 1, 0, k, d, 0, f⟩ [fm]⊢* ⟨a + k + 1, 0, 0, d, 0, f + k⟩ := by
  intro k; induction' k with k ih <;> intro a d f
  · exists 0
  · step fm; step fm
    apply stepStar_trans (ih (a + 1) d (f + 1))
    ring_nf; finish

theorem phases (n : ℕ) :
    ⟨0, 2 * n, 0, 0, n + 1, n * n + n + 1⟩ [fm]⊢⁺
    ⟨0, 0, 0, 2 * n + 2, n + 2, n * n + 3 * n + 3⟩ := by
  apply step_stepStar_stepPlus
  · show fm ⟨0, 2 * n, 0, 0, n + 1, n * n + n + 1⟩ = some ⟨1, 2 * n + 2, 0, 0, n + 1, n * n + n⟩
    simp [fm]
  step fm
  apply stepStar_trans (r2r1r1_chain n 0 1 (n * n + n))
  rw [show 0 + n + 1 = n + 1 from by ring,
      show 1 + 2 * n + 1 = 2 * n + 2 from by ring]
  apply stepStar_trans (r3r2_chain (n + 1) 0 (2 * n + 2) (n * n + n))
  rw [show 0 + (n + 1) + 1 = n + 2 from by ring,
      show n * n + n + (n + 1) = n * n + 2 * n + 1 from by ring]
  apply stepStar_trans (r3_drain (n + 2) (2 * n + 2) 0 (n * n + 2 * n + 1))
  rw [show 0 + (n + 2) = n + 2 from by ring,
      show n * n + 2 * n + 1 + (n + 2) = n * n + 3 * n + 3 from by ring]
  finish

theorem main_trans (n : ℕ) :
    ⟨0, 0, 0, 2 * n, n + 1, n * n + n + 1⟩ [fm]⊢⁺
    ⟨0, 0, 0, 2 * n + 2, n + 2, n * n + 3 * n + 3⟩ := by
  apply stepStar_stepPlus_stepPlus (r4_chain (2 * n) 0 (n + 1) (n * n + n + 1))
  rw [show 0 + 2 * n = 2 * n from by ring]
  exact phases n

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨0, 0, 0, 0, 1, 1⟩) (by execute fm 1)
  apply progress_nonhalt_simple (fm := fm) (A := ℕ)
    (fun n ↦ ⟨0, 0, 0, 2 * n, n + 1, n * n + n + 1⟩) 0
  intro n; refine ⟨n + 1, ?_⟩
  convert main_trans n using 2
  ring_nf

end Sz22_2003_unofficial_727
