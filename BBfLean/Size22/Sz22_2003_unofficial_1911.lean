import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #1911: [9/385, 28/5, 5/6, 121/2, 5/11]

Vector representation:
```
 0  2 -1 -1 -1
 2  0 -1  1  0
-1 -1  1  0  0
-1  0  0  0  2
 0  0  1  0 -1
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_1911

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a, b, c+1, d+1, e+1⟩ => some ⟨a, b+2, c, d, e⟩
  | ⟨a, b, c+1, d, e⟩ => some ⟨a+2, b, c, d+1, e⟩
  | ⟨a+1, b+1, c, d, e⟩ => some ⟨a, b, c+1, d, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b, c, d, e+2⟩
  | ⟨a, b, c, d, e+1⟩ => some ⟨a, b, c+1, d, e⟩
  | _ => none

theorem r4_drain : ∀ k, ∀ a d e, ⟨a + k, 0, 0, d, e⟩ [fm]⊢* ⟨a, 0, 0, d, e + 2 * k⟩ := by
  intro k; induction' k with k ih <;> intro a d e
  · exists 0
  · rw [show a + (k + 1) = (a + k) + 1 from by ring]
    step fm
    apply stepStar_trans (ih a d (e + 2))
    ring_nf; finish

theorem r5r1_chain : ∀ k, ∀ b d e,
    ⟨0, b, 0, d + k, e + 2 * k + 1⟩ [fm]⊢* ⟨0, b + 2 * k, 0, d, e + 1⟩ := by
  intro k; induction' k with k ih <;> intro b d e
  · exists 0
  · rw [show d + (k + 1) = (d + k) + 1 from by ring,
        show e + 2 * (k + 1) + 1 = (e + 2 * k + 1) + 2 from by ring]
    step fm
    step fm
    show ⟨0, b + 2, 0, d + k, e + 2 * k + 1⟩ [fm]⊢* ⟨0, b + 2 * (k + 1), 0, d, e + 1⟩
    apply stepStar_trans (ih (b + 2) d e)
    ring_nf; finish

theorem r3r2_drain : ∀ k, ∀ a d,
    ⟨a + 1, k, 0, d, 0⟩ [fm]⊢* ⟨a + k + 1, 0, 0, d + k, 0⟩ := by
  intro k; induction' k with k ih <;> intro a d
  · exists 0
  · show ⟨a + 1, k + 1, 0, d, 0⟩ [fm]⊢* ⟨a + (k + 1) + 1, 0, 0, d + (k + 1), 0⟩
    step fm; step fm
    show ⟨a + 2, k, 0, d + 1, 0⟩ [fm]⊢* ⟨a + (k + 1) + 1, 0, 0, d + (k + 1), 0⟩
    rw [show a + 2 = (a + 1) + 1 from by ring,
        show a + (k + 1) + 1 = (a + 1) + k + 1 from by ring,
        show d + (k + 1) = (d + 1) + k from by ring]
    exact ih (a + 1) (d + 1)

theorem tail_phase : ⟨0, 2 * n + 2, 0, 0, 2⟩ [fm]⊢⁺ ⟨2 * n + 4, 0, 0, 2 * n + 3, 0⟩ := by
  step fm; step fm; step fm; step fm
  show ⟨0 + 1, 2 * n + 3, 0, 0, 0⟩ [fm]⊢* ⟨2 * n + 4, 0, 0, 2 * n + 3, 0⟩
  apply stepStar_trans (r3r2_drain (2 * n + 3) 0 0)
  ring_nf; finish

theorem r5r1_full : ⟨0, 0, 0, n + 1, 2 * n + 4⟩ [fm]⊢* ⟨0, 2 * n + 2, 0, 0, 2⟩ := by
  rw [show n + 1 = 0 + (n + 1) from by ring,
      show 2 * n + 4 = 1 + 2 * (n + 1) + 1 from by ring]
  apply stepStar_trans (r5r1_chain (n + 1) 0 0 1)
  ring_nf; finish

theorem main_trans_aux : ⟨0, 0, 0, n + 1, 0 + 2 * (n + 2)⟩ [fm]⊢⁺ ⟨2 * n + 4, 0, 0, 2 * n + 3, 0⟩ := by
  rw [show 0 + 2 * (n + 2) = 2 * n + 4 from by ring]
  apply stepStar_stepPlus_stepPlus r5r1_full
  exact tail_phase

theorem main_trans : ⟨n + 2, 0, 0, n + 1, 0⟩ [fm]⊢⁺ ⟨2 * n + 4, 0, 0, 2 * n + 3, 0⟩ := by
  rw [show n + 2 = 0 + (n + 2) from by ring]
  apply stepStar_stepPlus_stepPlus (r4_drain (n + 2) 0 (n + 1) 0)
  exact main_trans_aux

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨4, 0, 0, 3, 0⟩) (by execute fm 21)
  apply progress_nonhalt_simple (fm := fm) (A := ℕ)
    (fun n ↦ ⟨n + 2, 0, 0, n + 1, 0⟩) 2
  intro n; exists 2 * n + 2
  exact main_trans
