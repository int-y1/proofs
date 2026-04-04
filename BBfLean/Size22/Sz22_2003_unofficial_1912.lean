import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #1912: [9/385, 5/6, 28/5, 121/2, 5/11]

Vector representation:
```
 0  2 -1 -1 -1
-1 -1  1  0  0
 2  0 -1  1  0
-1  0  0  0  2
 0  0  1  0 -1
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_1912

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a, b, c+1, d+1, e+1⟩ => some ⟨a, b+2, c, d, e⟩
  | ⟨a+1, b+1, c, d, e⟩ => some ⟨a, b, c+1, d, e⟩
  | ⟨a, b, c+1, d, e⟩ => some ⟨a+2, b, c, d+1, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b, c, d, e+2⟩
  | ⟨a, b, c, d, e+1⟩ => some ⟨a, b, c+1, d, e⟩
  | _ => none

theorem r4_chain : ∀ a d e, ⟨a, 0, 0, d, e⟩ [fm]⊢* ⟨0, 0, 0, d, e + 2 * a⟩ := by
  intro a; induction' a with a ih <;> intro d e
  · exists 0
  · step fm
    apply stepStar_trans (ih d (e + 2))
    ring_nf; finish

theorem r5r1_chain : ∀ k b e, ⟨0, b, 0, k, e + 2 * k⟩ [fm]⊢* ⟨0, b + 2 * k, 0, 0, e⟩ := by
  intro k; induction' k with k ih <;> intro b e
  · exists 0
  · rw [show e + 2 * (k + 1) = (e + 2 * k) + 1 + 1 from by ring]
    step fm; step fm
    apply stepStar_trans (ih (b + 2) e)
    ring_nf; finish

theorem transition : ∀ b, ⟨0, b + 2, 0, 0, 2⟩ [fm]⊢* ⟨2, b + 2, 0, 1, 0⟩ := by
  intro b; execute fm 6

theorem r2r2r3_chain : ∀ k c d, ⟨2, 2 * k + 2, c, d, 0⟩ [fm]⊢* ⟨2, 0, c + k + 1, d + k + 1, 0⟩ := by
  intro k; induction' k with k ih <;> intro c d
  · step fm; step fm; step fm; finish
  · rw [show 2 * (k + 1) + 2 = (2 * k + 2) + 1 + 1 from by ring]
    step fm; step fm; step fm
    apply stepStar_trans (ih (c + 1) (d + 1))
    ring_nf; finish

theorem r3_chain : ∀ k a d, ⟨a, 0, k, d, 0⟩ [fm]⊢* ⟨a + 2 * k, 0, 0, d + k, 0⟩ := by
  intro k; induction' k with k ih <;> intro a d
  · exists 0
  · step fm
    apply stepStar_trans (ih (a + 2) (d + 1))
    ring_nf; finish

theorem main_trans : ∀ n, ⟨n + 2, 0, 0, n + 1, 0⟩ [fm]⊢⁺ ⟨2 * n + 4, 0, 0, 2 * n + 3, 0⟩ := by
  intro n
  apply stepStar_stepPlus_stepPlus
  · exact r4_chain (n + 2) (n + 1) 0
  apply stepStar_stepPlus_stepPlus
  · rw [show 0 + 2 * (n + 2) = 2 + 2 * (n + 1) from by ring]
    exact r5r1_chain (n + 1) 0 2
  apply stepStar_stepPlus_stepPlus
  · rw [show 0 + 2 * (n + 1) = 2 * n + 2 from by ring,
        show (2 : ℕ) = 0 + 2 from by ring]
    rw [show 2 * n + 2 = 2 * n + 0 + 2 from by ring]
    exact transition (2 * n + 0)
  apply stepStar_stepPlus_stepPlus
  · rw [show 2 * n + 0 + 2 = 2 * n + 2 from by ring]
    exact r2r2r3_chain n 0 1
  rw [show 0 + n + 1 = n + 1 from by ring,
      show 1 + n + 1 = n + 2 from by ring]
  step fm
  apply stepStar_trans (r3_chain n 4 (n + 3))
  ring_nf; finish

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨4, 0, 0, 3, 0⟩) (by execute fm 21)
  apply progress_nonhalt_simple (fm := fm) (A := ℕ)
    (fun n ↦ ⟨n + 2, 0, 0, n + 1, 0⟩) 2
  intro n; exact ⟨2 * n + 2, main_trans n⟩
