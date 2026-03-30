import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #728: [35/6, 4/55, 143/2, 3/7, 245/13]

Vector representation:
```
-1 -1  1  1  0  0
 2  0 -1  0 -1  0
-1  0  0  0  1  1
 0  1  0 -1  0  0
 0  0  1  2  0 -1
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_728

def Q := ℕ × ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a+1, b+1, c, d, e, f⟩ => some ⟨a, b, c+1, d+1, e, f⟩
  | ⟨a, b, c+1, d, e+1, f⟩ => some ⟨a+2, b, c, d, e, f⟩
  | ⟨a+1, b, c, d, e, f⟩ => some ⟨a, b, c, d, e+1, f+1⟩
  | ⟨a, b, c, d+1, e, f⟩ => some ⟨a, b+1, c, d, e, f⟩
  | ⟨a, b, c, d, e, f+1⟩ => some ⟨a, b, c+1, d+2, e, f⟩
  | _ => none

theorem r2r3_chain : ∀ k, ∀ a d f, ⟨a, 0, k + 1, d, 1, f⟩ [fm]⊢* ⟨a + k + 2, 0, 0, d, 0, f + k⟩ := by
  intro k; induction' k with k ih <;> intro a d f
  · step fm; finish
  · step fm; step fm
    apply stepStar_trans (ih (a + 1) d (f + 1))
    ring_nf; finish

theorem r3_drain : ∀ k, ∀ d e f, ⟨k, 0, 0, d, e, f⟩ [fm]⊢* ⟨0, 0, 0, d, e + k, f + k⟩ := by
  intro k; induction' k with k ih <;> intro d e f
  · exists 0
  · step fm
    apply stepStar_trans (ih d (e + 1) (f + 1))
    ring_nf; finish

theorem r4_chain : ∀ k, ∀ b e f, ⟨0, b, 0, k, e, f⟩ [fm]⊢* ⟨0, b + k, 0, 0, e, f⟩ := by
  intro k; induction' k with k ih <;> intro b e f
  · exists 0
  · step fm
    apply stepStar_trans (ih (b + 1) e f)
    ring_nf; finish

theorem r2r1r1_chain : ∀ k, ∀ c d e f, ⟨0, 2 * k, c + 1, d, e + k, f⟩ [fm]⊢* ⟨0, 0, c + k + 1, d + 2 * k, e, f⟩ := by
  intro k; induction' k with k ih <;> intro c d e f
  · exists 0
  · rw [show 2 * (k + 1) = (2 * k + 1) + 1 from by ring,
        show e + (k + 1) = (e + k) + 1 from by ring]
    step fm; step fm; step fm
    apply stepStar_trans (ih (c + 1) (d + 2) e f)
    ring_nf; finish

theorem main_trans (n : ℕ) :
    ⟨0, 0, n + 1, 2 * n + 2, 1, n * n⟩ [fm]⊢⁺ ⟨0, 0, n + 2, 2 * n + 4, 1, (n + 1) * (n + 1)⟩ := by
  apply stepStar_stepPlus_stepPlus (r2r3_chain n 0 (2 * n + 2) (n * n))
  rw [show 0 + n + 2 = n + 2 from by ring,
      show n * n + n = n * n + n from by ring]
  apply stepPlus_stepStar_stepPlus
  · apply stepStar_stepPlus
    · exact r3_drain (n + 2) (2 * n + 2) 0 (n * n + n)
    · simp [Q]
  rw [show 0 + (n + 2) = n + 2 from by ring,
      show n * n + n + (n + 2) = n * n + 2 * n + 2 from by ring]
  apply stepStar_trans (r4_chain (2 * n + 2) 0 (n + 2) (n * n + 2 * n + 2))
  rw [show 0 + (2 * n + 2) = 2 * (n + 1) from by ring]
  step fm
  rw [show n * n + 2 * n + 1 = (n + 1) * (n + 1) from by ring]
  convert stepStar_trans (r2r1r1_chain (n + 1) 0 2 1 ((n + 1) * (n + 1)))
    (by ring_nf; finish) using 2
  ring_nf

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨0, 0, 1, 2, 1, 0⟩) (by execute fm 2)
  apply progress_nonhalt_simple (fm := fm) (A := ℕ)
    (fun n ↦ ⟨0, 0, n + 1, 2 * n + 2, 1, n * n⟩) 0
  intro n; exact ⟨n + 1, main_trans n⟩

end Sz22_2003_unofficial_728
