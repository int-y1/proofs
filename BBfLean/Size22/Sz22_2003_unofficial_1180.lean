import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #1180: [5/6, 49/2, 44/35, 3/11, 66/7]

Vector representation:
```
-1 -1  1  0  0
-1  0  0  2  0
 2  0 -1 -1  1
 0  1  0  0 -1
 1  1  0 -1  1
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_1180

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a+1, b+1, c, d, e⟩ => some ⟨a, b, c+1, d, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b, c, d+2, e⟩
  | ⟨a, b, c+1, d+1, e⟩ => some ⟨a+2, b, c, d, e+1⟩
  | ⟨a, b, c, d, e+1⟩ => some ⟨a, b+1, c, d, e⟩
  | ⟨a, b, c, d+1, e⟩ => some ⟨a+1, b+1, c, d, e+1⟩
  | _ => none

-- R4 repeated: transfer e to b.
theorem e_to_b : ∀ k, ∀ b d e, ⟨0, b, 0, d, e + k⟩ [fm]⊢* ⟨0, b + k, 0, d, e⟩ := by
  intro k; induction' k with k ih <;> intro b d e
  · exists 0
  · rw [show e + (k + 1) = (e + k) + 1 from by ring]
    step fm
    apply stepStar_trans (ih (b + 1) d e)
    ring_nf; finish

-- Interleave: (R3, R1, R1) repeated j times.
theorem interleave : ∀ j, ∀ c d e,
    ⟨0, 2 * j, c + 1, d + j, e⟩ [fm]⊢* ⟨0, 0, c + j + 1, d, e + j⟩ := by
  intro j; induction' j with j ih <;> intro c d e
  · exists 0
  · rw [show 2 * (j + 1) = (2 * j + 1) + 1 from by ring,
        show d + (j + 1) = (d + j) + 1 from by ring]
    step fm
    step fm
    step fm
    apply stepStar_trans (ih (c + 1) d (e + 1))
    ring_nf; finish

-- Drain: (R3, R2, R2) repeated k+1 times.
theorem drain : ∀ k, ∀ c d e,
    ⟨0, 0, c + k + 1, d + 1, e⟩ [fm]⊢* ⟨0, 0, c, d + 3 * k + 4, e + k + 1⟩ := by
  intro k; induction' k with k ih <;> intro c d e
  · step fm; step fm; step fm; finish
  · rw [show c + (k + 1) + 1 = (c + k + 1) + 1 from by ring]
    step fm
    step fm
    step fm
    rw [show d + 2 + 2 = (d + 3) + 1 from by ring]
    apply stepStar_trans (ih c (d + 3) (e + 1))
    ring_nf; finish

theorem main_transition (n : ℕ) :
    ⟨0, 0, 0, n * n + n + 2, 2 * n⟩ [fm]⊢⁺ ⟨0, 0, 0, n * n + 3 * n + 4, 2 * n + 2⟩ := by
  rw [show (2 * n : ℕ) = 0 + 2 * n from by ring]
  apply stepStar_stepPlus_stepPlus (e_to_b (2 * n) 0 (n * n + n + 2) 0)
  rw [show 0 + 2 * n = 2 * n from by ring,
      show n * n + n + 2 = (n * n + n + 1) + 1 from by ring]
  step fm
  step fm
  rw [show n * n + n + 1 = (n * n + 1) + n from by ring,
      show (1 : ℕ) = 0 + 1 from by ring]
  apply stepStar_trans (interleave n 0 (n * n + 1) 1)
  have hdrain := drain n 0 (n * n) (n + 1)
  rw [show 1 + n = n + 1 from by ring]
  apply stepStar_trans hdrain
  ring_nf; finish

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨0, 0, 0, 4, 2⟩) (by execute fm 6)
  apply progress_nonhalt_simple (fm := fm) (A := ℕ)
    (fun n ↦ ⟨0, 0, 0, (n + 1) * (n + 1) + (n + 1) + 2, 2 * (n + 1)⟩) 0
  intro n
  exists n + 1
  show ⟨0, 0, 0, (n + 1) * (n + 1) + (n + 1) + 2, 2 * (n + 1)⟩ [fm]⊢⁺
       ⟨0, 0, 0, (n + 2) * (n + 2) + (n + 2) + 2, 2 * (n + 2)⟩
  rw [show (n + 2) * (n + 2) + (n + 2) + 2 = (n + 1) * (n + 1) + 3 * (n + 1) + 4 from by ring,
      show 2 * (n + 2) = 2 * (n + 1) + 2 from by ring]
  exact main_transition (n + 1)

end Sz22_2003_unofficial_1180
