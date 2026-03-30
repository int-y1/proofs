import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #870: [4/15, 1/14, 33/2, 7/3, 50/77]

Vector representation:
```
 2 -1 -1  0  0
-1  0  0 -1  0
-1  1  0  0  1
 0 -1  0  1  0
 1  0  2 -1 -1
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_870

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a, b+1, c+1, d, e⟩ => some ⟨a+2, b, c, d, e⟩
  | ⟨a+1, b, c, d+1, e⟩ => some ⟨a, b, c, d, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b+1, c, d, e+1⟩
  | ⟨a, b+1, c, d, e⟩ => some ⟨a, b, c, d+1, e⟩
  | ⟨a, b, c, d+1, e+1⟩ => some ⟨a+1, b, c+2, d, e⟩
  | _ => none

-- R3 repeated: (a+k, b, 0, 0, e) →* (a, b+k, 0, 0, e+k)
theorem a_to_b : ∀ k, ∀ b e, ⟨a + k, b, 0, 0, e⟩ [fm]⊢* ⟨a, b + k, 0, 0, e + k⟩ := by
  intro k; induction' k with k ih <;> intro b e
  · exists 0
  · rw [show a + (k + 1) = (a + k) + 1 from by ring]
    step fm
    apply stepStar_trans (ih (b + 1) (e + 1))
    ring_nf; finish

-- R4 repeated: (0, b+k, 0, d, e) →* (0, b, 0, d+k, e)
theorem b_to_d : ∀ k, ∀ d, ⟨0, b + k, 0, d, e⟩ [fm]⊢* ⟨0, b, 0, d + k, e⟩ := by
  intro k; induction' k with k ih <;> intro d
  · exists 0
  · rw [show b + (k + 1) = (b + k) + 1 from by ring]
    step fm
    apply stepStar_trans (ih (d + 1))
    ring_nf; finish

-- R5/R2 interleave for odd d: (0, 0, c, 2m+1, m+1+f) →* (1, 0, c+2m+2, 0, f)
theorem de_drain : ∀ m, ∀ c f, ⟨0, 0, c, 2 * m + 1, m + 1 + f⟩ [fm]⊢* ⟨1, 0, c + 2 * m + 2, 0, f⟩ := by
  intro m; induction' m with m ih <;> intro c f
  · rw [show 2 * 0 + 1 = 0 + 1 from by ring, show 0 + 1 + f = f + 1 from by ring]
    step fm
    ring_nf; finish
  · rw [show 2 * (m + 1) + 1 = (2 * m + 2) + 1 from by ring,
        show (m + 1) + 1 + f = (m + 1 + f) + 1 from by ring]
    step fm
    step fm
    apply stepStar_trans (ih (c + 2) f)
    ring_nf; finish

-- R3/R1 spiral: (a+1, 0, n, 0, e) →* (a+1+n, 0, 0, 0, e+n)
theorem spiral : ∀ n, ∀ a e, ⟨a + 1, 0, n, 0, e⟩ [fm]⊢* ⟨a + 1 + n, 0, 0, 0, e + n⟩ := by
  intro n; induction' n with n ih <;> intro a e
  · exists 0
  · step fm; step fm
    apply stepStar_trans (ih (a + 1) (e + 1))
    ring_nf; finish

-- Main transition: (2k+3, 0, 0, 0, e) →⁺ (2k+5, 0, 0, 0, e+3k+5)
theorem main_trans : ⟨2 * k + 3, 0, 0, 0, e⟩ [fm]⊢⁺ ⟨2 * k + 5, 0, 0, 0, e + 3 * k + 5⟩ := by
  rw [show 2 * k + 3 = (2 * k + 2) + 1 from by ring]
  apply step_stepStar_stepPlus (by unfold fm; rfl : (⟨(2 * k + 2) + 1, 0, 0, 0, e⟩ : Q) [fm]⊢ ⟨2 * k + 2, 1, 0, 0, e + 1⟩)
  rw [show (2 * k + 2 : ℕ) = 0 + (2 * k + 2) from by ring]
  apply stepStar_trans (a_to_b (2 * k + 2) 1 (e + 1) (a := 0))
  rw [show 1 + (2 * k + 2) = 0 + (2 * k + 3) from by ring]
  apply stepStar_trans (b_to_d (2 * k + 3) 0 (b := 0) (e := e + 1 + (2 * k + 2)))
  rw [show 0 + (2 * k + 3) = 2 * (k + 1) + 1 from by ring,
      show e + 1 + (2 * k + 2) = (k + 1) + 1 + (e + k + 1) from by ring]
  apply stepStar_trans (de_drain (k + 1) 0 (e + k + 1))
  rw [show 0 + 2 * (k + 1) + 2 = 2 * k + 4 from by ring]
  apply stepStar_trans (spiral (2 * k + 4) 0 (e + k + 1))
  ring_nf; finish

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨3, 0, 0, 0, 2⟩) (by execute fm 7)
  apply progress_nonhalt_simple (fm := fm) (A := ℕ × ℕ)
    (fun ⟨k, e⟩ ↦ ⟨2 * k + 3, 0, 0, 0, e⟩) ⟨0, 2⟩
  intro ⟨k, e⟩; exists ⟨k + 1, e + 3 * k + 5⟩
  show ⟨2 * k + 3, 0, 0, 0, e⟩ [fm]⊢⁺ ⟨2 * (k + 1) + 3, 0, 0, 0, e + 3 * k + 5⟩
  rw [show 2 * (k + 1) + 3 = 2 * k + 5 from by ring]
  exact main_trans
