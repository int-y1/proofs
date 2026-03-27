import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #311: [154/15, 1/3, 3/7, 125/2, 1/55, 3/5]

Vector representation:
```
 1 -1 -1  1  1
 0 -1  0  0  0
 0  1  0 -1  0
-1  0  3  0  0
 0  0 -1  0 -1
 0  1 -1  0  0
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_311

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a, b+1, c+1, d, e⟩ => some ⟨a+1, b, c, d+1, e+1⟩
  | ⟨a, b+1, c, d, e⟩ => some ⟨a, b, c, d, e⟩
  | ⟨a, b, c, d+1, e⟩ => some ⟨a, b+1, c, d, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b, c+3, d, e⟩
  | ⟨a, b, c+1, d, e+1⟩ => some ⟨a, b, c, d, e⟩
  | ⟨a, b, c+1, d, e⟩ => some ⟨a, b+1, c, d, e⟩
  | _ => none

-- Zip: (k, 1, c, 0, k) ->* (k+c, 0, 0, 0, k+c)
theorem zip : ∀ c k, ⟨k, 1, c, 0, k⟩ [fm]⊢* ⟨k+c, 0, 0, 0, k+c⟩ := by
  intro c; induction' c with c ih <;> intro k
  · step fm; finish
  · step fm; step fm
    apply stepStar_trans (ih _)
    ring_nf; finish

-- Convert a to c: (a+k, 0, c, 0, e) ->* (a, 0, c+3*k, 0, e)
theorem a_to_c : ∀ k a c e, ⟨a+k, 0, c, 0, e⟩ [fm]⊢* ⟨a, 0, c+3*k, 0, e⟩ := by
  intro k; induction' k with k ih <;> intro a c e
  · exists 0
  · rw [show a + (k + 1) = (a + k) + 1 from by ring]
    step fm
    have h := ih a (c + 3) e
    rw [show c + 3 + 3 * k = c + 3 * (k + 1) from by ring] at h
    exact h

-- Cancel c and e: (0, 0, c+k, 0, k) ->* (0, 0, c, 0, 0)
theorem cancel : ∀ k c, ⟨0, 0, c+k, 0, k⟩ [fm]⊢* ⟨0, 0, c, 0, 0⟩ := by
  intro k; induction' k with k ih <;> intro c
  · exists 0
  · rw [show c + (k + 1) = (c + k) + 1 from by ring]
    step fm
    exact ih _

-- Combined: (n, 0, 0, 0, n) ->* (0, 0, 2*n, 0, 0)
theorem phase23 (n : ℕ) : ⟨n, 0, 0, 0, n⟩ [fm]⊢* ⟨0, 0, 2*n, 0, 0⟩ := by
  have h1 := a_to_c n 0 0 n
  simp only [Nat.zero_add] at h1
  apply stepStar_trans h1
  have h2 := cancel n (2*n)
  rw [show 2 * n + n = 3 * n from by ring] at h2
  exact h2

-- Main transition: (0, 0, c+2, 0, 0) ->+ (0, 0, 2*c+2, 0, 0)
theorem main_trans (c : ℕ) : ⟨0, 0, c+2, 0, 0⟩ [fm]⊢⁺ ⟨0, 0, 2*c+2, 0, 0⟩ := by
  apply step_stepStar_stepPlus (by unfold fm; rfl)
  apply stepStar_trans (zip (c+1) 0)
  rw [show 0 + (c + 1) = c + 1 from by ring]
  have h := phase23 (c+1)
  rw [show 2 * (c + 1) = 2 * c + 2 from by ring] at h
  exact h

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨0, 0, 3, 0, 0⟩) (by execute fm 1)
  show ¬halts fm ⟨0, 0, 1+2, 0, 0⟩
  apply progress_nonhalt_simple (fm := fm) (A := ℕ) (fun n ↦ ⟨0, 0, n+2, 0, 0⟩) 1
  intro n
  exact ⟨2*n, main_trans n⟩

end Sz22_2003_unofficial_311
