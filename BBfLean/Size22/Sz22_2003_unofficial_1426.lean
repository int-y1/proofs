import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #1426: [7/15, 2/3, 99/14, 5/11, 495/2]

Vector representation:
```
 0 -1 -1  1  0
 1 -1  0  0  0
-1  2  0 -1  1
 0  0  1  0 -1
-1  2  1  0  1
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_1426

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a, b+1, c+1, d, e⟩ => some ⟨a, b, c, d+1, e⟩
  | ⟨a, b+1, c, d, e⟩ => some ⟨a+1, b, c, d, e⟩
  | ⟨a+1, b, c, d+1, e⟩ => some ⟨a, b+2, c, d, e+1⟩
  | ⟨a, b, c, d, e+1⟩ => some ⟨a, b, c+1, d, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b+2, c+1, d, e+1⟩
  | _ => none

-- R1-R1-R3 chain: (k, 2, 2k+1, d, e) ->* (0, 2, 1, d+k, e+k)
theorem r1r1r3_chain : ∀ k d e, ⟨k, (2 : ℕ), 2 * k + 1, d, e⟩ [fm]⊢* ⟨(0 : ℕ), (2 : ℕ), 1, d + k, e + k⟩ := by
  intro k; induction' k with k ih <;> intro d e
  · exists 0
  · rw [show 2 * (k + 1) + 1 = (2 * k + 1) + 2 from by ring]
    step fm; step fm
    rw [show d + 1 + 1 = (d + 1) + 1 from by ring]
    step fm
    apply stepStar_trans (ih (d + 1) (e + 1))
    rw [show d + 1 + k = d + (k + 1) from by ring,
        show e + 1 + k = e + (k + 1) from by ring]
    finish

-- R3-R2-R2 chain: (a+1, 0, 0, d+k, e) ->* (a+k+1, 0, 0, d, e+k)
theorem r3r2r2_chain : ∀ k a d e, ⟨a + 1, (0 : ℕ), (0 : ℕ), d + k, e⟩ [fm]⊢* ⟨a + k + 1, (0 : ℕ), (0 : ℕ), d, e + k⟩ := by
  intro k; induction' k with k ih <;> intro a d e
  · exists 0
  · rw [show d + (k + 1) = (d + k) + 1 from by ring]
    step fm; step fm; step fm
    rw [show a + 1 + 1 = (a + 1) + 1 from by ring]
    apply stepStar_trans (ih (a + 1) d (e + 1))
    rw [show a + 1 + k + 1 = a + (k + 1) + 1 from by ring,
        show e + 1 + k = e + (k + 1) from by ring]
    finish

-- R4 chain: (a, 0, c, 0, e+k) ->* (a, 0, c+k, 0, e)
theorem e_to_c : ∀ k a c e, ⟨a, (0 : ℕ), c, (0 : ℕ), e + k⟩ [fm]⊢* ⟨a, (0 : ℕ), c + k, (0 : ℕ), e⟩ := by
  intro k; induction' k with k ih <;> intro a c e
  · exists 0
  · rw [show e + (k + 1) = (e + k) + 1 from by ring]
    step fm
    apply stepStar_trans (ih a (c + 1) e)
    rw [show c + 1 + k = c + (k + 1) from by ring]
    finish

-- Canonical states: (n+2, 0, 2n+2, 0, 0) for n = 0, 1, 2, ...
theorem main_transition (n : ℕ) :
    ⟨n + 2, (0 : ℕ), 2 * n + 2, (0 : ℕ), (0 : ℕ)⟩ [fm]⊢⁺
    ⟨n + 3, (0 : ℕ), 2 * n + 4, (0 : ℕ), (0 : ℕ)⟩ := by
  rw [show 2 * n + 2 = 2 * (n + 1) + 0 from by ring]
  apply step_stepStar_stepPlus
    (by simp [fm] : (⟨n + 2, 0, 2 * (n + 1) + 0, 0, 0⟩ : Q) [fm]⊢ ⟨n + 1, 2, 2 * (n + 1) + 1, 0, 1⟩)
  apply stepStar_trans (r1r1r3_chain (n + 1) 0 1)
  rw [show 0 + (n + 1) = n + 1 from by ring,
      show 1 + (n + 1) = n + 2 from by ring]
  apply stepStar_trans (step_stepStar
    (by simp [fm] : (⟨0, 2, 1, n + 1, n + 2⟩ : Q) [fm]⊢ ⟨0, 1, 0, n + 2, n + 2⟩))
  apply stepStar_trans (step_stepStar
    (by simp [fm] : (⟨0, 1, 0, n + 2, n + 2⟩ : Q) [fm]⊢ ⟨1, 0, 0, n + 2, n + 2⟩))
  rw [show (1 : ℕ) = 0 + 1 from by ring,
      show (n + 2 : ℕ) = 0 + (n + 2) from by ring]
  apply stepStar_trans (r3r2r2_chain (n + 2) 0 0 (0 + (n + 2)))
  rw [show 0 + (n + 2) + 1 = n + 3 from by ring,
      show 0 + (n + 2) + (n + 2) = 2 * n + 4 from by ring]
  rw [show (2 * n + 4 : ℕ) = 0 + (2 * n + 4) from by ring]
  apply e_to_c (2 * n + 4) (n + 3) 0 0

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨2, 0, 2, 0, 0⟩) (by execute fm 8)
  apply progress_nonhalt_simple (fm := fm) (A := ℕ)
    (fun n ↦ ⟨n + 2, 0, 2 * n + 2, 0, 0⟩) 0
  intro n
  exists n + 1
  exact main_transition n

end Sz22_2003_unofficial_1426
