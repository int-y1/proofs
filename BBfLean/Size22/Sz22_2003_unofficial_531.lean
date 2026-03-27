import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #531: [28/15, 39/22, 35/2, 11/13, 39/7]

Vector representation:
```
 2 -1 -1  1  0  0
-1  1  0  0 -1  1
-1  0  1  1  0  0
 0  0  0  0  1 -1
 0  1  0 -1  0  1
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_531

def Q := ℕ × ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a, b+1, c+1, d, e, f⟩ => some ⟨a+2, b, c, d+1, e, f⟩
  | ⟨a+1, b, c, d, e+1, f⟩ => some ⟨a, b+1, c, d, e, f+1⟩
  | ⟨a+1, b, c, d, e, f⟩ => some ⟨a, b, c+1, d+1, e, f⟩
  | ⟨a, b, c, d, e, f+1⟩ => some ⟨a, b, c, d, e+1, f⟩
  | ⟨a, b, c, d+1, e, f⟩ => some ⟨a, b+1, c, d, e, f+1⟩
  | _ => none

-- R3 repeated k times
theorem r3_chain : ∀ k c d, ⟨k, 0, c, d, 0, f⟩ [fm]⊢* ⟨0, 0, c+k, d+k, 0, f⟩ := by
  intro k; induction' k with k h <;> intro c d
  · exists 0
  rw [show c + (k + 1) = (c + 1) + k from by omega,
      show d + (k + 1) = (d + 1) + k from by omega]
  step fm
  exact h _ _

-- R4 repeated k times
theorem f_to_e : ∀ k c d e, ⟨0, 0, c, d, e, k⟩ [fm]⊢* ⟨0, 0, c, d, e+k, 0⟩ := by
  intro k; induction' k with k h <;> intro c d e
  · exists 0
  rw [show e + (k + 1) = (e + 1) + k from by omega]
  step fm
  exact h _ _ _

-- R5+R1 pair
theorem r5r1 (n D : ℕ) :
    ⟨0, 0, (n+1)+1, D+1, n+1, 0⟩ [fm]⊢* ⟨2, 0, n+1, D+1, n+1, 1⟩ := by
  apply stepStar_trans
    (step_stepStar (by unfold fm; rfl : ⟨0, 0, (n+1)+1, D+1, n+1, 0⟩ [fm]⊢ ⟨0, 1, (n+1)+1, D, n+1, 1⟩))
  exact step_stepStar (by unfold fm; rfl : ⟨0, 1, (n+1)+1, D, n+1, 1⟩ [fm]⊢ ⟨2, 0, n+1, D+1, n+1, 1⟩)

-- R2+R1 pair: (a+1, 0, c+1, d, e+1, f) →* (a+2, 0, c, d+1, e, f+1)
theorem r2r1_pair (a c d e f : ℕ) :
    ⟨a+1, 0, c+1, d, e+1, f⟩ [fm]⊢* ⟨a+2, 0, c, d+1, e, f+1⟩ := by
  apply stepStar_trans
    (step_stepStar (by unfold fm; rfl : ⟨a+1, 0, c+1, d, e+1, f⟩ [fm]⊢ ⟨a, 1, c+1, d, e, f+1⟩))
  exact step_stepStar (by unfold fm; rfl : ⟨a, 1, c+1, d, e, f+1⟩ [fm]⊢ ⟨a+2, 0, c, d+1, e, f+1⟩)

-- R2,R1 chain: k rounds where c=e=k
theorem r2r1_chain : ∀ k, ∀ a d f,
    ⟨a+1, 0, k, d, k, f⟩ [fm]⊢* ⟨a+1+k, 0, 0, d+k, 0, f+k⟩ := by
  intro k; induction' k with k h <;> intro a d f
  · exists 0
  apply stepStar_trans (r2r1_pair a k d k f)
  -- (a+2, 0, k, d+1, k, f+1)
  rw [show a + 1 + (k + 1) = (a + 1) + 1 + k from by omega,
      show d + (k + 1) = (d + 1) + k from by omega,
      show f + (k + 1) = (f + 1) + k from by omega]
  exact h (a+1) (d+1) (f+1)

-- Full cycle
theorem full_cycle (n D : ℕ) :
    ⟨n+2, 0, 0, D, 0, n+1⟩ [fm]⊢⁺ ⟨n+3, 0, 0, D+2*n+3, 0, n+2⟩ := by
  rw [show n + 2 = (n + 1) + 1 from by omega]
  step fm
  apply stepStar_trans (r3_chain (n+1) 1 (D+1) (f := n+1))
  apply stepStar_trans (f_to_e (n+1) (1+(n+1)) ((D+1)+(n+1)) 0)
  suffices ⟨0, 0, (n+1)+1, (D+n+1)+1, n+1, 0⟩ [fm]⊢* ⟨n+3, 0, 0, D+2*n+3, 0, n+2⟩ by
    rw [show 1 + (n + 1) = (n + 1) + 1 from by omega,
        show (D + 1) + (n + 1) = (D + n + 1) + 1 from by omega,
        show 0 + (n + 1) = n + 1 from by omega]
    exact this
  apply stepStar_trans (r5r1 n (D+n+1))
  -- (2, 0, n+1, (D+n+1)+1, n+1, 1)
  -- r2r1_chain (n+1) 1 ((D+n+1)+1) 1
  -- Need: (1+1, 0, n+1, (D+n+1)+1, n+1, 1). 2 = 1+1 ✓ def equal.
  apply stepStar_trans (r2r1_chain (n+1) 1 ((D+n+1)+1) 1)
  rw [show 1 + 1 + (n + 1) = n + 3 from by omega,
      show (D + n + 1) + 1 + (n + 1) = D + 2 * n + 3 from by omega,
      show 1 + (n + 1) = n + 2 from by omega]
  finish

theorem main_trans (n : ℕ) :
    ⟨n+2, 0, 0, (n+1)*(n+1), 0, n+1⟩ [fm]⊢⁺ ⟨n+3, 0, 0, (n+2)*(n+2), 0, n+2⟩ := by
  have h := full_cycle n ((n+1)*(n+1))
  rw [show (n + 1) * (n + 1) + 2 * n + 3 = (n + 2) * (n + 2) from by ring] at h
  exact h

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨3, 0, 0, 4, 0, 2⟩) (by execute fm 10)
  apply progress_nonhalt_simple (fm := fm) (A := ℕ)
    (fun n ↦ ⟨n+2, 0, 0, (n+1)*(n+1), 0, n+1⟩) 1
  intro n; exact ⟨n+1, main_trans n⟩
