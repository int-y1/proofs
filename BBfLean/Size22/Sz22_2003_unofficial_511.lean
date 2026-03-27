import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #511: [28/15, 3/22, 65/2, 11/7, 154/13]

Vector representation:
```
 2 -1 -1  1  0  0
-1  1  0  0 -1  0
-1  0  1  0  0  1
 0  0  0 -1  1  0
 1  0  0  1  1 -1
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_511

def Q := ℕ × ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a, b+1, c+1, d, e, f⟩ => some ⟨a+2, b, c, d+1, e, f⟩
  | ⟨a+1, b, c, d, e+1, f⟩ => some ⟨a, b+1, c, d, e, f⟩
  | ⟨a+1, b, c, d, e, f⟩ => some ⟨a, b, c+1, d, e, f+1⟩
  | ⟨a, b, c, d+1, e, f⟩ => some ⟨a, b, c, d, e+1, f⟩
  | ⟨a, b, c, d, e, f+1⟩ => some ⟨a+1, b, c, d+1, e+1, f⟩
  | _ => none

-- R3 chain: drain a, build c and f (requires b=0, e=0)
theorem a_to_cf (a k c d f : ℕ) :
    ⟨a+k, 0, c, d, 0, f⟩ [fm]⊢* ⟨a, 0, c+k, d, 0, f+k⟩ := by
  have many_step : ∀ k c f, ⟨a+k, 0, c, d, 0, f⟩ [fm]⊢* ⟨a, 0, c+k, d, 0, f+k⟩ := by
    intro k; induction' k with k h <;> intro c f
    · exists 0
    rw [show a + (k + 1) = (a + k) + 1 from by ring]
    step fm
    apply stepStar_trans (h _ _); ring_nf; finish
  exact many_step k c f

-- R4 chain: drain d, build e (requires a=0, b=0)
theorem d_to_e (c d k e f : ℕ) :
    ⟨0, 0, c, d+k, e, f⟩ [fm]⊢* ⟨0, 0, c, d, e+k, f⟩ := by
  have many_step : ∀ k d e, ⟨0, 0, c, d+k, e, f⟩ [fm]⊢* ⟨0, 0, c, d, e+k, f⟩ := by
    intro k; induction' k with k h <;> intro d e
    · exists 0
    rw [show d + (k + 1) = (d + k) + 1 from by ring]
    step fm
    apply stepStar_trans (h _ _); ring_nf; finish
  exact many_step k d e

-- R2+R1 chain: (a+1, 0, c+k, d, e+k, f) →* (a+k+1, 0, c, d+k, e, f)
theorem r2r1_chain (e a k c d f : ℕ) :
    ⟨a+1, 0, c+k, d, e+k, f⟩ [fm]⊢* ⟨a+k+1, 0, c, d+k, e, f⟩ := by
  have many_step : ∀ k a c d, ⟨a+1, 0, c+k, d, e+k, f⟩ [fm]⊢* ⟨a+k+1, 0, c, d+k, e, f⟩ := by
    intro k; induction' k with k h <;> intro a c d
    · exists 0
    rw [show c + (k + 1) = (c + k) + 1 from by ring,
        show e + (k + 1) = (e + k) + 1 from by ring]
    step fm; step fm
    apply stepStar_trans (h _ _ _); ring_nf; finish
  exact many_step k a c d

-- R2 chain: drain e, build b (requires b=0, c=0)
theorem r2_chain (d a k b f : ℕ) :
    ⟨a+k, b, 0, d, k, f⟩ [fm]⊢* ⟨a, b+k, 0, d, 0, f⟩ := by
  have many_step : ∀ k a b, ⟨a+k, b, 0, d, k, f⟩ [fm]⊢* ⟨a, b+k, 0, d, 0, f⟩ := by
    intro k; induction' k with k h <;> intro a b
    · exists 0
    rw [show a + (k + 1) = (a + k) + 1 from by ring]
    step fm
    apply stepStar_trans (h _ _); ring_nf; finish
  exact many_step k a b

-- R3+R1 chain: (a+1, b+k, 0, d, 0, f) →* (a+k+1, b, 0, d+k, 0, f+k)
theorem r3r1_chain (b a k d f : ℕ) :
    ⟨a+1, b+k, 0, d, 0, f⟩ [fm]⊢* ⟨a+k+1, b, 0, d+k, 0, f+k⟩ := by
  have many_step : ∀ k a d f, ⟨a+1, b+k, 0, d, 0, f⟩ [fm]⊢* ⟨a+k+1, b, 0, d+k, 0, f+k⟩ := by
    intro k; induction' k with k h <;> intro a d f
    · exists 0
    rw [show b + (k + 1) = (b + k) + 1 from by ring]
    step fm; step fm
    apply stepStar_trans (h _ _ _); ring_nf; finish
  exact many_step k a d f

-- Combine all phases into main transition
-- C(n) = (n+2, 0, 0, 2*(n+1), 0, n*(n+1))
-- C(n+1) = (n+3, 0, 0, 2*(n+2), 0, (n+1)*(n+2))
theorem main_trans (n : ℕ) :
    ⟨n+2, 0, 0, 2*(n+1), 0, n*(n+1)⟩ [fm]⊢⁺ ⟨n+3, 0, 0, 2*(n+2), 0, (n+1)*(n+2)⟩ := by
  -- Phase 1: R3 chain (n+2 times): drain a, build c and f
  rw [show n + 2 = 0 + (n + 2) from by ring]
  apply stepStar_stepPlus_stepPlus (a_to_cf 0 (n + 2) 0 (2 * (n + 1)) (n * (n + 1)))
  simp only [Nat.zero_add]
  -- Phase 2: R4 chain (2(n+1) times): drain d, build e
  rw [show 2 * (n + 1) = 0 + (2 * (n + 1)) from by ring]
  apply stepStar_stepPlus_stepPlus (d_to_e (n + 2) 0 (2 * (n + 1)) 0 (n * (n + 1) + (n + 2)))
  simp only [Nat.zero_add]
  -- Phase 3: R5 step
  have r5 : (⟨0, 0, n + 2, 0, 2 * (n + 1), n * (n + 1) + (n + 2)⟩ : Q) [fm]⊢
            ⟨1, 0, n + 2, 1, 2 * (n + 1) + 1, n * (n + 1) + (n + 1)⟩ := by
    rw [show n * (n + 1) + (n + 2) = (n * (n + 1) + (n + 1)) + 1 from by ring]
    unfold fm; rfl
  apply step_stepStar_stepPlus r5
  -- Phase 4: R2+R1 chain (n+2 times)
  rw [show n + 2 = 0 + (n + 2) from by ring,
      show 2 * (n + 1) + 1 = (n + 1) + (n + 2) from by ring,
      show (1 : ℕ) = 0 + 1 from by ring]
  apply stepStar_trans (r2r1_chain (n + 1) 0 (n + 2) 0 1 (n * (n + 1) + (n + 1)))
  -- Phase 5: R2 chain (n+1 times)
  rw [show 0 + (n + 2) + 1 = 2 + (n + 1) from by ring,
      show 1 + (n + 2) = n + 3 from by ring]
  apply stepStar_trans (r2_chain (n + 3) 2 (n + 1) 0 (n * (n + 1) + (n + 1)))
  simp only [Nat.zero_add]
  -- Phase 6: R3+R1 chain (n+1 times)
  have h6 : ⟨2, n + 1, 0, n + 3, 0, n * (n + 1) + (n + 1)⟩ [fm]⊢*
             ⟨(n + 1) + 2, 0, 0, (n + 3) + (n + 1), 0, n * (n + 1) + (n + 1) + (n + 1)⟩ := by
    have := r3r1_chain 0 1 (n + 1) (n + 3) (n * (n + 1) + (n + 1))
    rw [show 1 + (n + 1) + 1 = (n + 1) + 2 from by ring] at this
    simp only [Nat.zero_add] at this; exact this
  apply stepStar_trans h6
  ring_nf; finish

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨2, 0, 0, 2, 0, 0⟩) (by execute fm 4)
  apply progress_nonhalt_simple (fm := fm) (A := ℕ)
    (fun n ↦ ⟨n+2, 0, 0, 2*(n+1), 0, n*(n+1)⟩) 0
  intro n; exists n + 1; exact main_trans n

end Sz22_2003_unofficial_511
