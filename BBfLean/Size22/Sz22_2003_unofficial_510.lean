import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #510: [28/15, 3/22, 5/2, 11/7, 42/5]

Vector representation:
```
 2 -1 -1  1  0
-1  1  0  0 -1
-1  0  1  0  0
 0  0  0 -1  1
 1  1 -1  1  0
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_510

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a, b+1, c+1, d, e⟩ => some ⟨a+2, b, c, d+1, e⟩
  | ⟨a+1, b, c, d, e+1⟩ => some ⟨a, b+1, c, d, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b, c+1, d, e⟩
  | ⟨a, b, c, d+1, e⟩ => some ⟨a, b, c, d, e+1⟩
  | ⟨a, b, c+1, d, e⟩ => some ⟨a+1, b+1, c, d+1, e⟩
  | _ => none

-- R3 chain: transfer a to c (when b=0, e=0)
theorem a_to_c (a k c d : ℕ) : ⟨a+k, 0, c, d, 0⟩ [fm]⊢* ⟨a, 0, c+k, d, 0⟩ := by
  have many_step : ∀ k c, ⟨a+k, 0, c, d, 0⟩ [fm]⊢* ⟨a, 0, c+k, d, 0⟩ := by
    intro k; induction' k with k h <;> intro c
    · exists 0
    rw [show a + (k + 1) = (a + k) + 1 from by ring]
    step fm
    apply stepStar_trans (h _); ring_nf; finish
  exact many_step k c

-- R4 chain: transfer d to e (when a=0, b=0)
theorem d_to_e (c d k e : ℕ) : ⟨0, 0, c, d+k, e⟩ [fm]⊢* ⟨0, 0, c, d, e+k⟩ := by
  have many_step : ∀ k d e, ⟨0, 0, c, d+k, e⟩ [fm]⊢* ⟨0, 0, c, d, e+k⟩ := by
    intro k; induction' k with k h <;> intro d e
    · exists 0
    rw [show d + (k + 1) = (d + k) + 1 from by ring]
    step fm
    apply stepStar_trans (h _ _); ring_nf; finish
  exact many_step k d e

-- R2+R1 chain: (a+1, 0, k, d, e+k) →* (a+k+1, 0, 0, d+k, e)
theorem r2r1_chain (e a k d : ℕ) : ⟨a+1, 0, k, d, e+k⟩ [fm]⊢* ⟨a+k+1, 0, 0, d+k, e⟩ := by
  have many_step : ∀ k a d, ⟨a+1, 0, k, d, e+k⟩ [fm]⊢* ⟨a+k+1, 0, 0, d+k, e⟩ := by
    intro k; induction' k with k h <;> intro a d
    · exists 0
    rw [show e + (k + 1) = (e + k) + 1 from by ring]
    step fm
    rw [show k + 1 = k + 1 from rfl]
    step fm
    apply stepStar_trans (h _ _); ring_nf; finish
  exact many_step k a d

-- R2 chain: consume e, grow b (when c=0)
theorem r2_chain (d a k b : ℕ) : ⟨a+k, b, 0, d, k⟩ [fm]⊢* ⟨a, b+k, 0, d, 0⟩ := by
  have many_step : ∀ k a b, ⟨a+k, b, 0, d, k⟩ [fm]⊢* ⟨a, b+k, 0, d, 0⟩ := by
    intro k; induction' k with k h <;> intro a b
    · exists 0
    rw [show a + (k + 1) = (a + k) + 1 from by ring]
    step fm
    apply stepStar_trans (h _ _); ring_nf; finish
  exact many_step k a b

-- R3+R1 chain: (a+1, b+k, 0, d, 0) →* (a+k+1, b, 0, d+k, 0)
theorem r3r1_chain (b a k d : ℕ) : ⟨a+1, b+k, 0, d, 0⟩ [fm]⊢* ⟨a+k+1, b, 0, d+k, 0⟩ := by
  have many_step : ∀ k a d, ⟨a+1, b+k, 0, d, 0⟩ [fm]⊢* ⟨a+k+1, b, 0, d+k, 0⟩ := by
    intro k; induction' k with k h <;> intro a d
    · exists 0
    rw [show b + (k + 1) = (b + k) + 1 from by ring]
    step fm
    rw [show (b + k) + 1 = (b + k) + 1 from rfl]
    step fm
    apply stepStar_trans (h _ _); ring_nf; finish
  exact many_step k a d

-- Main transition: (n+2, 0, 0, 2*n+2, 0) →⁺ (n+3, 0, 0, 2*n+4, 0)
theorem main_trans (n : ℕ) : ⟨n+2, 0, 0, 2*n+2, 0⟩ [fm]⊢⁺ ⟨n+3, 0, 0, 2*n+4, 0⟩ := by
  -- Phase 1: R3 chain
  rw [show n + 2 = 0 + (n + 2) from by ring]
  apply stepStar_stepPlus_stepPlus (a_to_c 0 (n + 2) 0 (2 * n + 2))
  simp only [Nat.zero_add]
  -- Phase 2: R4 chain
  rw [show 2 * n + 2 = 0 + (2 * n + 2) from by ring]
  apply stepStar_stepPlus_stepPlus (d_to_e (n + 2) 0 (2 * n + 2) 0)
  simp only [Nat.zero_add]
  -- Phase 3: R5: (0, 0, n+2, 0, 2n+2) → (1, 1, n+1, 1, 2n+2)
  rw [show n + 2 = (n + 1) + 1 from by ring]
  apply step_stepPlus_stepPlus (by unfold fm; rfl)
  simp only [Nat.succ_eq_add_one, Nat.reduceAdd]
  -- Phase 4: R1: (1, 1, n+1, 1, 2n+2) → (3, 0, n, 2, 2n+2)
  apply step_stepStar_stepPlus (by unfold fm; rfl)
  simp only [Nat.reduceAdd]
  -- Phase 5: R2+R1 chain: (3, 0, n, 2, 2n+2) →* (n+3, 0, 0, n+2, n+2)
  rw [show 2 * n + 2 = (n + 2) + n from by ring,
      show (3 : ℕ) = 2 + 1 from by ring]
  apply stepStar_trans (r2r1_chain (n + 2) 2 n 2)
  -- Phase 6: R2 chain: (n+3, 0, 0, n+2, n+2) →* (1, n+2, 0, n+2, 0)
  rw [show 2 + n + 1 = 1 + (n + 2) from by ring]
  apply stepStar_trans (r2_chain (2 + n) 1 (n + 2) 0)
  -- Phase 7: R3+R1 chain: (1, n+2, 0, n+2, 0) →* (n+3, 0, 0, 2n+4, 0)
  rw [show (1 : ℕ) = 0 + 1 from by ring]
  apply stepStar_trans (r3r1_chain 0 0 (n + 2) (2 + n))
  ring_nf; finish

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨2, 0, 0, 2, 0⟩) (by execute fm 4)
  apply progress_nonhalt_simple (fm := fm) (A := ℕ)
    (fun n ↦ ⟨n+2, 0, 0, 2*n+2, 0⟩) 0
  intro n; exists n + 1; exact main_trans n

end Sz22_2003_unofficial_510
