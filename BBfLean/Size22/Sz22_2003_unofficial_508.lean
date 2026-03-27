import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #508: [28/15, 3/22, 5/2, 11/7, 196/5]

Vector representation:
```
 2 -1 -1  1  0
-1  1  0  0 -1
-1  0  1  0  0
 0  0  0 -1  1
 2  0 -1  2  0
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_508

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a, b+1, c+1, d, e⟩ => some ⟨a+2, b, c, d+1, e⟩
  | ⟨a+1, b, c, d, e+1⟩ => some ⟨a, b+1, c, d, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b, c+1, d, e⟩
  | ⟨a, b, c, d+1, e⟩ => some ⟨a, b, c, d, e+1⟩
  | ⟨a, b, c+1, d, e⟩ => some ⟨a+2, b, c, d+2, e⟩
  | _ => none

-- Phase A: R3 repeated
theorem a_to_c : ∀ k, ∀ c, ⟨a+k, 0, c, d, 0⟩ [fm]⊢* ⟨a, 0, c+k, d, 0⟩ := by
  intro k; induction' k with k ih <;> intro c
  · exists 0
  rw [show a + (k + 1) = (a + k) + 1 from by ring]
  step fm; apply stepStar_trans (ih _); ring_nf; finish

-- Phase B: R4 repeated
theorem d_to_e : ∀ k, ∀ d, ⟨0, 0, c, d+k, 0⟩ [fm]⊢* ⟨0, 0, c, d, k⟩ := by
  intro k; induction' k with k ih <;> intro d
  · exists 0
  rw [show d + (k + 1) = (d + 1) + k from by ring]
  apply stepStar_trans (ih _); step fm; ring_nf; finish

-- Phase D: (R2, R1) interleaved
theorem r2r1_chain : ∀ k, ∀ a d e, ⟨a+1, 0, k, d, e+k⟩ [fm]⊢*
    ⟨a+1+k, 0, 0, d+k, e⟩ := by
  intro k; induction' k with k ih <;> intro a d e
  · exists 0
  rw [show e + (k + 1) = (e + k) + 1 from by ring]
  step fm; step fm
  rw [show a + 2 = (a + 1) + 1 from by ring,
      show a + 1 + (k + 1) = (a + 1) + 1 + k from by ring,
      show d + (k + 1) = (d + 1) + k from by ring]
  exact ih _ _ _

-- Phase E: R2 repeated
theorem r2_drain : ∀ k, ∀ a b, ⟨a+1+k, b, 0, d, k⟩ [fm]⊢* ⟨a+1, b+k, 0, d, 0⟩ := by
  intro k; induction' k with k ih <;> intro a b
  · exists 0
  rw [show a + 1 + (k + 1) = (a + 1 + k) + 1 from by ring,
      show (k : ℕ) + 1 = k + 1 from rfl]
  step fm
  rw [show b + (k + 1) = (b + 1) + k from by ring]
  exact ih _ _

-- Phase F: (R3, R1) interleaved
theorem r3r1_chain : ∀ k, ∀ a d, ⟨a+1, b+k, 0, d, 0⟩ [fm]⊢* ⟨a+1+k, b, 0, d+k, 0⟩ := by
  intro k; induction' k with k ih <;> intro a d
  · exists 0
  rw [show b + (k + 1) = (b + k) + 1 from by ring]
  step fm; step fm
  rw [show a + 2 = (a + 1) + 1 from by ring,
      show a + 1 + (k + 1) = (a + 1) + 1 + k from by ring,
      show d + (k + 1) = (d + 1) + k from by ring]
  exact ih _ _

-- Main transition: (n+2, 0, 0, 2n+2, 0) ⊢⁺ (n+3, 0, 0, 2n+4, 0)
theorem main_trans (n : ℕ) : ⟨n+2, 0, 0, 2*n+2, 0⟩ [fm]⊢⁺ ⟨n+3, 0, 0, 2*n+4, 0⟩ := by
  -- Phase A: R3 x (n+2): → (0, 0, n+2, 2n+2, 0)
  rw [show n + 2 = 0 + (n + 2) from by ring]
  apply stepStar_stepPlus_stepPlus (a_to_c (n + 2) 0)
  simp only [Nat.zero_add]
  -- Phase B: R4 x (2n+2): → (0, 0, n+2, 0, 2n+2)
  rw [show 2 * n + 2 = 0 + (2 * n + 2) from by ring]
  apply stepStar_stepPlus_stepPlus (d_to_e (2 * n + 2) 0)
  -- Phase C: R5: → (2, 0, n+1, 2, 2n+2)
  rw [show n + 2 = (n + 1) + 1 from by ring]
  step fm
  -- Phase D: (R2, R1) x (n+1): (2, 0, n+1, 2, 2n+2)
  --   r2r1_chain expects (a+1, 0, k, d, e+k)
  --   here: a=1, k=n+1, d=2, e=n+1, so e+k=2n+2
  rw [show 2 * n + 2 = (n + 1) + (n + 1) from by ring]
  apply stepStar_trans (r2r1_chain (n + 1) 1 2 (n + 1))
  -- State: (1+1+(n+1), 0, 0, 2+(n+1), n+1)
  -- Phase E: R2 x (n+1): → (1+1, n+1, 0, 2+(n+1), 0)
  apply stepStar_trans (r2_drain (d := 2 + (n + 1)) (n + 1) 1 0)
  -- State: (1+1, 0+(n+1), 0, 2+(n+1), 0)
  -- Phase F: (R3, R1) x (n+1): → (1+1+(n+1), 0, 0, 2+(n+1)+(n+1), 0)
  apply stepStar_trans (r3r1_chain (b := 0) (n + 1) 1 (2 + (n + 1)))
  ring_nf; finish

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨2, 0, 0, 2, 0⟩) (by execute fm 2)
  apply progress_nonhalt_simple (fm := fm) (A := ℕ)
    (fun n ↦ ⟨n+2, 0, 0, 2*n+2, 0⟩) 0
  intro n; exists n+1; exact main_trans n

end Sz22_2003_unofficial_508
