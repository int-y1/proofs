import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #521: [28/15, 3/242, 35/2, 11/7, 6/5]

Vector representation:
```
 2 -1 -1  1  0
-1  1  0  0 -2
-1  0  1  1  0
 0  0  0 -1  1
 1  1 -1  0  0
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_521

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a, b+1, c+1, d, e⟩ => some ⟨a+2, b, c, d+1, e⟩
  | ⟨a+1, b, c, d, e+2⟩ => some ⟨a, b+1, c, d, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b, c+1, d+1, e⟩
  | ⟨a, b, c, d+1, e⟩ => some ⟨a, b, c, d, e+1⟩
  | ⟨a, b, c+1, d, e⟩ => some ⟨a+1, b+1, c, d, e⟩
  | _ => none

-- R2+R1 chain: k rounds of (R2, R1)
theorem r2r1_chain : ∀ k, ∀ a d, ⟨a+1, 0, k, d, e+2*k⟩ [fm]⊢* ⟨a+k+1, 0, 0, d+k, e⟩ := by
  intro k; induction' k with k ih <;> intro a d
  · exists 0
  rw [Nat.mul_succ, ← Nat.add_assoc]
  step fm; step fm
  apply stepStar_trans (ih _ _)
  ring_nf; finish

-- R2 drain: k+1 rounds of R2 with c=0
theorem r2_drain : ∀ k, ∀ a b, ⟨a+1+k, b, 0, d, e+2+2*k⟩ [fm]⊢* ⟨a, b+k+1, 0, d, e⟩ := by
  intro k; induction' k with k ih <;> intro a b
  · step fm; finish
  rw [Nat.mul_succ, ← Nat.add_assoc, ← Nat.add_assoc]
  step fm
  apply stepStar_trans (ih _ _)
  ring_nf; finish

-- R3+R1 chain: k rounds of (R3, R1) with e=1
theorem r3r1_chain : ∀ k, ∀ a d, ⟨a+1, k, 0, d, 1⟩ [fm]⊢* ⟨a+k+1, 0, 0, d+2*k, 1⟩ := by
  intro k; induction' k with k ih <;> intro a d
  · exists 0
  rw [show (k + 1) = k + 1 from rfl]
  step fm; step fm
  apply stepStar_trans (ih _ _)
  ring_nf; finish

-- R3 drain: k+1 rounds of R3 with b=0, e=1
theorem r3_drain : ∀ k, ∀ c d, ⟨k+1, 0, c, d, 1⟩ [fm]⊢* ⟨0, 0, c+k+1, d+k+1, 1⟩ := by
  intro k; induction' k with k ih <;> intro c d
  · step fm; finish
  rw [show (k + 1) + 1 = (k + 1) + 1 from rfl]
  step fm
  apply stepStar_trans (ih _ _)
  ring_nf; finish

-- R4 drain: convert d to e
theorem d_to_e : ∀ k, ∀ e, ⟨0, 0, c, k, e⟩ [fm]⊢* ⟨0, 0, c, 0, e+k⟩ := by
  intro k; induction' k with k ih <;> intro e
  · exists 0
  step fm
  apply stepStar_trans (ih _)
  ring_nf; finish

-- Main transition: (0, 0, n+2, 0, 4n+5) →⁺ (0, 0, n+3, 0, 4n+9)
theorem main_trans (n : ℕ) : (⟨0, 0, n+2, 0, 4*n+5⟩ : Q) [fm]⊢⁺ ⟨0, 0, n+3, 0, 4*n+9⟩ := by
  -- R5, R1
  step fm; step fm
  -- R2+R1 chain: n rounds
  rw [show 4 * n + 5 = (2 * n + 5) + 2 * n from by ring]
  apply stepStar_trans (r2r1_chain n 2 1 (e := 2*n+5))
  -- R2 drain: n+1 rounds
  rw [show 2 + n + 1 = 1 + 1 + (n + 1) from by ring,
      show 2 * n + 5 = 1 + 2 + 2 * (n + 1) from by ring]
  apply stepStar_trans (r2_drain (n+1) 1 0 (e := 1))
  -- R3
  rw [show 0 + (n + 1) + 1 = n + 2 from by ring]
  step fm
  -- R1
  rw [show n + 2 = (n + 1) + 1 from by ring]
  step fm
  -- R3+R1 chain: n+1 rounds
  rw [show (2 : ℕ) = 1 + 1 from by ring,
      show 1 + n + 1 + 1 = n + 3 from by ring]
  apply stepStar_trans (r3r1_chain (n+1) 1 (n+3))
  -- R3 drain
  rw [show 1 + (n + 1) + 1 = (n + 2) + 1 from by ring,
      show n + 3 + 2 * (n + 1) = 3 * n + 5 from by ring]
  apply stepStar_trans (r3_drain (n+2) 0 (3*n+5))
  -- R4 drain
  rw [show 0 + (n + 2) + 1 = n + 3 from by ring,
      show 3 * n + 5 + (n + 2) + 1 = 4 * n + 8 from by ring]
  apply stepStar_trans (d_to_e (4*n+8) (c := n+3) 1)
  ring_nf; finish

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨0, 0, 2, 0, 5⟩) (by execute fm 11)
  apply progress_nonhalt_simple (fm := fm) (A := ℕ)
    (fun n ↦ ⟨0, 0, n+2, 0, 4*n+5⟩) 0
  intro n; exact ⟨n+1, main_trans n⟩
