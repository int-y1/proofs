import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #23: [1/15, 1617/2, 2/39, 65/7, 9/55]

Vector representation:
```
 0 -1 -1  0  0  0
-1  1  0  2  1  0
 1 -1  0  0  0 -1
 0  0  1 -1  0  1
 0  2 -1  0 -1  0
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_23

def Q := ℕ × ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a, b+1, c+1, d, e, f⟩ => some ⟨a, b, c, d, e, f⟩
  | ⟨a+1, b, c, d, e, f⟩ => some ⟨a, b+1, c, d+2, e+1, f⟩
  | ⟨a, b+1, c, d, e, f+1⟩ => some ⟨a+1, b, c, d, e, f⟩
  | ⟨a, b, c, d+1, e, f⟩ => some ⟨a, b, c+1, d, e, f+1⟩
  | ⟨a, b, c+1, d, e+1, f⟩ => some ⟨a, b+2, c, d, e, f⟩
  | _ => none

-- R3 chain: transfer d to c and f
theorem r3_chain : ∀ k, ∀ c e f, ⟨0, 0, c, k, e, f⟩ [fm]⊢* ⟨0, 0, c + k, 0, e, f + k⟩ := by
  intro k; induction' k with k ih <;> intro c e f
  · exists 0
  rw [show c + (k + 1) = c + 1 + k from by ring,
      show f + (k + 1) = f + 1 + k from by ring]
  step fm
  exact ih _ _ _

-- R4-R0-R0 drain: k cycles then final R4
-- (0, 0, 3k+1, 0, e+k+1, f) ->* (0, 2, 0, 0, e, f)
theorem drain_phase : ∀ k, ∀ e f, ⟨0, 0, 3 * k + 1, 0, e + k + 1, f⟩ [fm]⊢* ⟨0, 2, 0, 0, e, f⟩ := by
  intro k; induction' k with k ih <;> intro e f
  · step fm; finish
  -- c = 3(k+1)+1 = 3k+4, e_reg = e+(k+1)+1 = e+k+2
  -- After R4-R0-R0: c = 3k+1, e_reg = e+k+1 = (e+1)+k+1-1 ... tricky
  -- Rewrite to get 3 extra c and 1 extra e
  rw [show 3 * (k + 1) + 1 = (3 * k + 1) + 3 from by ring,
      show e + (k + 1) + 1 = (e + 1) + k + 1 from by ring]
  -- Now goal: (0, 0, (3k+1)+3, 0, (e+1)+k+1, f) ->* (0, 2, 0, 0, e, f)
  step fm; step fm; step fm
  -- After R4-R0-R0: c = 3k+1, e_reg = (e+1)+k+1-1 = e+k+1
  -- But Lean sees: e_reg = e + 1 + k (left-associated)
  -- ih gives: (0, 0, 3k+1, 0, ?e + k + 1, ?f) ->* (0, 2, 0, 0, ?e, ?f)
  -- We need: e + 1 + k = e + k + 1, which is true but Lean might not see it
  -- Let's add a rewrite
  rw [show e + 1 + k = e + k + 1 from by ring]
  exact ih _ _

-- R2-R1 chain: each round converts f to d and e
theorem r2r1_chain : ∀ k, ∀ d e, ⟨0, 2, 0, d, e, k⟩ [fm]⊢* ⟨0, 2, 0, d + 2 * k, e + k, 0⟩ := by
  intro k; induction' k with k ih <;> intro d e
  · exists 0
  step fm; step fm
  apply stepStar_trans (ih _ _)
  ring_nf; finish

-- Main transition: C(n) ⊢⁺ C(2n+2)
-- where C(n) = (1, 0, 0, 3*(n+1), 2*(n+1), 0)
theorem main_trans (n : ℕ) : (⟨1, 0, 0, 3 * (n + 1), 2 * (n + 1), 0⟩ : Q) [fm]⊢⁺
    ⟨1, 0, 0, 3 * (2 * n + 3), 2 * (2 * n + 3), 0⟩ := by
  -- Phase A (3 steps): R1, R3, R0
  step fm; step fm; step fm
  -- Now at: (0, 0, 0, 3*(n+1)+1, 2*(n+1)+1, 1)
  -- Phase B: R3 chain of 3*(n+1)+1 steps
  apply stepStar_trans (r3_chain (3 * (n + 1) + 1) 0 (2 * (n + 1) + 1) 1)
  simp only [Nat.zero_add]
  -- Now at: (0, 0, 3*(n+1)+1, 0, 2*(n+1)+1, 1+(3*(n+1)+1))
  -- Phase C: drain with k = n+1
  -- Need: 2*(n+1)+1 = (n+1) + (n+1) + 1, which is drain_phase's e + k + 1 with e=n+1, k=n+1
  -- Also need f = 3*(n+1)+2 = 1+(3*(n+1)+1)
  rw [show 1 + (3 * (n + 1) + 1) = 3 * (n + 1) + 2 from by ring,
      show 2 * (n + 1) + 1 = (n + 1) + (n + 1) + 1 from by ring]
  apply stepStar_trans (drain_phase (n + 1) (n + 1) (3 * (n + 1) + 2))
  -- Now at: (0, 2, 0, 0, n+1, 3*(n+1)+2)
  -- Phase D: R2-R1 chain of 3*(n+1)+2 rounds
  apply stepStar_trans (r2r1_chain (3 * (n + 1) + 2) 0 (n + 1))
  simp only [Nat.zero_add]
  -- Now at: (0, 2, 0, 2*(3*(n+1)+2), (n+1)+(3*(n+1)+2), 0)
  -- Phase E (3 steps): R3, R0, R2
  rw [show 2 * (3 * (n + 1) + 2) = 6 * n + 10 from by ring,
      show n + 1 + (3 * (n + 1) + 2) = 4 * n + 6 from by ring]
  step fm; step fm; step fm
  ring_nf; finish

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨1, 0, 0, 3, 2, 0⟩) (by execute fm 12)
  apply progress_nonhalt_simple (fm := fm) (A := ℕ)
    (fun n ↦ ⟨1, 0, 0, 3 * (n + 1), 2 * (n + 1), 0⟩) 0
  intro n; exact ⟨2 * n + 2, main_trans n⟩

end Sz22_2003_unofficial_23
