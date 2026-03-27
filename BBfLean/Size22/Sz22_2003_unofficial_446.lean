import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #446: [28/15, 1/154, 3/2, 121/3, 50/11]

Vector representation:
```
 2 -1 -1  1  0
-1  0  0 -1 -1
-1  1  0  0  0
 0 -1  0  0  2
 1  0  2  0 -1
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_446

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a, b+1, c+1, d, e⟩ => some ⟨a+2, b, c, d+1, e⟩
  | ⟨a+1, b, c, d+1, e+1⟩ => some ⟨a, b, c, d, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b+1, c, d, e⟩
  | ⟨a, b+1, c, d, e⟩ => some ⟨a, b, c, d, e+2⟩
  | ⟨a, b, c, d, e+1⟩ => some ⟨a+1, b, c+2, d, e⟩
  | _ => none

-- R1-R3 interleaved chain: each round does R1 (a+=2, b-=1, c-=1, d+=1) then R3 (a-=1, b+=1)
-- Net per round: a+=1, c-=1, d+=1. Last round is just R1.
-- (a, 1, k+1, d, 0) ->* (a+k+2, 0, 0, d+k+1, 0)
theorem r1r3_chain : ∀ k, ∀ a d, ⟨a, 1, k+1, d, 0⟩ [fm]⊢* ⟨a+k+2, 0, 0, d+k+1, 0⟩ := by
  intro k; induction' k with k h <;> intro a d
  · step fm; ring_nf; finish
  rw [show (k + 1) + 1 = (k + 1) + 1 from rfl]
  step fm
  step fm
  apply stepStar_trans (h _ _)
  ring_nf; finish

-- R3 chain: (a+k, b, 0, d, 0) ->* (a, b+k, 0, d, 0)
theorem a_to_b : ∀ k, ∀ a b d, ⟨a+k, b, 0, d, 0⟩ [fm]⊢* ⟨a, b+k, 0, d, 0⟩ := by
  intro k; induction' k with k h <;> intro a b d
  · exists 0
  rw [← Nat.add_assoc]
  step fm
  apply stepStar_trans (h _ _ _)
  ring_nf; finish

-- R4 chain: (0, b+k, 0, d, e) ->* (0, b, 0, d, e+2*k)
theorem b_to_e : ∀ k, ∀ b d e, ⟨0, b+k, 0, d, e⟩ [fm]⊢* ⟨0, b, 0, d, e+2*k⟩ := by
  intro k; induction' k with k h <;> intro b d e
  · exists 0
  rw [← Nat.add_assoc]
  step fm
  apply stepStar_trans (h _ _ _)
  ring_nf; finish

-- R5-R2 interleaved chain: (0, 0, c, d+k, e+2*k) ->* (0, 0, c+2*k, d, e)
theorem r5r2_chain : ∀ k, ∀ c d e, ⟨0, 0, c, d+k, e+2*k⟩ [fm]⊢* ⟨0, 0, c+2*k, d, e⟩ := by
  intro k; induction' k with k h <;> intro c d e
  · exists 0
  rw [show d + (k + 1) = (d + k) + 1 from by ring,
      show e + 2 * (k + 1) = (e + 2 * k) + 2 from by ring]
  step fm
  step fm
  apply stepStar_trans (h _ _ _)
  ring_nf; finish

-- Main transition: (1, 0, c+1, 0, 0) ⊢⁺ (1, 0, 2*c+3, 0, 0)
theorem main_trans (c : ℕ) : ⟨1, 0, c+1, 0, 0⟩ [fm]⊢⁺ ⟨1, 0, 2*c+3, 0, 0⟩ := by
  -- R3: (1, 0, c+1, 0, 0) -> (0, 1, c+1, 0, 0)
  step fm
  -- R1-R3 chain: (0, 1, c+1, 0, 0) ->* (c+2, 0, 0, c+1, 0)
  apply stepStar_trans
  · have h := r1r3_chain c 0 0
    simp only [Nat.zero_add] at h; exact h
  -- R3 chain: (c+2, 0, 0, c+1, 0) ->* (0, c+2, 0, c+1, 0)
  apply stepStar_trans
  · have h := a_to_b (c+2) 0 0 (c+1)
    simp only [Nat.zero_add] at h; exact h
  -- R4 chain: (0, c+2, 0, c+1, 0) ->* (0, 0, 0, c+1, 2*(c+2))
  apply stepStar_trans
  · have h := b_to_e (c+2) 0 (c+1) 0
    simp only [Nat.zero_add] at h; exact h
  -- R5-R2 chain: (0, 0, 0, c+1, 2*(c+2)) ->* (0, 0, 2*(c+1), 0, 2)
  apply stepStar_trans
  · have h := r5r2_chain (c+1) 0 0 2
    simp only [Nat.zero_add, (by ring : 2 + 2 * (c + 1) = 2 * (c + 2)),
               (by ring : 0 + 2 * (c + 1) = 2 * (c + 1))] at h; exact h
  -- Tail: (0, 0, 2*(c+1), 0, 2) -> 4 steps -> (1, 0, 2*c+3, 0, 0)
  step fm; step fm; step fm; step fm
  ring_nf; finish

theorem nonhalt : ¬halts fm c₀ := by
  -- c₀ = (1, 0, 0, 0, 0). Execute to reach (1, 0, 1, 0, 0).
  apply stepStar_not_halts_not_halts (c₂ := ⟨1, 0, 1, 0, 0⟩) (by execute fm 6)
  apply progress_nonhalt_simple (fm := fm) (A := ℕ) (fun c ↦ ⟨1, 0, c+1, 0, 0⟩) 0
  intro c; exists 2*c+2; exact main_trans c

end Sz22_2003_unofficial_446
