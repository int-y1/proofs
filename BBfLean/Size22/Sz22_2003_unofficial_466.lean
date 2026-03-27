import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #466: [28/15, 21/22, 25/2, 11/7, 14/5]

Vector representation:
```
 2 -1 -1  1  0
-1  1  0  1 -1
-1  0  2  0  0
 0  0  0 -1  1
 1  0 -1  1  0
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_466

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a, b+1, c+1, d, e⟩ => some ⟨a+2, b, c, d+1, e⟩
  | ⟨a+1, b, c, d, e+1⟩ => some ⟨a, b+1, c, d+1, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b, c+2, d, e⟩
  | ⟨a, b, c, d+1, e⟩ => some ⟨a, b, c, d, e+1⟩
  | ⟨a, b, c+1, d, e⟩ => some ⟨a+1, b, c, d+1, e⟩
  | _ => none

-- R4 repeated: convert d to e
theorem d_to_e : ∀ k c d e, ⟨0, 0, c, d+k, e⟩ [fm]⊢* ⟨0, 0, c, d, e+k⟩ := by
  intro k; induction' k with k h <;> intro c d e
  · exists 0
  rw [← Nat.add_assoc]
  step fm
  apply stepStar_trans (h _ _ _)
  ring_nf; finish

-- R3 repeated: convert a to c (when b=0, e=0)
theorem a_to_c : ∀ k a c d, ⟨a+k, 0, c, d, 0⟩ [fm]⊢* ⟨a, 0, c+2*k, d, 0⟩ := by
  intro k; induction' k with k h <;> intro a c d
  · exists 0
  rw [← Nat.add_assoc]
  step fm
  apply stepStar_trans (h _ _ _)
  ring_nf; finish

-- R2-R1 interleaved chain: k rounds of (R2, R1)
-- Net effect per round: a→a+1, c→c-1, d→d+2, e→e-1
theorem r2r1_chain : ∀ k a c d e, ⟨a+1, 0, c+k, d, e+k⟩ [fm]⊢* ⟨a+k+1, 0, c, d+2*k, e⟩ := by
  intro k; induction' k with k h <;> intro a c d e
  · exists 0
  rw [show c + (k + 1) = (c + k) + 1 from by ring,
      show e + (k + 1) = (e + k) + 1 from by ring]
  step fm  -- R2: (a, 1, (c+k)+1, d+1, e+k)
  rw [show (c + k) + 1 = (c + k + 1) from by ring]
  step fm  -- R1: (a+2, 0, c+k, d+2, e+k)
  apply stepStar_trans (h (a+1) c (d+2) e)
  ring_nf; finish

-- Main transition: (0, 0, d+2, d, 0) ⊢⁺ (0, 0, 2*d+3, 2*d+1, 0)
theorem main_trans (d : ℕ) : ⟨0, 0, d+2, d, 0⟩ [fm]⊢⁺ ⟨0, 0, 2*d+3, 2*d+1, 0⟩ := by
  rcases d with _ | d
  · -- d=0: (0,0,2,0,0) -> R5 -> (1,0,1,1,0) -> R3 -> (0,0,3,1,0)
    execute fm 2
  · -- d+1 >= 1: goal is (0, 0, d+1+2, d+1, 0) ⊢⁺ (0, 0, 2*(d+1)+3, 2*(d+1)+1, 0)
    -- Phase 1: R4 (d+1) times
    apply stepStar_stepPlus_stepPlus (c₂ := ⟨0, 0, d+1+2, 0, d+1⟩)
    · have h := d_to_e (d+1) (d+1+2) 0 0
      simp only [Nat.zero_add] at h; exact h
    -- Phase 2: R5
    step fm
    -- Phase 3: R2-R1 chain (d+1) rounds
    apply stepStar_trans (c₂ := ⟨d+2, 0, 1, 2*d+3, 0⟩)
    · have h := r2r1_chain (d+1) 0 1 1 0
      simp only [Nat.zero_add,
                 (by ring : 1 + (d + 1) = d + 2),
                 (by ring : 0 + (d + 1) = d + 1),
                 (by ring : 1 + 2 * (d + 1) = 2 * d + 3)] at h
      exact h
    -- Phase 4: R3 (d+2) times
    have h := a_to_c (d+2) 0 1 (2*d+3)
    simp only [Nat.zero_add,
               (by ring : 1 + 2 * (d + 2) = 2 * (d + 1) + 3),
               (by ring : 2 * d + 3 = 2 * (d + 1) + 1)] at h
    exact h

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨0, 0, 2, 0, 0⟩) (by execute fm 1)
  apply progress_nonhalt_simple (fm := fm) (A := ℕ) (fun d ↦ ⟨0, 0, d+2, d, 0⟩) 0
  intro d; exists 2*d+1
  exact main_trans d

end Sz22_2003_unofficial_466
