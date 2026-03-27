import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #444: [27/385, 1/30, 14/3, 5/7, 33/2]

Vector representation:
```
 0  3 -1 -1 -1
-1 -1 -1  0  0
 1 -1  0  1  0
 0  0  1 -1  0
-1  1  0  0  1
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_444

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a, b, c+1, d+1, e+1⟩ => some ⟨a, b+3, c, d, e⟩
  | ⟨a+1, b+1, c+1, d, e⟩ => some ⟨a, b, c, d, e⟩
  | ⟨a, b+1, c, d, e⟩ => some ⟨a+1, b, c, d+1, e⟩
  | ⟨a, b, c, d+1, e⟩ => some ⟨a, b, c+1, d, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b+1, c, d, e+1⟩
  | _ => none

-- Phase 1: R4 repeated — transfer d to c
theorem d_to_c : ∀ k a c d, ⟨a, 0, c, d+k, 0⟩ [fm]⊢* ⟨a, 0, c+k, d, 0⟩ := by
  intro k; induction' k with k h <;> intro a c d
  · exists 0
  rw [← Nat.add_assoc]
  step fm
  apply stepStar_trans (h _ _ _)
  ring_nf; finish

-- Phase 2: (R5, R2) drain
theorem drain : ∀ k a c e, ⟨a+2*k, 0, c+k, 0, e⟩ [fm]⊢* ⟨a, 0, c, 0, e+k⟩ := by
  intro k; induction' k with k h <;> intro a c e
  · exists 0
  rw [show a + 2 * (k + 1) = (a + 2 * k) + 2 from by ring,
      show c + (k + 1) = (c + k) + 1 from by ring]
  step fm  -- R5
  step fm  -- R2
  apply stepStar_trans (h _ _ _)
  ring_nf; finish

-- Phase 3: Unwind — (a+2, 0, 0, 0, e) -> (a, 0, 0, 0, e+2) per cycle
theorem unwind : ∀ k a e, ⟨a+2*k, 0, 0, 0, e⟩ [fm]⊢* ⟨a, 0, 0, 0, e+2*k⟩ := by
  intro k; induction' k with k h <;> intro a e
  · exists 0
  rw [show a + 2 * (k + 1) = (a + 2 * k) + 2 from by ring]
  step fm  -- R5
  step fm  -- R3
  step fm  -- R4
  step fm  -- R5
  step fm  -- R2
  apply stepStar_trans (h _ _)
  ring_nf; finish

-- Phase 4: Bootstrap — (1, 0, 0, 0, e) -> (4, 0, 0, 3, e+1) in 9 steps
theorem bootstrap (e : ℕ) : ⟨1, 0, 0, 0, e⟩ [fm]⊢* ⟨4, 0, 0, 3, e+1⟩ := by
  step fm; step fm; step fm; step fm; step fm; step fm; step fm; step fm; step fm; finish

-- Phase 5: Main loop — uses d+2 pattern so R1 can see d+1 after R4
theorem main_loop : ∀ k a d e, ⟨a, 0, 0, d+2, e+k⟩ [fm]⊢* ⟨a+3*k, 0, 0, d+2+k, e⟩ := by
  intro k; induction' k with k h <;> intro a d e
  · exists 0
  rw [show e + (k + 1) = (e + k) + 1 from by ring]
  step fm  -- R4: (a, 0, 1, d+1, e+k+1)
  step fm  -- R1: (a, 3, 0, d, e+k)
  step fm  -- R3
  step fm  -- R3
  step fm  -- R3
  apply stepStar_trans (h _ _ _)
  ring_nf; finish

-- Full transition: (6k+13, 0, 0, 2k+6, 0) ⊢⁺ (12k+25, 0, 0, 4k+10, 0)
theorem main_trans (k : ℕ) : ⟨6*k+13, 0, 0, 2*k+6, 0⟩ [fm]⊢⁺ ⟨12*k+25, 0, 0, 4*k+10, 0⟩ := by
  -- Phase 1: d_to_c — (6k+13, 0, 0, 2k+6, 0) ⊢* (6k+13, 0, 2k+6, 0, 0)
  apply stepStar_stepPlus_stepPlus
  · have h := d_to_c (2*k+6) (6*k+13) 0 0
    simp only [Nat.zero_add] at h; exact h
  -- Phase 2: drain — (6k+13, 0, 2k+6, 0, 0) ⊢⁺ (2k+1, 0, 0, 0, 2k+6)
  -- Rewrite to get (R5,R2) compatible form, then use drain for ⊢*
  -- First manually take one R5 step, then R2, then use drain for the rest
  -- (6k+13, 0, 2k+6, 0, 0) = ((6k+12)+1, 0, (2k+5)+1, 0, 0)
  -- R5: -> (6k+12, 1, 2k+6, 0, 1) = ((6k+11)+1, 1, (2k+5)+1, 0, 1)
  -- R2: -> (6k+11, 0, 2k+5, 0, 1) = (2k+1 + 2*(2k+5), 0, 0 + (2k+5), 0, 1)
  -- drain (2k+5): -> (2k+1, 0, 0, 0, 2k+6)
  rw [show (6*k+13 : ℕ) = (6*k+12) + 1 from by ring,
      show (2*k+6 : ℕ) = (2*k+5) + 1 from by ring]
  apply step_stepStar_stepPlus (c₂ := ⟨6*k+12, 1, (2*k+5)+1, 0, 1⟩)
  · show fm ⟨6*k+12+1, 0, (2*k+5)+1, 0, 0⟩ = some ⟨6*k+12, 1, (2*k+5)+1, 0, 1⟩
    unfold fm; simp only
  apply stepStar_trans (c₂ := ⟨6*k+11, 0, 2*k+5, 0, 1⟩)
  · step fm; finish
  apply stepStar_trans
  · have h := drain (2*k+5) (2*k+1) 0 1
    simp only [Nat.zero_add,
               show 2*k+1 + 2*(2*k+5) = 6*k+11 from by ring,
               show 1 + (2*k+5) = 2*k+6 from by ring] at h
    exact h
  -- Phase 3: unwind — (2k+1, 0, 0, 0, 2k+6) -> (1, 0, 0, 0, 4k+6)
  apply stepStar_trans
  · have h := unwind k 1 (2*k+6)
    simp only [show 1 + 2*k = 2*k+1 from by ring,
               show 2*k+6 + 2*k = 4*k+6 from by ring] at h
    exact h
  -- Phase 4: bootstrap — (1, 0, 0, 0, 4k+6) -> (4, 0, 0, 3, 4k+7)
  apply stepStar_trans (bootstrap (4*k+6))
  -- Phase 5: main loop — (4, 0, 0, 3, 4k+7) -> (12k+25, 0, 0, 4k+10, 0)
  have h := main_loop (4*k+7) 4 1 0
  simp only [show 0 + (4*k+7) = 4*k+7 from by ring,
             show 4 + 3*(4*k+7) = 12*k+25 from by ring,
             show 1 + 2 + (4*k+7) = 4*k+10 from by ring] at h
  exact h

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨7, 0, 0, 4, 0⟩) (by execute fm 14)
  apply progress_nonhalt_simple (fm := fm) (A := ℕ) (fun k ↦ ⟨6*k+7, 0, 0, 2*k+4, 0⟩) 0
  intro k
  rcases k with _ | k
  · exists 1; execute fm 31
  · exists 2*k+3
    show ⟨6*k+13, 0, 0, 2*k+6, 0⟩ [fm]⊢⁺ ⟨6*(2*k+3)+7, 0, 0, 2*(2*k+3)+4, 0⟩
    simp only [show 6*(2*k+3)+7 = 12*k+25 from by ring,
               show 2*(2*k+3)+4 = 4*k+10 from by ring]
    exact main_trans k

end Sz22_2003_unofficial_444
