import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #97: [1/30, 27/385, 14/3, 5/7, 33/2]

Vector representation:
```
-1 -1 -1  0  0
 0  3 -1 -1 -1
 1 -1  0  1  0
 0  0  1 -1  0
-1  1  0  0  1
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_97

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a+1, b+1, c+1, d, e⟩ => some ⟨a, b, c, d, e⟩
  | ⟨a, b, c+1, d+1, e+1⟩ => some ⟨a, b+3, c, d, e⟩
  | ⟨a, b+1, c, d, e⟩ => some ⟨a+1, b, c, d+1, e⟩
  | ⟨a, b, c, d+1, e⟩ => some ⟨a, b, c+1, d, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b+1, c, d, e+1⟩
  | _ => none

-- Phase 1: Opening steps. (0,1,0,0,e) -> (4,0,0,3,e) in 8 steps.
theorem opening : ⟨0, 1, 0, 0, e+1⟩ [fm]⊢* ⟨4, 0, 0, 3, e+1⟩ := by
  step fm; step fm; step fm; step fm
  step fm; step fm; step fm; step fm
  finish

-- Phase 2: Inner loop step. (A,0,0,D+2,E+1) -> (A+3,0,0,D+3,E) in 5 steps.
theorem inner_step : ⟨a, 0, 0, d+2, e+1⟩ [fm]⊢* ⟨a+3, 0, 0, d+3, e⟩ := by
  step fm; step fm; step fm; step fm; step fm
  finish

-- Phase 2: Inner loop iterated. (A,0,0,D+2,k) -> (A+3k,0,0,D+2+k,0).
theorem inner_loop : ⟨a, 0, 0, d+2, k⟩ [fm]⊢* ⟨a+3*k, 0, 0, d+2+k, 0⟩ := by
  have h : ∀ k a d, ⟨a, 0, 0, d+2, k⟩ [fm]⊢* ⟨a+3*k, 0, 0, d+2+k, 0⟩ := by
    intro k; induction' k with k ih <;> intro a d
    · exists 0
    apply stepStar_trans (@inner_step a d k)
    rw [show d + 3 = (d + 1) + 2 from by ring]
    apply stepStar_trans (ih (a + 3) (d + 1))
    ring_nf; finish
  exact h k a d

-- Phase 3: d to c transfer. (a,0,c,d+k,0) -> (a,0,c+k,d,0).
theorem d_to_c : ⟨a, 0, c, d+k, 0⟩ [fm]⊢* ⟨a, 0, c+k, d, 0⟩ := by
  have h : ∀ k c, ⟨a, 0, c, d+k, 0⟩ [fm]⊢* ⟨a, 0, c+k, d, 0⟩ := by
    intro k; induction' k with k ih <;> intro c
    · exists 0
    rw [← Nat.add_assoc]; step fm
    apply stepStar_trans (ih _); ring_nf; finish
  exact h k c

-- Phase 4: ac drain. (a+2k,0,k,0,e) -> (a,0,0,0,e+k).
theorem ac_drain : ⟨a+2*k, 0, k, 0, e⟩ [fm]⊢* ⟨a, 0, 0, 0, e+k⟩ := by
  have h : ∀ k a e, ⟨a+2*k, 0, k, 0, e⟩ [fm]⊢* ⟨a, 0, 0, 0, e+k⟩ := by
    intro k; induction' k with k ih <;> intro a e
    · exists 0
    rw [show a + 2 * (k + 1) = (a + 2 * k) + 2 from by ring]
    rw [show k + 1 = k + 1 from rfl]
    step fm; step fm
    apply stepStar_trans (ih _ _); ring_nf; finish
  exact h k a e

-- Phase 5: Tail step. (a+2,0,0,0,e) -> (a,0,0,0,e+2) in 5 steps.
theorem tail_step : ⟨a+2, 0, 0, 0, e⟩ [fm]⊢* ⟨a, 0, 0, 0, e+2⟩ := by
  step fm; step fm; step fm; step fm; step fm
  finish

-- Phase 5: Tail loop iterated. (a+2k,0,0,0,e) -> (a,0,0,0,e+2k).
theorem tail_loop : ⟨a+2*k, 0, 0, 0, e⟩ [fm]⊢* ⟨a, 0, 0, 0, e+2*k⟩ := by
  have h : ∀ k a e, ⟨a+2*k, 0, 0, 0, e⟩ [fm]⊢* ⟨a, 0, 0, 0, e+2*k⟩ := by
    intro k; induction' k with k ih <;> intro a e
    · exists 0
    rw [show a + 2 * (k + 1) = (a + 2 * k) + 2 from by ring]
    apply stepStar_trans tail_step
    apply stepStar_trans (ih _ _); ring_nf; finish
  exact h k a e

-- Phase 6: Final R5 step. (1,0,0,0,e) -> (0,1,0,0,e+1).
theorem final_r5 : ⟨1, 0, 0, 0, e⟩ [fm]⊢⁺ ⟨0, 1, 0, 0, e+1⟩ := by
  step fm; finish

-- Main transition: (0,1,0,0,2n+7) →⁺ (0,1,0,0,4n+15).
theorem main_trans : ⟨0, 1, 0, 0, 2*n+7⟩ [fm]⊢⁺ ⟨0, 1, 0, 0, 4*n+15⟩ := by
  -- Phase 1: Opening. (0,1,0,0,2n+7) -> (4,0,0,3,2n+7).
  rw [show 2*n+7 = (2*n+6)+1 from by ring]
  apply stepStar_stepPlus_stepPlus opening
  -- Phase 2: Inner loop. (4,0,0,3,2n+7) -> (6n+25,0,0,2n+10,0).
  rw [show (3 : ℕ) = 1 + 2 from by ring]
  apply stepStar_stepPlus_stepPlus (inner_loop (k := 2*n+7))
  -- Phase 3: d to c. (6n+25,0,0,2n+10,0) -> (6n+25,0,2n+10,0,0).
  rw [show 1 + 2 + (2 * n + 7) = 0 + (2 * n + 10) from by ring]
  rw [show 4 + 3 * (2 * n + 7) = 6 * n + 25 from by ring]
  apply stepStar_stepPlus_stepPlus (d_to_c (k := 2*n+10) (d := 0))
  simp only [Nat.zero_add]
  -- Phase 4: ac drain. (6n+25,0,2n+10,0,0) -> (2n+5,0,0,0,2n+10).
  rw [show 6*n+25 = (2*n+5) + 2*(2*n+10) from by ring]
  apply stepStar_stepPlus_stepPlus (ac_drain (k := 2*n+10) (e := 0))
  simp only [Nat.zero_add]
  -- Phase 5: Tail loop. (2n+5,0,0,0,2n+10) -> (1,0,0,0,4n+14).
  rw [show 2*n+5 = 1 + 2*(n+2) from by ring]
  apply stepStar_stepPlus_stepPlus (tail_loop (k := n+2))
  rw [show 2*n+10 + 2*(n+2) = 4*n+14 from by ring]
  -- Phase 6: Final R5. (1,0,0,0,4n+14) -> (0,1,0,0,4n+15).
  exact final_r5

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨0, 1, 0, 0, 7⟩) (by execute fm 64)
  apply progress_nonhalt_simple (fm := fm) (A := ℕ)
    (fun n ↦ ⟨0, 1, 0, 0, 2*n+7⟩) 0
  intro n; exists 2*n+4
  rw [show 2 * (2 * n + 4) + 7 = 4 * n + 15 from by ring]
  exact main_trans

end Sz22_2003_unofficial_97
