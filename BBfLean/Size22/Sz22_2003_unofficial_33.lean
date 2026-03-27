import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #33: [1/15, 28/3, 9/539, 275/2, 7/5]

Vector representation:
```
 0 -1 -1  0  0
 2 -1  0  1  0
 0  2  0 -2 -1
-1  0  2  0  1
 0  0 -1  1  0
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_33

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a, b+1, c+1, d, e⟩ => some ⟨a, b, c, d, e⟩
  | ⟨a, b+1, c, d, e⟩ => some ⟨a+2, b, c, d+1, e⟩
  | ⟨a, b, c, d+2, e+1⟩ => some ⟨a, b+2, c, d, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b, c+2, d, e+1⟩
  | ⟨a, b, c+1, d, e⟩ => some ⟨a, b, c, d+1, e⟩
  | _ => none

-- R4 repeated: (a+k, 0, c, 0, e) →* (a, 0, c+2k, 0, e+k)
theorem r4_chain : ⟨a+k, 0, c, 0, e⟩ [fm]⊢* ⟨a, 0, c+2*k, 0, e+k⟩ := by
  have h : ∀ k a c e, ⟨a+k, 0, c, 0, e⟩ [fm]⊢* ⟨a, 0, c+2*k, 0, e+k⟩ := by
    intro k; induction' k with k ih <;> intro a c e
    · exists 0
    rw [← Nat.add_assoc]; step fm
    apply stepStar_trans (ih _ _ _); ring_nf; finish
  exact h k a c e

-- Drain round: (0, 0, c+4, 0, e+1) →* (0, 0, c, 0, e) in 5 steps
theorem drain_round : ⟨0, 0, c+4, 0, e+1⟩ [fm]⊢* ⟨0, 0, c, 0, e⟩ := by
  execute fm 5

-- Drain loop: (0, 0, 4k+2, 0, e+k) →* (0, 0, 2, 0, e)
theorem drain_loop : ⟨0, 0, 4*k+2, 0, e+k⟩ [fm]⊢* ⟨0, 0, 2, 0, e⟩ := by
  have h : ∀ k e, ⟨0, 0, 4*k+2, 0, e+k⟩ [fm]⊢* ⟨0, 0, 2, 0, e⟩ := by
    intro k; induction' k with k ih <;> intro e
    · exists 0
    rw [show 4*(k+1)+2 = (4*k+2) + 4 from by ring,
        show e + (k+1) = e + k + 1 from by ring]
    apply stepStar_trans drain_round
    exact ih _
  exact h k e

-- Final drain: (0, 0, 2, 0, e+1) →* (0, 2, 0, 0, e)
theorem final_drain : ⟨0, 0, 2, 0, e+1⟩ [fm]⊢* ⟨0, 2, 0, 0, e⟩ := by
  execute fm 3

-- Accumulate: (a, 2, 0, 0, e) →* (a + 4*e + 4, 0, 0, 2, 0)
theorem accum_chain : ⟨a, 2, 0, 0, e⟩ [fm]⊢* ⟨a + 4*e + 4, 0, 0, 2, 0⟩ := by
  have h : ∀ e a, ⟨a, 2, 0, 0, e⟩ [fm]⊢* ⟨a + 4*e + 4, 0, 0, 2, 0⟩ := by
    intro e; induction' e with e ih <;> intro a
    · step fm; step fm; ring_nf; finish
    step fm; step fm; step fm
    apply stepStar_trans (ih _); ring_nf; finish
  exact h e a

-- Tail: (a+1, 0, 0, 2, 0) →⁺ (a, 0, 0, 0, 0)
theorem tail : ⟨a+1, 0, 0, 2, 0⟩ [fm]⊢⁺ ⟨a, 0, 0, 0, 0⟩ := by
  execute fm 4

-- Main transition: (2n+1, 0, 0, 0, 0) →⁺ (4n+3, 0, 0, 0, 0)
theorem main_trans : ⟨2*n+1, 0, 0, 0, 0⟩ [fm]⊢⁺ ⟨4*n+3, 0, 0, 0, 0⟩ := by
  -- Phase 1: R4 chain, k = 2n+1, a = 0, c = 0, e = 0
  rw [show 2*n+1 = 0 + (2*n+1) from by ring]
  apply stepStar_stepPlus_stepPlus (@r4_chain 0 (2*n+1) 0 0)
  -- State: (0, 0, 0+2*(2n+1), 0, 0+(2n+1)) = (0, 0, 4n+2, 0, 2n+1)
  -- Phase 2: drain loop, k = n, e = n+1
  rw [show 0 + 2*(2*n+1) = 4*n+2 from by ring,
      show (0:ℕ) + (2*n+1) = (n+1) + n from by ring]
  apply stepStar_stepPlus_stepPlus (@drain_loop n (n+1))
  -- State: (0, 0, 2, 0, n+1)
  -- Phase 3: final drain
  apply stepStar_stepPlus_stepPlus (@final_drain n)
  -- State: (0, 2, 0, 0, n)
  -- Phase 4: accumulate
  apply stepStar_stepPlus_stepPlus (@accum_chain 0 n)
  -- State: (0 + 4*n + 4, 0, 0, 2, 0) = (4n+4, 0, 0, 2, 0)
  rw [show 0 + 4*n + 4 = (4*n+3) + 1 from by ring]
  -- Phase 5: tail
  exact @tail (4*n+3)

theorem nonhalt : ¬halts fm c₀ := by
  apply progress_nonhalt_simple (fm := fm) (A := ℕ)
    (fun n ↦ ⟨2*n+1, 0, 0, 0, 0⟩) 0
  intro n; refine ⟨2*n+1, ?_⟩
  rw [show 2*(2*n+1)+1 = 4*n+3 from by ring]
  exact main_trans

end Sz22_2003_unofficial_33
