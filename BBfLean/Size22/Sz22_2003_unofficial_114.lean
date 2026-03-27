import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #114: [1/30, 7/3, 45/77, 4/7, 363/2]

Vector representation:
```
-1 -1 -1  0  0
 0 -1  0  1  0
 0  2  1 -1 -1
 2  0  0 -1  0
-1  1  0  0  2
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_114

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a+1, b+1, c+1, d, e⟩ => some ⟨a, b, c, d, e⟩
  | ⟨a, b+1, c, d, e⟩ => some ⟨a, b, c, d+1, e⟩
  | ⟨a, b, c, d+1, e+1⟩ => some ⟨a, b+2, c+1, d, e⟩
  | ⟨a, b, c, d+1, e⟩ => some ⟨a+2, b, c, d, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b+1, c, d, e+2⟩
  | _ => none

-- R4 chain: transfer d to a (each d gives a+2)
theorem r4_chain : ∀ k, ∀ a c d,
    ⟨a, 0, c, d + k, 0⟩ [fm]⊢* ⟨a + 2 * k, 0, c, d, 0⟩ := by
  intro k; induction' k with k ih <;> intro a c d
  · exists 0
  rw [← Nat.add_assoc]
  step fm
  apply stepStar_trans (ih _ _ _)
  ring_nf; finish

-- R5,R1 alternating chain: consume a and c pairwise
theorem r5r1_chain : ∀ k, ∀ a c e,
    ⟨a + 2 * k + 2, 0, c + k, 0, e⟩ [fm]⊢* ⟨a + 2, 0, c, 0, e + 2 * k⟩ := by
  intro k; induction' k with k ih <;> intro a c e
  · exists 0
  rw [show a + 2 * (k + 1) + 2 = (a + 2 * k + 2) + 2 from by ring,
      show c + (k + 1) = (c + k) + 1 from by ring]
  step fm; step fm
  apply stepStar_trans (ih _ _ _)
  ring_nf; finish

-- Pump loop: 3-step cycle consuming e, growing c and d
theorem pump_loop : ∀ j, ∀ c d e,
    ⟨0, 2, c, d, e + j⟩ [fm]⊢* ⟨0, 2, c + j, d + j, e⟩ := by
  intro j; induction' j with j ih <;> intro c d e
  · exists 0
  rw [show e + (j + 1) = (e + j) + 1 from by ring]
  step fm; step fm; step fm
  apply stepStar_trans (ih _ _ _)
  ring_nf; finish

-- R2 pair: drain b=2 into d
theorem r2_pair : ∀ c d,
    ⟨0, 2, c, d, 0⟩ [fm]⊢* ⟨0, 0, c, d + 2, 0⟩ := by
  intro c d
  step fm; step fm; finish

-- Main transition: one full cycle (0,0,n,n+1,0) -> (0,0,2n+1,2n+2,0)
theorem main_trans (n : ℕ) :
    ⟨0, 0, n + 2, n + 3, 0⟩ [fm]⊢⁺ ⟨0, 0, 2 * n + 5, 2 * n + 6, 0⟩ := by
  -- Phase 1: R4 chain
  apply stepStar_stepPlus_stepPlus
  · have h := r4_chain (n + 3) 0 (n + 2) 0
    simp only [Nat.zero_add] at h
    rw [show 2 * (n + 3) = 2 * n + 6 from by ring] at h
    exact h
  -- Phase 2: R5,R1 chain
  apply step_stepStar_stepPlus
  · show fm ⟨2 * n + 6, 0, n + 2, 0, 0⟩ = some ⟨2 * n + 5, 1, n + 2, 0, 2⟩; rfl
  apply stepStar_trans
  · have : ⟨2 * n + 5, 1, n + 2, 0, 2⟩ [fm]⊢* ⟨2 * n + 4, 0, n + 1, 0, 2⟩ := by
      step fm; finish
    exact this
  apply stepStar_trans
  · have h := r5r1_chain (n + 1) 0 0 2
    rw [show 0 + 2 * (n + 1) + 2 = 2 * n + 4 from by ring,
        show 0 + (n + 1) = n + 1 from by ring,
        show 2 + 2 * (n + 1) = 2 * n + 4 from by ring] at h
    exact h
  -- Phase 3: transition steps
  apply stepStar_trans
  · show ⟨0 + 2, 0, 0, 0, 2 * n + 4⟩ [fm]⊢* ⟨0, 2, 1, 0, 2 * n + 4⟩
    step fm; step fm; step fm; step fm; step fm; step fm
    ring_nf; finish
  -- Phase 4: pump loop
  apply stepStar_trans
  · have h := pump_loop (2 * n + 4) 1 0 0
    simp only [Nat.zero_add] at h
    rw [show 1 + (2 * n + 4) = 2 * n + 5 from by ring] at h
    exact h
  -- Phase 5: R2 pair
  exact r2_pair _ _

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨0, 0, 2, 3, 0⟩) (by execute fm 8)
  apply progress_nonhalt_simple (fm := fm) (A := ℕ)
    (fun n ↦ ⟨0, 0, n + 2, n + 3, 0⟩) 0
  intro n
  exact ⟨2 * n + 3, main_trans n⟩

end Sz22_2003_unofficial_114
