import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #269: [14/15, 18/7, 1/6, 125/2, 14/5]

Vector representation:
```
 1 -1 -1  1
 1  2  0 -1
-1 -1  0  0
-1  0  3  0
 1  0 -1  1
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_269

def Q := ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a, b+1, c+1, d⟩ => some ⟨a+1, b, c, d+1⟩
  | ⟨a, b, c, d+1⟩ => some ⟨a+1, b+2, c, d⟩
  | ⟨a+1, b+1, c, d⟩ => some ⟨a, b, c, d⟩
  | ⟨a+1, b, c, d⟩ => some ⟨a, b, c+3, d⟩
  | ⟨a, b, c+1, d⟩ => some ⟨a+1, b, c, d+1⟩
  | _ => none

-- R2 chain: consume d, increase a and b
theorem r2_chain : ∀ j, ∀ a b d,
    ⟨a, b, 0, d+j⟩ [fm]⊢* ⟨a+j, b+2*j, 0, d⟩ := by
  intro j; induction' j with j ih <;> intro a b d
  · exists 0
  rw [← Nat.add_assoc]
  step fm
  apply stepStar_trans (ih _ _ _)
  ring_nf; finish

-- R3 chain: consume equal amounts from a and b
theorem r3_chain : ∀ j, ∀ a b,
    ⟨a+j, b+j, 0, 0⟩ [fm]⊢* ⟨a, b, 0, 0⟩ := by
  intro j; induction' j with j ih <;> intro a b
  · exists 0
  show ⟨(a + j) + 1, (b + j) + 1, 0, 0⟩ [fm]⊢* ⟨a, b, 0, 0⟩
  step fm
  exact ih _ _

-- R4 chain: consume a, produce c
theorem r4_chain : ∀ j, ∀ a c,
    ⟨a+j, 0, c, 0⟩ [fm]⊢* ⟨a, 0, c+3*j, 0⟩ := by
  intro j; induction' j with j ih <;> intro a c
  · exists 0
  show ⟨(a + j) + 1, 0, c, 0⟩ [fm]⊢* ⟨a, 0, c + 3 * (j + 1), 0⟩
  step fm
  apply stepStar_trans (ih _ _)
  ring_nf; finish

-- Triplet: (a, 2, c+2, d) -> (a+3, 2, c, d+1) in 3 steps
theorem triplet : ∀ a c d,
    ⟨a, 2, c+2, d⟩ [fm]⊢* ⟨a+3, 2, c, d+1⟩ := by
  intro a c d
  show ⟨a, 1+1, (c+1)+1, d⟩ [fm]⊢* _
  step fm
  show ⟨a+1, 0+1, c+1, d+1⟩ [fm]⊢* _
  step fm
  show ⟨a+1+1, 0, c, (d+1)+1⟩ [fm]⊢* _
  step fm
  ring_nf; finish

-- Triplet iteration: j triplets
theorem triplet_iter : ∀ j, ∀ a c d,
    ⟨a, 2, c+2*j, d⟩ [fm]⊢* ⟨a+3*j, 2, c, d+j⟩ := by
  intro j; induction' j with j ih <;> intro a c d
  · exists 0
  rw [show c + 2 * (j + 1) = (c + 2 * j) + 2 from by ring]
  apply stepStar_trans (triplet _ _ _)
  apply stepStar_trans (ih (a + 3) c (d + 1))
  ring_nf; finish

-- Combined consume: process all c and d from (a, 2, c, d) to (a+2c+d, c+2+2d, 0, 0)
theorem consume : ∀ c, ∀ d a,
    ⟨a, 2, c, d⟩ [fm]⊢* ⟨a+2*c+d, c+2+2*d, 0, 0⟩ := by
  intro c; induction' c using Nat.strongRecOn with c IH; intro d a
  rcases c with _ | _ | c
  · -- c = 0: just R2 chain
    simp only [Nat.zero_add, Nat.mul_zero, Nat.add_zero]
    have h := r2_chain d a 2 0
    simp only [Nat.zero_add] at h
    exact h
  · -- c = 1: R1 then R2 chain
    show ⟨a, 0 + 1 + 1, 0 + 1, d⟩ [fm]⊢* _
    step fm
    have h := r2_chain (d + 1) (a + 1) 1 0
    simp only [Nat.zero_add] at h
    apply stepStar_trans h
    ring_nf; finish
  · -- c + 2: triplet then IH
    apply stepStar_trans (triplet a c d)
    apply stepStar_trans (IH c (by omega) (d + 1) (a + 3))
    ring_nf; finish

-- Main transition: (0, 0, 3*(k+1), 0) →⁺ (0, 0, 9*k+6, 0)
theorem main_trans (k : ℕ) :
    ⟨0, 0, 3*k+3, 0⟩ [fm]⊢⁺ ⟨0, 0, 9*k+6, 0⟩ := by
  -- Step 1: R5: (0, 0, 3k+3, 0) -> (1, 0, 3k+2, 1)
  apply step_stepStar_stepPlus
  · show fm ⟨0, 0, 3 * k + 3, 0⟩ = some ⟨1, 0, 3 * k + 2, 1⟩
    show fm ⟨0, 0, (3 * k + 2) + 1, 0⟩ = some ⟨1, 0, 3 * k + 2, 1⟩
    rfl
  -- Step 2: R2: (1, 0, 3k+2, 1) -> (2, 2, 3k+2, 0)
  apply stepStar_trans
  · show ⟨1, 0, 3 * k + 2, 0 + 1⟩ [fm]⊢* ⟨2, 2, 3 * k + 2, 0⟩
    step fm; ring_nf; finish
  -- Phase 2: consume: (2, 2, 3k+2, 0) ->* (6k+6, 3k+4, 0, 0)
  apply stepStar_trans
  · have h := consume (3 * k + 2) 0 2
    simp only [Nat.mul_zero, Nat.add_zero] at h
    exact h
  -- Phase 3: R3 chain: (6k+6, 3k+4, 0, 0) ->* (3k+2, 0, 0, 0)
  apply stepStar_trans
  · have h := r3_chain (3 * k + 4) (3 * k + 2) 0
    rw [show (3 * k + 2) + (3 * k + 4) = 2 + 2 * (3 * k + 2) from by ring,
        show 0 + (3 * k + 4) = 3 * k + 2 + 2 + 2 * 0 from by ring] at h
    exact h
  -- Phase 4: R4 chain: (3k+2, 0, 0, 0) ->* (0, 0, 9k+6, 0)
  have h := r4_chain (3 * k + 2) 0 0
  simp only [Nat.zero_add] at h
  rw [show 3 * (3 * k + 2) = 9 * k + 6 from by ring] at h
  exact h

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨0, 0, 3, 0⟩) (by execute fm 1)
  apply progress_nonhalt_simple (fm := fm) (A := ℕ)
    (fun k ↦ ⟨0, 0, 3 * (k + 1), 0⟩) 0
  intro k
  refine ⟨3 * k + 1, ?_⟩
  show ⟨0, 0, 3 * (k + 1), 0⟩ [fm]⊢⁺ ⟨0, 0, 3 * ((3 * k + 1) + 1), 0⟩
  rw [show 3 * (k + 1) = 3 * k + 3 from by ring,
      show 3 * ((3 * k + 1) + 1) = 9 * k + 6 from by ring]
  exact main_trans k

end Sz22_2003_unofficial_269
