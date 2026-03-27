import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #271: [14/15, 18/7, 1/6, 625/2, 3/5]

Vector representation:
```
 1 -1 -1  1
 1  2  0 -1
-1 -1  0  0
-1  0  4  0
 0  1 -1  0
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_271

def Q := ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a, b+1, c+1, d⟩ => some ⟨a+1, b, c, d+1⟩
  | ⟨a, b, c, d+1⟩ => some ⟨a+1, b+2, c, d⟩
  | ⟨a+1, b+1, c, d⟩ => some ⟨a, b, c, d⟩
  | ⟨a+1, b, c, d⟩ => some ⟨a, b, c+4, d⟩
  | ⟨a, b, c+1, d⟩ => some ⟨a, b+1, c, d⟩
  | _ => none

-- R2 chain: consume d when c=0
theorem r2_chain : ∀ j, ∀ a b d,
    ⟨a, b, 0, d+j⟩ [fm]⊢* ⟨a+j, b+2*j, 0, d⟩ := by
  intro j; induction' j with j ih <;> intro a b d
  · exists 0
  rw [← Nat.add_assoc]
  step fm
  apply stepStar_trans (ih _ _ _)
  ring_nf; finish

-- R3 chain: consume equal a and b when c=0, d=0
theorem r3_chain : ∀ j, ∀ a b,
    ⟨a+j, b+j, 0, 0⟩ [fm]⊢* ⟨a, b, 0, 0⟩ := by
  intro j; induction' j with j ih <;> intro a b
  · exists 0
  show ⟨(a + j) + 1, (b + j) + 1, 0, 0⟩ [fm]⊢* ⟨a, b, 0, 0⟩
  step fm
  exact ih _ _

-- R4 chain: consume a when b=0 (c accumulates)
theorem r4_chain : ∀ j, ∀ a c,
    ⟨a+j, 0, c, 0⟩ [fm]⊢* ⟨a, 0, c+4*j, 0⟩ := by
  intro j; induction' j with j ih <;> intro a c
  · exists 0
  show ⟨(a + j) + 1, 0, c, 0⟩ [fm]⊢* ⟨a, 0, c + 4 * (j + 1), 0⟩
  step fm
  apply stepStar_trans (ih _ _)
  ring_nf; finish

-- Triplet: (a, 2, c+2, d) -> (a+3, 2, c, d+1) in 3 steps
theorem triplet : ∀ a c d,
    ⟨a, 2, c+2, d⟩ [fm]⊢* ⟨a+3, 2, c, d+1⟩ := by
  intro a c d
  step fm; step fm
  show ⟨a + 1 + 1, 0, c, (d + 1) + 1⟩ [fm]⊢* ⟨a + 3, 2, c, d + 1⟩
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

-- Consume: from (a, 2, c+1, d) reach (a+2c+d+2, c+2d+3, 0, 0)
theorem consume : ∀ c, ∀ d a,
    ⟨a, 2, c+1, d⟩ [fm]⊢* ⟨a+2*c+d+2, c+2*d+3, 0, 0⟩ := by
  intro c; induction' c using Nat.strongRecOn with c IH; intro d a
  rcases c with _ | c
  · -- c+1 = 1: R1 then R2 chain
    step fm
    show ⟨a + 1, 1, 0, d + 1⟩ [fm]⊢* ⟨a + 0 + d + 2, 0 + 2 * d + 3, 0, 0⟩
    rw [show d + 1 = 0 + (d + 1) from by ring]
    apply stepStar_trans (r2_chain (d+1) (a+1) 1 0)
    ring_nf; finish
  · -- c+2: triplet then handle remaining c
    show ⟨a, 2, (c + 1) + 1, d⟩ [fm]⊢* _
    rw [show (c + 1) + 1 = c + 2 from by ring]
    apply stepStar_trans (triplet a c d)
    rcases c with _ | c'
    · -- c = 0: after triplet at (a+3, 2, 0, d+1). R2 chain.
      show ⟨a + 3, 2, 0, d + 1⟩ [fm]⊢* ⟨a + 2 * (0 + 1) + d + 2, 0 + 1 + 2 * d + 3, 0, 0⟩
      rw [show d + 1 = 0 + (d + 1) from by ring]
      apply stepStar_trans (r2_chain (d+1) (a+3) 2 0)
      ring_nf; finish
    · -- c = c'+1: recurse with IH
      show ⟨a + 3, 2, c' + 1, d + 1⟩ [fm]⊢* ⟨a + 2 * (c' + 1 + 1) + d + 2, c' + 1 + 1 + 2 * d + 3, 0, 0⟩
      apply stepStar_trans (IH c' (by omega) (d+1) (a+3))
      ring_nf; finish

-- Main transition: (0, 0, k+4, 0) →⁺ (0, 0, 4k+8, 0)
theorem main_trans (k : ℕ) :
    ⟨0, 0, k+4, 0⟩ [fm]⊢⁺ ⟨0, 0, 4*k+8, 0⟩ := by
  -- Phase 1: R5, R1, R2: (0, 0, k+4, 0) -> (2, 2, k+2, 0)
  show ⟨0, 0, (k + 3) + 1, 0⟩ [fm]⊢⁺ ⟨0, 0, 4 * k + 8, 0⟩
  apply step_stepStar_stepPlus
  · rfl  -- R5: (0, 1, k+3, 0)
  show ⟨0, 1, (k + 2) + 1, 0⟩ [fm]⊢* ⟨0, 0, 4 * k + 8, 0⟩
  step fm  -- R1: (1, 0, k+2, 1)
  show ⟨1, 0, k + 2, 0 + 1⟩ [fm]⊢* ⟨0, 0, 4 * k + 8, 0⟩
  step fm  -- R2: (2, 2, k+2, 0)
  -- Phase 2: consume: (2, 2, (k+1)+1, 0) ->* (2k+6, k+4, 0, 0)
  show ⟨2, 2, (k + 1) + 1, 0⟩ [fm]⊢* ⟨0, 0, 4 * k + 8, 0⟩
  apply stepStar_trans (consume (k+1) 0 2)
  -- At (2+2*(k+1)+0+2, (k+1)+2*0+3, 0, 0) = (2k+6, k+4, 0, 0)
  -- Phase 3: R3 chain
  have hr3 := r3_chain (k+4) (k+2) 0
  rw [show (k + 2) + (k + 4) = 2 + 2 * (k + 1) + 0 + 2 from by ring,
      show (0 : ℕ) + (k + 4) = k + 1 + 2 * 0 + 3 from by ring] at hr3
  apply stepStar_trans hr3
  -- Now at (k+2, 0, 0, 0)
  -- Phase 4: R4 chain
  have hr4 := r4_chain (k+2) 0 0
  rw [show (0 : ℕ) + (k + 2) = k + 2 from by ring,
      show 0 + 4 * (k + 2) = 4 * k + 8 from by ring] at hr4
  exact hr4

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨0, 0, 4, 0⟩) (by execute fm 1)
  apply progress_nonhalt_simple (fm := fm) (A := ℕ)
    (fun k ↦ ⟨0, 0, k+4, 0⟩) 0
  intro k
  refine ⟨4*k+4, ?_⟩
  show ⟨0, 0, k+4, 0⟩ [fm]⊢⁺ ⟨0, 0, (4*k+4)+4, 0⟩
  rw [show (4 * k + 4) + 4 = 4 * k + 8 from by ring]
  exact main_trans k

end Sz22_2003_unofficial_271
