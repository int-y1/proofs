import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz21_140_unofficial #62: [4/15, 33/14, 25/2, 7/11, 14/5]

Vector representation:
```
 2 -1 -1  0  0
-1  1  0 -1  1
-1  0  2  0  0
 0  0  0  1 -1
 1  0 -1  1  0
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz21_140_unofficial_62

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a, b+1, c+1, d, e⟩ => some ⟨a+2, b, c, d, e⟩
  | ⟨a+1, b, c, d+1, e⟩ => some ⟨a, b+1, c, d, e+1⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b, c+2, d, e⟩
  | ⟨a, b, c, d, e+1⟩ => some ⟨a, b, c, d+1, e⟩
  | ⟨a, b, c+1, d, e⟩ => some ⟨a+1, b, c, d+1, e⟩
  | _ => none

-- Phase 2: R2/R1 chain. From (a+1, 0, c+k, d+k, e) take k R2/R1 pairs.
-- Result: (a+k+1, 0, c, d, e+k)
theorem r2r1_chain : ∀ k, ∀ a c d e, ⟨a+1, 0, c+k, d+k, e⟩ [fm]⊢* ⟨a+k+1, 0, c, d, e+k⟩ := by
  intro k; induction' k with k h <;> intro a c d e
  · exists 0
  -- State: (a+1, 0, c+(k+1), d+(k+1), e)
  rw [show c + (k + 1) = (c + k) + 1 from by ring,
      show d + (k + 1) = (d + k) + 1 from by ring]
  -- R2 fires: a+1 ≥ 1, d+k+1 ≥ 1
  step fm
  -- After R2: (a, 1, (c+k)+1, d+k, e+1)
  -- R1 fires: b=1 ≥ 1, c+k+1 ≥ 1
  step fm
  -- After R1: (a+2, 0, c+k, d+k, e+1)
  -- Apply IH with a' = a+1
  have h2 := h (a + 1) c d (e + 1)
  rw [show a + 1 + 1 = a + 2 from by ring] at h2
  apply stepStar_trans h2
  ring_nf; finish

-- Phase 3: R3 repeated. a → 0, c increases by 2*a.
theorem r3_repeat : ∀ k, ∀ c e, ⟨k, 0, c, 0, e⟩ [fm]⊢* ⟨0, 0, c+2*k, 0, e⟩ := by
  intro k; induction' k with k h <;> intro c e
  · exists 0
  -- State: (k+1, 0, c, 0, e). R3 fires (a=k+1≥1, b=0, d=0).
  -- But wait: R2 needs a≥1 and d≥1. d=0, so R2 doesn't fire. R3 fires.
  step fm
  -- After R3: (k, 0, c+2, 0, e)
  apply stepStar_trans (h (c + 2) e)
  ring_nf; finish

-- Phase 4: R4 repeated. e → d.
theorem r4_repeat : ∀ k, ∀ c d, ⟨0, 0, c, d, k⟩ [fm]⊢* ⟨0, 0, c, d+k, 0⟩ := by
  intro k; induction' k with k h <;> intro c d
  · exists 0
  -- State: (0, 0, c, d, k+1). R4 fires (e=k+1≥1, a=0 so R1-R3 don't fire).
  -- Wait: R1 needs b≥1. b=0. R2 needs a≥1. a=0. R3 needs a≥1. a=0.
  -- R4 needs e≥1. e=k+1≥1. But also need c=0? No, R4 matches any c.
  -- R4: (a, b, c, d, e+1) → (a, b, c, d+1, e). Fires.
  step fm
  -- After R4: (0, 0, c, d+1, k)
  apply stepStar_trans (h c (d + 1))
  ring_nf; finish

-- Main transition: (0, 0, c+d+3, d+1, 0) →⁺ (0, 0, c+2*d+6, d+2, 0)
theorem main_trans : ⟨0, 0, c+d+3, d+1, 0⟩ [fm]⊢⁺ ⟨0, 0, c+2*d+6, d+2, 0⟩ := by
  -- Phase 1: R5. (0, 0, c+d+3, d+1, 0) → (1, 0, c+d+2, d+2, 0)
  rw [show c + d + 3 = (c + d + 2) + 1 from by ring]
  apply step_stepStar_stepPlus
  · show fm ⟨0, 0, (c + d + 2) + 1, d + 1, 0⟩ = some ⟨1, 0, c + d + 2, d + 2, 0⟩
    simp [fm]
  -- Phase 2: R2/R1 chain with k=d+2 pairs.
  -- r2r1_chain (d+2) 0 c 0 0 gives: (1, 0, c+d+2, d+2, 0) →* (d+3, 0, c, 0, d+2)
  apply stepStar_trans
  · have h := r2r1_chain (d + 2) 0 c 0 0
    simp only [Nat.zero_add] at h
    rw [show c + (d + 2) = c + d + 2 from by ring] at h
    exact h
  -- Phase 3: R3 repeated d+3 times.
  -- (d+3, 0, c, 0, d+2) →* (0, 0, c+2*(d+3), 0, d+2)
  apply stepStar_trans
  · exact r3_repeat (d + 3) c (d + 2)
  -- Phase 4: R4 repeated d+2 times.
  -- (0, 0, c+2*(d+3), 0, d+2) →* (0, 0, c+2*(d+3), d+2, 0)
  have h4 := r4_repeat (d + 2) (c + 2 * (d + 3)) 0
  simp only [Nat.zero_add] at h4
  refine stepStar_trans h4 ?_
  ring_nf; finish

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨0, 0, 4, 1, 0⟩) (by execute fm 7)
  apply progress_nonhalt_simple (fm := fm) (A := ℕ × ℕ)
    (fun ⟨c, d⟩ ↦ ⟨0, 0, c+d+3, d+1, 0⟩) ⟨1, 0⟩
  intro ⟨c, d⟩; exact ⟨⟨c+d+2, d+1⟩, by
    show ⟨0, 0, c+d+3, d+1, 0⟩ [fm]⊢⁺ ⟨0, 0, (c+d+2)+(d+1)+3, (d+1)+1, 0⟩
    have h := @main_trans c d
    rw [show c + 2 * d + 6 = (c + d + 2) + (d + 1) + 3 from by ring,
        show d + 2 = (d + 1) + 1 from by ring] at h
    exact h⟩

end Sz21_140_unofficial_62
