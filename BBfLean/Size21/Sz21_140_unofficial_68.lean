import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz21_140_unofficial #68: [4/15, 33/14, 275/2, 7/11, 3/7]

Vector representation:
```
 2 -1 -1  0  0
-1  1  0 -1  1
-1  0  2  0  1
 0  0  0  1 -1
 0  1  0 -1  0
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz21_140_unofficial_68

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a, b+1, c+1, d, e⟩ => some ⟨a+2, b, c, d, e⟩
  | ⟨a+1, b, c, d+1, e⟩ => some ⟨a, b+1, c, d, e+1⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b, c+2, d, e+1⟩
  | ⟨a, b, c, d, e+1⟩ => some ⟨a, b, c, d+1, e⟩
  | ⟨a, b, c, d+1, e⟩ => some ⟨a, b+1, c, d, e⟩
  | _ => none

-- R4 repeated: e → d transfer
theorem e_to_d : ∀ k, ∀ c d, ⟨0, 0, c, d, k⟩ [fm]⊢* ⟨0, 0, c, d+k, 0⟩ := by
  intro k; induction' k with k h <;> intro c d
  · exists 0
  rw [show d + (k + 1) = (d + k) + 1 from by ring]
  step fm
  apply stepStar_trans (h c (d + 1))
  ring_nf; finish

-- R3 repeated: a → c+2, e+1
theorem r3_chain : ∀ k, ∀ c e, ⟨k, 0, c, 0, e⟩ [fm]⊢* ⟨0, 0, c+2*k, 0, e+k⟩ := by
  intro k; induction' k with k h <;> intro c e
  · exists 0
  step fm
  apply stepStar_trans (h (c+2) (e+1))
  ring_nf; finish

-- [R2,R1] chain: each round a→a+1, c→c-1, d→d-1, e→e+1
-- From (a+2, 0, c+k+1, k+1, e) to (a+k+3, 0, c, 0, e+k+1)
theorem r2r1_chain : ∀ k, ∀ a c e, ⟨a+2, 0, c+k+1, k+1, e⟩ [fm]⊢* ⟨a+k+3, 0, c, 0, e+k+1⟩ := by
  intro k; induction' k with k h <;> intro a c e
  · -- (a+2, 0, c+1, 1, e) →R2 (a+1, 1, c+1, 0, e+1) →R1 (a+3, 0, c, 0, e+1)
    step fm; step fm; finish
  · -- (a+2, 0, c+(k+2), k+2, e)
    -- R2: matches (a'+1, 0, c', d'+1, e) with a'=a+1 ≥ 1
    -- → (a+1, 1, c+(k+2), k+1, e+1)
    -- R1: matches (_, b'+1, c'+1, _, _) with c+(k+2) = (c+k+1)+1
    -- → (a+3, 0, c+k+1, k+1, e+1)
    rw [show c + (k + 1) + 1 = (c + (k + 1)) + 1 from by ring]
    step fm
    -- After R2: (a+1, 1, (c+(k+1))+1, k+1, e+1)
    step fm
    -- After R1: (a+1+2, 0, c+(k+1), k+1, e+1) = (a+3, 0, c+k+1, k+1, e+1)
    -- Need to apply h with a' = a+1
    rw [show a + 1 + 2 = (a + 1) + 2 from by ring]
    apply stepStar_trans (h (a+1) c (e+1))
    ring_nf; finish

-- Processing from (2, 0, c+d, d, 0) → (0, 0, c+2*d+4, 0, 2*d+2)
-- d=0: R3*2
-- d≥1: R2R1 chain then R3 chain
theorem process_chain : ∀ d, ∀ c, ⟨2, 0, c+d, d, 0⟩ [fm]⊢* ⟨0, 0, c+2*d+4, 0, 2*d+2⟩ := by
  intro d; induction' d with d ih <;> intro c
  · step fm; step fm; finish
  · -- (2, 0, c+(d+1), d+1, 0)
    -- r2r1_chain with k=d, a=0, c'=c, e=0:
    -- (0+2, 0, c+d+1, d+1, 0) →* (0+d+3, 0, c, 0, 0+d+1) = (d+3, 0, c, 0, d+1)
    rw [show c + (d + 1) = c + d + 1 from by ring]
    apply stepStar_trans (c₂ := ⟨d+3, 0, c, 0, d+1⟩)
    · have h := r2r1_chain d 0 c 0
      simp only [Nat.zero_add] at h; exact h
    -- r3_chain: (d+3, 0, c, 0, d+1) →* (0, 0, c+2*(d+3), 0, d+1+d+3)
    apply stepStar_trans (r3_chain (d+3) c (d+1))
    ring_nf; finish

-- Main transition
theorem main_trans (c e : ℕ) : ⟨0, 0, c+e+1, 0, e+1⟩ [fm]⊢⁺ ⟨0, 0, c+2*e+4, 0, 2*e+2⟩ := by
  -- Phase 1: e_to_d
  apply stepStar_stepPlus_stepPlus (c₂ := ⟨0, 0, c+e+1, e+1, 0⟩)
  · have h := e_to_d (e+1) (c+e+1) 0
    simp only [Nat.zero_add] at h; exact h
  -- R5 step (gives stepPlus)
  apply step_stepStar_stepPlus (c₂ := ⟨0, 1, c+e+1, e, 0⟩)
  · show fm ⟨0, 0, c+e+1, e+1, 0⟩ = some ⟨0, 1, c+e+1, e, 0⟩; simp [fm]
  -- R1 step
  apply stepStar_trans (c₂ := ⟨2, 0, c+e, e, 0⟩)
  · rw [show c + e + 1 = (c + e) + 1 from by ring]
    step fm; finish
  -- process_chain
  apply stepStar_trans (process_chain e c)
  ring_nf; finish

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨0, 0, 2, 0, 1⟩) (by execute fm 1)
  -- Canonical state: (0, 0, c+e+1, 0, e+1) parameterized by (c, e)
  -- Initial: (0, 0, 2, 0, 1) = (0, 0, 1+0+1, 0, 0+1) with (c,e) = (1,0)
  -- main_trans: (c,e) ↦ state (0,0,c+2*e+4,0,2*e+2) = (0,0,(c+2)+(2*e+1)+1,0,(2*e+1)+1)
  -- So next params = (c+2, 2*e+1)
  apply progress_nonhalt_simple (fm := fm) (A := ℕ × ℕ)
    (fun ⟨c, e⟩ ↦ ⟨0, 0, c+e+1, 0, e+1⟩) ⟨1, 0⟩
  intro ⟨c, e⟩; exact ⟨⟨c+2, 2*e+1⟩, by
    show ⟨0, 0, c+e+1, 0, e+1⟩ [fm]⊢⁺ ⟨0, 0, (c+2)+(2*e+1)+1, 0, (2*e+1)+1⟩
    have h := main_trans c e
    rw [show (c + 2) + (2 * e + 1) + 1 = c + 2 * e + 4 from by ring,
        show (2 * e + 1) + 1 = 2 * e + 2 from by ring]
    exact h⟩
