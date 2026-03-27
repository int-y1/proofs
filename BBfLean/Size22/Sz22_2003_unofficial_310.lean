import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #310: [154/15, 1/3, 21/2, 25/7, 1/55, 3/5]

Vector representation:
```
 1 -1 -1  1  1
 0 -1  0  0  0
-1  1  0  1  0
 0  0  2 -1  0
 0  0 -1  0 -1
 0  1 -1  0  0
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_310

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a, b+1, c+1, d, e⟩ => some ⟨a+1, b, c, d+1, e+1⟩
  | ⟨a, b+1, c, d, e⟩ => some ⟨a, b, c, d, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b+1, c, d+1, e⟩
  | ⟨a, b, c, d+1, e⟩ => some ⟨a, b, c+2, d, e⟩
  | ⟨a, b, c+1, d, e+1⟩ => some ⟨a, b, c, d, e⟩
  | ⟨a, b, c+1, d, e⟩ => some ⟨a, b+1, c, d, e⟩
  | _ => none

-- R1+R3 chain: (0, 1, k, d, e) →* (0, 1, 0, d+2k, e+k)
theorem r1r3_chain : ∀ k d e, ⟨(0:ℕ), 1, k, d, e⟩ [fm]⊢* (⟨0, 1, 0, d + 2*k, e + k⟩ : Q) := by
  intro k; induction k with
  | zero => intro d e; exists 0
  | succ k ih =>
    intro d e
    step fm; step fm
    apply stepStar_trans (ih _ _)
    ring_nf; finish

-- R4 chain: (0, 0, c, k, e) →* (0, 0, c+2k, 0, e)
theorem r4_chain : ∀ k c, ⟨(0:ℕ), 0, c, k, e⟩ [fm]⊢* (⟨0, 0, c + 2*k, 0, e⟩ : Q) := by
  intro k; induction k with
  | zero => intro c; exists 0
  | succ k ih =>
    intro c
    step fm
    apply stepStar_trans (ih _)
    ring_nf; finish

-- R5 chain: (0, 0, c+k, 0, k) →* (0, 0, c, 0, 0)
-- We rewrite c+k to expose the +1 in both c and e positions
theorem r5_chain : ∀ k c, ⟨(0:ℕ), 0, c + k, 0, k⟩ [fm]⊢* (⟨0, 0, c, 0, 0⟩ : Q) := by
  intro k; induction k with
  | zero => intro c; exists 0
  | succ k ih =>
    intro c
    -- We need to show fm ⟨0, 0, c+(k+1), 0, k+1⟩ = some ⟨0, 0, c+k, 0, k⟩
    -- Rule 5 matches: (a, b, c'+1, d, e'+1) with c' = c+k-1... no
    -- c+(k+1) = (c+k)+1 which gives pattern c'+1 with c'=c+k
    -- k+1 gives e'+1 with e'=k
    -- So rule 5 fires: result is (0, 0, c+k, 0, k)
    have h : fm ⟨0, 0, (c+k)+1, 0, k+1⟩ = some ⟨0, 0, c+k, 0, k⟩ := by
      unfold fm; simp
    rw [show c + (k + 1) = (c + k) + 1 from by ring]
    exact stepStar_trans (step_stepStar h) (ih c)

-- Full cycle: (0, 0, c+2, 0, 0) →* (0, 0, 3*c+3, 0, 0)
theorem full_star (c : ℕ) :
    (⟨0, 0, c+2, 0, 0⟩ : Q) [fm]⊢* ⟨0, 0, 3*c+3, 0, 0⟩ := by
  -- Phase 1: R6: (0, 0, (c+1)+1, 0, 0) → (0, 1, c+1, 0, 0)
  step fm
  -- Phase 2: R1+R3 chain (c+1 times)
  apply stepStar_trans (r1r3_chain (c+1) 0 0)
  -- Now at (0, 1, 0, 2(c+1), c+1)
  show (⟨0, 1, 0, 0 + 2 * (c + 1), 0 + (c + 1)⟩ : Q) [fm]⊢* _
  simp only [Nat.zero_add]
  -- Phase 3: R2
  step fm
  -- Now at (0, 0, 0, 2(c+1), c+1)
  -- Phase 4: R4 chain
  apply stepStar_trans (r4_chain (e := c+1) (2*(c+1)) 0)
  -- Now at (0, 0, 0+2*(2*(c+1)), 0, c+1) = (0, 0, 4c+4, 0, c+1)
  show (⟨0, 0, 0 + 2 * (2 * (c + 1)), 0, c + 1⟩ : Q) [fm]⊢* _
  -- Phase 5: R5 chain (c+1 times)
  -- Need: (0, 0, (3c+3) + (c+1), 0, c+1) →* (0, 0, 3c+3, 0, 0)
  rw [show 0 + 2 * (2 * (c + 1)) = (3 * c + 3) + (c + 1) from by ring]
  exact r5_chain (c+1) (3*c+3)

theorem full_cycle (c : ℕ) :
    (⟨0, 0, c+2, 0, 0⟩ : Q) [fm]⊢⁺ ⟨0, 0, 3*c+3, 0, 0⟩ := by
  apply stepStar_stepPlus (full_star c)
  simp [Q]
  omega

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := (⟨0, 0, 2, 0, 0⟩ : Q))
  · execute fm 3
  apply progress_nonhalt (fm := fm)
    (P := fun q ↦ ∃ c, q = (⟨0, 0, c+2, 0, 0⟩ : Q))
  · intro q ⟨c, hq⟩; subst hq
    exact ⟨⟨0, 0, 3*c+3, 0, 0⟩, ⟨3*c+1, by ring_nf⟩, full_cycle c⟩
  · exact ⟨0, by rfl⟩
