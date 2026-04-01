import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #1239: [5/6, 77/2, 392/55, 3/7, 5/3]

Vector representation:
```
-1 -1  1  0  0
-1  0  0  1  1
 3  0 -1  2 -1
 0  1  0 -1  0
 0 -1  1  0  0
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_1239

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a+1, b+1, c, d, e⟩ => some ⟨a, b, c+1, d, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b, c, d+1, e+1⟩
  | ⟨a, b, c+1, d, e+1⟩ => some ⟨a+3, b, c, d+2, e⟩
  | ⟨a, b, c, d+1, e⟩ => some ⟨a, b+1, c, d, e⟩
  | ⟨a, b+1, c, d, e⟩ => some ⟨a, b, c+1, d, e⟩
  | _ => none

-- R4 repeated: move d to b
theorem d_to_b : ∀ k b d e, ⟨(0 : ℕ), b, 0, d + k, e⟩ [fm]⊢* ⟨(0 : ℕ), b + k, 0, d, e⟩ := by
  intro k; induction' k with k ih <;> intro b d e
  · exists 0
  · rw [Nat.add_succ d k]
    step fm
    apply stepStar_trans (ih (b + 1) d e)
    ring_nf; finish

-- R2×3: drain 3 from a, add 3 to d and e
theorem r2_drain3 : ∀ c D e, ⟨(3 : ℕ), (0 : ℕ), c, D, e⟩ [fm]⊢* ⟨(0 : ℕ), (0 : ℕ), c, D + 3, e + 3⟩ := by
  intro c D e
  step fm; step fm; step fm
  ring_nf; finish

-- R3+R2×3 chain: each round (0,0,c+1,d,e+1) -> (0,0,c,d+5,e+3)
theorem r3r2_chain : ∀ k, ∀ c d e, ⟨(0 : ℕ), (0 : ℕ), c + k, d, e + 1⟩ [fm]⊢* ⟨(0 : ℕ), (0 : ℕ), c, d + 5 * k, e + 2 * k + 1⟩ := by
  intro k; induction' k with k ih <;> intro c d e
  · simp; exists 0
  · rw [show c + (k + 1) = (c + 1) + k from by ring]
    apply stepStar_trans (ih (c + 1) d e)
    rw [show e + 2 * k + 1 = (e + 2 * k) + 1 from by ring]
    -- R3: (0, 0, (c+1), d+5k, (e+2k)+1) -> (3, 0, c, d+5k+2, e+2k)
    apply stepStar_trans (step_stepStar
      (by simp [fm] : (⟨0, 0, c + 1, d + 5 * k, (e + 2 * k) + 1⟩ : Q) [fm]⊢ ⟨3, 0, c, d + 5 * k + 2, e + 2 * k⟩))
    -- R2×3
    apply stepStar_trans (r2_drain3 c (d + 5 * k + 2) (e + 2 * k))
    ring_nf; finish

-- Generalized middle phase with constraint
theorem gen_middle : ∀ d, ∀ c D e, 3 * (e + 1) ≥ d →
    ⟨(3 : ℕ), d, c, D, e + 1⟩ [fm]⊢* ⟨(0 : ℕ), (0 : ℕ), 0, 4 * d + 5 * c + D + 3, d + 2 * c + e + 4⟩ := by
  intro d; induction' d using Nat.strongRecOn with d ih
  intro c D e hconst
  rcases d with _ | _ | _ | d
  · -- d = 0: R2×3 then R3+R2×3 chain
    apply stepStar_trans (r2_drain3 c D (e + 1))
    rw [show e + 1 + 3 = (e + 3) + 1 from by ring,
        show c = 0 + c from by ring]
    apply stepStar_trans (r3r2_chain c 0 (D + 3) (e + 3))
    ring_nf; finish
  · -- d = 1: R1 then R2×2 then R3+R2×3 chain
    -- R1: (3, 1, c, D, e+1) -> (2, 0, c+1, D, e+1)
    apply stepStar_trans (step_stepStar
      (by simp [fm] : (⟨3, 1, c, D, e + 1⟩ : Q) [fm]⊢ ⟨2, 0, c + 1, D, e + 1⟩))
    -- R2×2: (2, 0, c+1, D, e+1) -> (0, 0, c+1, D+2, e+3)
    apply stepStar_trans (step_stepStar
      (by simp [fm] : (⟨2, 0, c + 1, D, e + 1⟩ : Q) [fm]⊢ ⟨1, 0, c + 1, D + 1, e + 2⟩))
    apply stepStar_trans (step_stepStar
      (by simp [fm] : (⟨1, 0, c + 1, D + 1, e + 2⟩ : Q) [fm]⊢ ⟨0, 0, c + 1, D + 2, e + 3⟩))
    rw [show c + 1 = 0 + (c + 1) from by ring,
        show e + 3 = (e + 2) + 1 from by ring]
    apply stepStar_trans (r3r2_chain (c + 1) 0 (D + 2) (e + 2))
    ring_nf; finish
  · -- d = 2: R1×2 then R2 then R3+R2×3 chain
    -- R1: (3, 2, c, D, e+1) -> (2, 1, c+1, D, e+1)
    apply stepStar_trans (step_stepStar
      (by simp [fm] : (⟨3, 2, c, D, e + 1⟩ : Q) [fm]⊢ ⟨2, 1, c + 1, D, e + 1⟩))
    -- R1: (2, 1, c+1, D, e+1) -> (1, 0, c+2, D, e+1)
    apply stepStar_trans (step_stepStar
      (by simp [fm] : (⟨2, 1, c + 1, D, e + 1⟩ : Q) [fm]⊢ ⟨1, 0, c + 2, D, e + 1⟩))
    -- R2: (1, 0, c+2, D, e+1) -> (0, 0, c+2, D+1, e+2)
    apply stepStar_trans (step_stepStar
      (by simp [fm] : (⟨1, 0, c + 2, D, e + 1⟩ : Q) [fm]⊢ ⟨0, 0, c + 2, D + 1, e + 2⟩))
    rw [show c + 2 = 0 + (c + 2) from by ring,
        show e + 2 = (e + 1) + 1 from by ring]
    apply stepStar_trans (r3r2_chain (c + 2) 0 (D + 1) (e + 1))
    ring_nf; finish
  · -- d + 3
    rcases e with _ | e
    · -- e = 0: constraint 3*1 >= d+3 forces d = 0
      have hd0 : d = 0 := by omega
      subst hd0
      -- State: (3, 3, c, D, 1)
      -- R1×3: (0, 0, c+3, D, 1)
      apply stepStar_trans (step_stepStar
        (by simp [fm] : (⟨3, 3, c, D, 1⟩ : Q) [fm]⊢ ⟨2, 2, c + 1, D, 1⟩))
      apply stepStar_trans (step_stepStar
        (by simp [fm] : (⟨2, 2, c + 1, D, 1⟩ : Q) [fm]⊢ ⟨1, 1, c + 2, D, 1⟩))
      apply stepStar_trans (step_stepStar
        (by simp [fm] : (⟨1, 1, c + 2, D, 1⟩ : Q) [fm]⊢ ⟨0, 0, c + 3, D, 1⟩))
      -- R3: (0, 0, (c+2)+1, D, 0+1) -> (3, 0, c+2, D+2, 0)
      apply stepStar_trans (step_stepStar
        (by simp [fm] : (⟨0, 0, c + 3, D, 1⟩ : Q) [fm]⊢ ⟨3, 0, c + 2, D + 2, 0⟩))
      -- R2×3: (3, 0, c+2, D+2, 0) -> (0, 0, c+2, D+5, 3)
      apply stepStar_trans (r2_drain3 (c + 2) (D + 2) 0)
      rw [show c + 2 = 0 + (c + 2) from by ring,
          show (0 : ℕ) + 3 = 2 + 1 from by ring]
      apply stepStar_trans (r3r2_chain (c + 2) 0 (D + 2 + 3) 2)
      ring_nf; finish
    · -- e + 1: state (3, d+3, c, D, e+2)
      -- R1×3
      apply stepStar_trans (step_stepStar
        (by simp [fm] : (⟨3, d + 3, c, D, e + 2⟩ : Q) [fm]⊢ ⟨2, d + 2, c + 1, D, e + 2⟩))
      apply stepStar_trans (step_stepStar
        (by simp [fm] : (⟨2, d + 2, c + 1, D, e + 2⟩ : Q) [fm]⊢ ⟨1, d + 1, c + 2, D, e + 2⟩))
      apply stepStar_trans (step_stepStar
        (by simp [fm] : (⟨1, d + 1, c + 2, D, e + 2⟩ : Q) [fm]⊢ ⟨0, d, c + 3, D, e + 2⟩))
      -- R3: (0, d, (c+2)+1, D, (e+1)+1) -> (3, d, c+2, D+2, e+1)
      rw [show e + 2 = (e + 1) + 1 from by ring]
      apply stepStar_trans (step_stepStar
        (by simp [fm] : (⟨0, d, c + 3, D, (e + 1) + 1⟩ : Q) [fm]⊢ ⟨3, d, c + 2, D + 2, e + 1⟩))
      -- Apply IH
      apply stepStar_trans (ih d (by omega) (c + 2) (D + 2) e (by omega))
      ring_nf; finish

-- Main transition
theorem main_transition (d e : ℕ) (hconst : 3 * (e + 2) ≥ d + 3) :
    ⟨(0 : ℕ), (0 : ℕ), 0, d + 1, e + 2⟩ [fm]⊢⁺
    ⟨(0 : ℕ), (0 : ℕ), 0, 4 * d + 5, d + e + 4⟩ := by
  -- Phase 1: R4 × (d+1)
  rw [show d + 1 = 0 + (d + 1) from by ring]
  apply stepStar_stepPlus_stepPlus (d_to_b (d + 1) 0 0 (e + 2))
  rw [show (0 : ℕ) + (d + 1) = d + 1 from by ring]
  -- State: (0, d+1, 0, 0, e+2)
  -- Phase 2: R5
  apply step_stepStar_stepPlus
    (by simp [fm] : (⟨0, d + 1, 0, 0, e + 2⟩ : Q) [fm]⊢ ⟨0, d, 1, 0, e + 2⟩)
  -- State: (0, d, 1, 0, e+2)
  -- Phase 3: R3
  rw [show e + 2 = (e + 1) + 1 from by ring]
  apply stepStar_trans (step_stepStar
    (by simp [fm] : (⟨0, d, 1, 0, (e + 1) + 1⟩ : Q) [fm]⊢ ⟨3, d, 0, 2, e + 1⟩))
  -- State: (3, d, 0, 2, e+1)
  -- Phase 4: gen_middle
  apply stepStar_trans (gen_middle d 0 2 e (by omega))
  ring_nf; finish

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨0, 0, 0, 5, 3⟩) (by execute fm 7)
  apply progress_nonhalt (fm := fm)
    (P := fun q ↦ ∃ d e, q = ⟨0, 0, 0, d + 1, e + 2⟩ ∧ 3 * (e + 2) ≥ d + 3)
  · intro q ⟨d, e, hq, hconst⟩; subst hq
    refine ⟨⟨0, 0, 0, 4 * d + 5, d + e + 4⟩, ⟨4 * d + 4, d + e + 2, ?_, ?_⟩, ?_⟩
    · ring_nf
    · omega
    · exact main_transition d e hconst
  · exact ⟨4, 1, rfl, by omega⟩

end Sz22_2003_unofficial_1239
