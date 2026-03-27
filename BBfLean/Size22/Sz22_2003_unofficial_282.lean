import BBfLean.FM

/-!
# sz22_2003_unofficial #282: [14/15, 66/7, 1/3, 25/2, 1/55, 3/5]

Vector representation:
```
 1 -1 -1  1  0
 1  1  0 -1  1
 0 -1  0  0  0
-1  0  2  0  0
 0  0 -1  0 -1
 0  1 -1  0  0
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_282

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a, b+1, c+1, d, e⟩ => some ⟨a+1, b, c, d+1, e⟩
  | ⟨a, b, c, d+1, e⟩ => some ⟨a+1, b+1, c, d, e+1⟩
  | ⟨a, b+1, c, d, e⟩ => some ⟨a, b, c, d, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b, c+2, d, e⟩
  | ⟨a, b, c+1, d, e+1⟩ => some ⟨a, b, c, d, e⟩
  | ⟨a, b, c+1, d, e⟩ => some ⟨a, b+1, c, d, e⟩
  | _ => none

-- R1/R2 chain: k rounds from (a, 1, c+k, 0, e) to (a+2k, 1, c, 0, e+k)
theorem r1r2_chain : ∀ k a c e,
    ⟨a, 1, c + k, 0, e⟩ [fm]⊢* ⟨a + 2 * k, (1 : ℕ), c, 0, e + k⟩ := by
  intro k; induction k with
  | zero => intro a c e; simp; exists 0
  | succ k ih =>
    intro a c e
    rw [show c + (k + 1) = (c + k) + 1 from by omega]
    step fm; step fm
    -- Goal: (a+1+1, 1, c+k, 0, e+1) ⊢* (a+2*(k+1), 1, c, 0, e+(k+1))
    rw [show a + 2 * (k + 1) = (a + 1 + 1) + 2 * k from by omega,
        show e + (k + 1) = (e + 1) + k from by omega]
    exact ih (a + 1 + 1) c (e + 1)

-- R4 chain: k steps of R4 from (k, 0, c, 0, e) -> (0, 0, c+2k, 0, e)
theorem r4_chain : ∀ k c e,
    ⟨k, 0, c, 0, e⟩ [fm]⊢* ⟨(0 : ℕ), 0, c + 2 * k, 0, e⟩ := by
  intro k; induction k with
  | zero => intro c e; exists 0
  | succ k ih =>
    intro c e
    step fm
    rw [show c + 2 * (k + 1) = c + 2 + 2 * k from by omega]
    exact ih (c + 2) e

-- R5 chain: k steps of R5 from (0, 0, c+k, 0, k) -> (0, 0, c, 0, 0)
theorem r5_chain : ∀ k c,
    ⟨0, 0, c + k, 0, k⟩ [fm]⊢* ⟨(0 : ℕ), 0, c, 0, 0⟩ := by
  intro k; induction k with
  | zero => intro c; exists 0
  | succ k ih =>
    intro c
    rw [show c + (k + 1) = (c + k) + 1 from by omega]
    step fm
    exact ih c

-- Main transition: (0, 0, C+2, 0, 0) ⊢⁺ (0, 0, 3*C+3, 0, 0)
-- Phase 1: R6 gives (0, 1, C+1, 0, 0)
-- Phase 2: (C+1) rounds of (R1, R2) gives (2*(C+1), 1, 0, 0, C+1)
-- Phase 3: R3 gives (2*(C+1), 0, 0, 0, C+1)
-- Phase 4: R4 * 2*(C+1) gives (0, 0, 4*(C+1), 0, C+1)
-- Phase 5: R5 * (C+1) gives (0, 0, 3*(C+1), 0, 0) = (0, 0, 3*C+3, 0, 0)
theorem main_trans (C : ℕ) :
    ⟨0, 0, C + 2, 0, 0⟩ [fm]⊢⁺ ⟨(0 : ℕ), 0, 3 * C + 3, 0, 0⟩ := by
  -- Phase 1: R6
  apply step_stepStar_stepPlus
  · show fm ⟨0, 0, (C + 1) + 1, 0, 0⟩ = some ⟨0, 1, C + 1, 0, 0⟩
    rfl
  -- Phase 2: (C+1) rounds of (R1, R2)
  rw [show C + 1 = 0 + (C + 1) from by omega]
  apply stepStar_trans
  · exact r1r2_chain (C + 1) 0 0 0
  -- Phase 3: R3
  apply stepStar_trans
  · apply step_stepStar
    show fm ⟨0 + 2 * (C + 1), 1, 0, 0, 0 + (C + 1)⟩ =
         some ⟨0 + 2 * (C + 1), 0, 0, 0, 0 + (C + 1)⟩
    rfl
  -- Phase 4: R4 * 2*(C+1)
  apply stepStar_trans
  · exact r4_chain (0 + 2 * (C + 1)) 0 (0 + (C + 1))
  -- Phase 5: R5 * (C+1)
  rw [show 0 + 2 * (0 + 2 * (C + 1)) = 3 * C + 3 + (0 + (C + 1)) from by omega,
      show 0 + (C + 1) = C + 1 from by omega]
  exact r5_chain (C + 1) (3 * C + 3)

-- Bootstrap: c₀ reaches (0, 0, 2, 0, 0)
theorem bootstrap : c₀ [fm]⊢* ⟨(0 : ℕ), 0, 2, 0, 0⟩ := by
  unfold c₀
  execute fm 1

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts bootstrap
  apply progress_nonhalt (P := fun q ↦ ∃ n, q = ⟨(0 : ℕ), 0, n + 2, 0, 0⟩)
  · intro q ⟨n, hq⟩
    subst hq
    exact ⟨⟨0, 0, 3 * n + 3, 0, 0⟩,
      ⟨3 * n + 1, by simp [Nat.add_assoc]⟩,
      main_trans n⟩
  · exact ⟨0, rfl⟩

end Sz22_2003_unofficial_282
