import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #279: [14/15, 363/2, 1/3, 25/11, 1/35, 3/5]

Vector representation:
```
 1 -1 -1  1  0
-1  1  0  0  2
 0 -1  0  0  0
 0  0  2  0 -1
 0  0 -1 -1  0
 0  1 -1  0  0
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_279

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a, b+1, c+1, d, e⟩ => some ⟨a+1, b, c, d+1, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b+1, c, d, e+2⟩
  | ⟨a, b+1, c, d, e⟩ => some ⟨a, b, c, d, e⟩
  | ⟨a, b, c, d, e+1⟩ => some ⟨a, b, c+2, d, e⟩
  | ⟨a, b, c+1, d+1, e⟩ => some ⟨a, b, c, d, e⟩
  | ⟨a, b, c+1, d, e⟩ => some ⟨a, b+1, c, d, e⟩
  | _ => none

-- R1/R2 chain: k rounds of (R1, R2) from (0, 1, c+k, d, e)
-- Net per pair: c-=1, d+=1, e+=2
theorem r1r2_chain : ∀ k c d e,
    ⟨0, 1, c + k, d, e⟩ [fm]⊢* ⟨(0 : ℕ), 1, c, d + k, e + 2 * k⟩ := by
  intro k; induction k with
  | zero => intro c d e; exists 0
  | succ k ih =>
    intro c d e
    rw [show c + (k + 1) = (c + k) + 1 from by omega]
    step fm; step fm
    have h := ih c (d + 1) (e + 2)
    rw [show d + 1 + k = d + (k + 1) from by omega,
        show e + 2 + 2 * k = e + 2 * (k + 1) from by omega] at h
    exact h

-- R4 chain: k steps of R4 from (0, 0, c, d, k)
-- Each R4: c+=2, e-=1
theorem r4_chain : ∀ k c d,
    ⟨0, 0, c, d, k⟩ [fm]⊢* ⟨(0 : ℕ), 0, c + 2 * k, d, 0⟩ := by
  intro k; induction k with
  | zero => intro c d; exists 0
  | succ k ih =>
    intro c d
    step fm
    have h := ih (c + 2) d
    rw [show c + 2 + 2 * k = c + 2 * (k + 1) from by omega] at h
    exact h

-- R5 chain: k steps of R5 from (0, 0, c+k, k, 0)
-- Each R5: c-=1, d-=1
theorem r5_chain : ∀ k c,
    ⟨0, 0, c + k, k, 0⟩ [fm]⊢* ⟨(0 : ℕ), 0, c, 0, 0⟩ := by
  intro k; induction k with
  | zero => intro c; exists 0
  | succ k ih =>
    intro c
    rw [show c + (k + 1) = (c + k) + 1 from by omega]
    step fm
    exact ih c

-- Main transition: (0, 0, C+2, 0, 0) ⊢⁺ (0, 0, 3*C+3, 0, 0)
-- Phase 1: R6, then (C+1) x (R1,R2), then R3
-- Phase 2: R4 * (2*C+2)
-- Phase 3: R5 * (C+1)
theorem main_trans (C : ℕ) :
    ⟨0, 0, C + 2, 0, 0⟩ [fm]⊢⁺ ⟨(0 : ℕ), 0, 3 * C + 3, 0, 0⟩ := by
  -- Phase 1a: R6
  apply step_stepStar_stepPlus
  · show fm ⟨0, 0, (C + 1) + 1, 0, 0⟩ = some ⟨0, 1, C + 1, 0, 0⟩
    simp [fm]
  -- Phase 1b: (C+1) x (R1, R2)
  apply stepStar_trans
  · have h := r1r2_chain (C + 1) 0 0 0
    simp only [Nat.zero_add] at h
    exact h
  -- Phase 1c: R3
  rw [show 2 * (C + 1) = 2 * C + 2 from by omega]
  apply stepStar_trans
  · apply step_stepStar
    show fm ⟨0, 1, 0, C + 1, 2 * C + 2⟩ = some ⟨0, 0, 0, C + 1, 2 * C + 2⟩
    simp [fm]
  -- Phase 2: R4 * (2*C+2)
  apply stepStar_trans
  · exact r4_chain (2 * C + 2) 0 (C + 1)
  -- Phase 3: R5 * (C+1)
  rw [show 0 + 2 * (2 * C + 2) = 3 * C + 3 + (C + 1) from by omega]
  exact r5_chain (C + 1) (3 * C + 3)

-- Bootstrap: c₀ reaches (0, 0, 4, 0, 0)
theorem bootstrap : c₀ [fm]⊢* ⟨(0 : ℕ), 0, 4, 0, 0⟩ := by
  unfold c₀
  execute fm 4

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts bootstrap
  apply progress_nonhalt (P := fun q ↦ ∃ n, q = ⟨(0 : ℕ), 0, n + 2, 0, 0⟩)
  · intro q ⟨n, hq⟩
    subst hq
    refine ⟨⟨0, 0, 3 * n + 3, 0, 0⟩, ⟨3 * n + 1, ?_⟩, main_trans n⟩
    simp only [Nat.add_assoc]
  · exact ⟨2, rfl⟩

end Sz22_2003_unofficial_279
