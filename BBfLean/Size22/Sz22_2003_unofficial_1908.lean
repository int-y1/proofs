import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #1908: [9/35, 8/5, 55/6, 7/11, 15/2]

Vector representation:
```
 0  2 -1 -1  0
 3  0 -1  0  0
-1 -1  1  0  1
 0  0  0  1 -1
-1  1  1  0  0
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_1908

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a, b, c+1, d+1, e⟩ => some ⟨a, b+2, c, d, e⟩
  | ⟨a, b, c+1, d, e⟩ => some ⟨a+3, b, c, d, e⟩
  | ⟨a+1, b+1, c, d, e⟩ => some ⟨a, b, c+1, d, e+1⟩
  | ⟨a, b, c, d, e+1⟩ => some ⟨a, b, c, d+1, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b+1, c+1, d, e⟩
  | _ => none

-- R4 repeated: move e to d when b=0, c=0.
theorem e_to_d : ∀ k d, ⟨a, 0, 0, d, e + k⟩ [fm]⊢* ⟨a, 0, 0, d + k, e⟩ := by
  intro k; induction' k with k ih <;> intro d
  · exists 0
  · rw [show e + (k + 1) = (e + k) + 1 from by ring]
    step fm
    apply stepStar_trans (ih (d + 1))
    ring_nf; finish

-- R1/R3 interleaving: each pair does a-=1, b+=1, d-=1, e+=1.
theorem r1r3_chain : ∀ k, ∀ b d e, ⟨a + k, b, 1, d + k, e⟩ [fm]⊢* ⟨a, b + k, 1, d, e + k⟩ := by
  intro k; induction' k with k ih <;> intro b d e
  · exists 0
  · rw [show a + (k + 1) = (a + k) + 1 from by ring,
        show d + (k + 1) = (d + k) + 1 from by ring]
    step fm
    step fm
    apply stepStar_trans (ih (b + 1) d (e + 1))
    ring_nf; finish

-- R3/R2 alternation draining b when c=0, d=0.
theorem r3r2_chain : ∀ k, ∀ a e, ⟨a + 1, k, 0, 0, e⟩ [fm]⊢* ⟨a + 2 * k + 1, 0, 0, 0, e + k⟩ := by
  intro k; induction' k with k ih <;> intro a e
  · exists 0
  · step fm
    step fm
    apply stepStar_trans (ih (a + 2) (e + 1))
    ring_nf; finish

-- Main transition for e >= 1
theorem main_trans_succ : ⟨m + e + 2, 0, 0, 0, e + 1⟩ [fm]⊢⁺ ⟨m + 2 * e + 7, 0, 0, 0, 2 * e + 3⟩ := by
  -- Phase 1: e_to_d. (m+e+2, 0, 0, 0, e+1) →* (m+e+2, 0, 0, e+1, 0)
  have phase1 : ⟨m + e + 2, 0, 0, 0, e + 1⟩ [fm]⊢* ⟨m + e + 2, 0, 0, e + 1, 0⟩ := by
    rw [show (e + 1 : ℕ) = 0 + (e + 1) from by ring]
    exact e_to_d (e + 1) 0
  -- R5: (m+e+2, 0, 0, e+1, 0) → (m+e+1, 1, 1, e+1, 0)
  have r5_step : ⟨m + e + 2, 0, 0, e + 1, 0⟩ [fm]⊢ ⟨m + e + 1, 1, 1, e + 1, 0⟩ := by
    show fm ⟨(m + e + 1) + 1, 0, 0, e + 1, 0⟩ = _; simp [fm]
  -- Phase 2: R1/R3 chain
  have phase2 : ⟨m + e + 1, 1, 1, e + 1, 0⟩ [fm]⊢* ⟨m, e + 2, 1, 0, e + 1⟩ := by
    rw [show m + e + 1 = m + (e + 1) from by ring,
        show e + 1 = 0 + (e + 1) from by ring]
    have h := @r1r3_chain m (e + 1) 1 0 0
    simp only [Nat.zero_add] at h
    convert h using 2; all_goals ring_nf
  -- R2: (m, e+2, 1, 0, e+1) → (m+3, e+2, 0, 0, e+1)
  have r2_step : ⟨m, e + 2, 1, 0, e + 1⟩ [fm]⊢ ⟨m + 3, e + 2, 0, 0, e + 1⟩ := by
    show fm ⟨m, e + 2, 0 + 1, 0, e + 1⟩ = _; simp [fm]
  -- Phase 3: R3/R2 chain
  have phase3 : ⟨m + 3, e + 2, 0, 0, e + 1⟩ [fm]⊢* ⟨m + 2 * e + 7, 0, 0, 0, 2 * e + 3⟩ := by
    rw [show m + 3 = (m + 2) + 1 from by ring]
    have h := r3r2_chain (e + 2) (m + 2) (e + 1)
    convert h using 2; all_goals ring_nf
  -- Compose all phases
  apply stepStar_stepPlus_stepPlus phase1
  exact step_stepStar_stepPlus r5_step
    (stepStar_trans phase2 (stepStar_trans (step_stepStar r2_step) phase3))

-- Main transition for e = 0
theorem main_trans_zero : ⟨m + 1, 0, 0, 0, 0⟩ [fm]⊢⁺ ⟨m + 5, 0, 0, 0, 1⟩ := by
  execute fm 4

-- Combined main transition
theorem main_trans : ⟨m + e + 1, 0, 0, 0, e⟩ [fm]⊢⁺ ⟨m + 2 * e + 5, 0, 0, 0, 2 * e + 1⟩ := by
  rcases e with _ | e
  · simp only [Nat.add_zero, Nat.mul_zero]
    exact main_trans_zero
  · rw [show m + (e + 1) + 1 = m + e + 2 from by ring,
        show m + 2 * (e + 1) + 5 = m + 2 * e + 7 from by ring,
        show 2 * (e + 1) + 1 = 2 * e + 3 from by ring]
    exact main_trans_succ

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨1, 0, 0, 0, 0⟩) (by exists 0)
  apply progress_nonhalt_simple (fm := fm) (A := ℕ × ℕ)
    (fun ⟨m, e⟩ ↦ ⟨m + e + 1, 0, 0, 0, e⟩) ⟨0, 0⟩
  intro ⟨m, e⟩
  refine ⟨⟨m + 3, 2 * e + 1⟩, ?_⟩
  show ⟨m + e + 1, 0, 0, 0, e⟩ [fm]⊢⁺ ⟨(m + 3) + (2 * e + 1) + 1, 0, 0, 0, 2 * e + 1⟩
  rw [show (m + 3) + (2 * e + 1) + 1 = m + 2 * e + 5 from by ring]
  exact main_trans
