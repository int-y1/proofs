import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz21_140_unofficial #61: [4/15, 3/14, 55/2, 49/5, 10/11]

Vector representation:
```
 2 -1 -1  0  0
-1  1  0 -1  0
-1  0  1  0  1
 0  0 -1  2  0
 1  0  1  0 -1
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz21_140_unofficial_61

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a, b+1, c+1, d, e⟩ => some ⟨a+2, b, c, d, e⟩
  | ⟨a+1, b, c, d+1, e⟩ => some ⟨a, b+1, c, d, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b, c+1, d, e+1⟩
  | ⟨a, b, c+1, d, e⟩ => some ⟨a, b, c, d+2, e⟩
  | ⟨a, b, c, d, e+1⟩ => some ⟨a+1, b, c+1, d, e⟩
  | _ => none

-- R3 chain: (a+k, 0, c, 0, e) →* (a, 0, c+k, 0, e+k)
theorem r3_chain : ∀ k, ∀ a c e, ⟨a+k, 0, c, 0, e⟩ [fm]⊢* ⟨a, 0, c+k, 0, e+k⟩ := by
  intro k; induction k with
  | zero => intro a c e; exists 0
  | succ k ih =>
    intro a c e
    rw [show a + (k + 1) = (a + k) + 1 from by ring]
    step fm
    apply stepStar_trans (ih a _ _)
    ring_nf; finish

-- R4 chain: (0, 0, c+k, d, e) →* (0, 0, c, d+2*k, e)
theorem r4_chain : ∀ k, ∀ c d e, ⟨0, 0, c+k, d, e⟩ [fm]⊢* ⟨0, 0, c, d+2*k, e⟩ := by
  intro k; induction k with
  | zero => intro c d e; exists 0
  | succ k ih =>
    intro c d e
    rw [show c + (k + 1) = (c + k) + 1 from by ring]
    step fm
    apply stepStar_trans (ih c _ e)
    ring_nf; finish

-- Drain b: (A+1, k, 0, 0, E) →* (A+1+k, 0, 0, 0, E+k)
theorem drain_b : ∀ k, ∀ A E, ⟨A+1, k, 0, 0, E⟩ [fm]⊢* ⟨A+1+k, 0, 0, 0, E+k⟩ := by
  intro k; induction k with
  | zero => intro A E; exists 0
  | succ k ih =>
    intro A E
    rw [show k + 1 = k + 1 from rfl]
    step fm; step fm
    -- After R3, R1: (A+2, k, 0, 0, E+1)
    -- IH: (A'+1, k, 0, 0, E') →* (A'+1+k, 0, 0, 0, E'+k)
    -- with A' = A+1, E' = E+1: ((A+1)+1, k, 0, 0, E+1) →* ((A+1)+1+k, 0, 0, 0, (E+1)+k)
    rw [show A + 2 = (A + 1) + 1 from by ring]
    apply stepStar_trans (ih (A + 1) (E + 1))
    ring_nf; finish

-- First drain round (B=0): (0, 0, 0, D+3, E+1) →* (0, 2, 0, D, E)
theorem first_round : ∀ D E, ⟨0, 0, 0, D+3, E+1⟩ [fm]⊢* ⟨0, 2, 0, D, E⟩ := by
  intro D E
  step fm; step fm; step fm; step fm; step fm; finish

-- Subsequent drain round (B≥1): (0, B+1, 0, D+3, E+1) →* (0, B+3, 0, D, E)
theorem drain_round : ∀ B D E, ⟨0, B+1, 0, D+3, E+1⟩ [fm]⊢* ⟨0, B+3, 0, D, E⟩ := by
  intro B D E
  step fm; step fm; step fm; step fm; step fm; finish

-- Tail D=0: (0, B+2, 0, 0, E+1) →* (B+4, 0, 0, 0, E+B+1)
theorem tail0 : ∀ B E, ⟨0, B+2, 0, 0, E+1⟩ [fm]⊢* ⟨B+4, 0, 0, 0, E+B+1⟩ := by
  intro B E
  step fm; step fm
  -- (3, B+1, 0, 0, E) = ((B+1)+1+1, ...) hmm. Let me use drain_b directly.
  -- drain_b (B+1) 2 E: ((2)+1, (B+1), 0, 0, E) →* ((2)+1+(B+1), 0, 0, 0, E+(B+1))
  rw [show (3 : ℕ) = 2 + 1 from by ring]
  apply stepStar_trans (drain_b (B + 1) 2 E)
  ring_nf; finish

-- Tail D=1: (0, B+2, 0, 1, E+1) →* (B+4, 0, 0, 0, E+B+2)
theorem tail1 : ∀ B E, ⟨0, B+2, 0, 1, E+1⟩ [fm]⊢* ⟨B+4, 0, 0, 0, E+B+2⟩ := by
  intro B E
  step fm; step fm; step fm
  -- (2, B+2, 0, 0, E) = ((1)+1, (B+2), 0, 0, E)
  rw [show (2 : ℕ) = 1 + 1 from by ring]
  apply stepStar_trans (drain_b (B + 2) 1 E)
  ring_nf; finish

-- Tail D=2: (0, B+2, 0, 2, E+1) →* (B+4, 0, 0, 0, E+B+3)
theorem tail2 : ∀ B E, ⟨0, B+2, 0, 2, E+1⟩ [fm]⊢* ⟨B+4, 0, 0, 0, E+B+3⟩ := by
  intro B E
  step fm; step fm; step fm; step fm
  -- (1, B+3, 0, 0, E) = ((0)+1, (B+3), 0, 0, E)
  rw [show (1 : ℕ) = 0 + 1 from by ring]
  apply stepStar_trans (drain_b (B + 3) 0 E)
  ring_nf; finish

-- Phase 3 by strong induction on D
theorem phase3_exists : ∀ D, ∀ B E, 3 * E ≥ D + 3 →
    ∃ A E', A ≥ 4 ∧ E' ≥ 1 ∧ (⟨0, B+2, 0, D, E⟩ [fm]⊢* ⟨A, 0, 0, 0, E'⟩) := by
  intro D; induction D using Nat.strongRecOn with
  | ind D ih =>
    intro B E hE
    match D with
    | 0 =>
      obtain ⟨E', rfl⟩ : ∃ E', E = E' + 1 := ⟨E - 1, by omega⟩
      exact ⟨B + 4, E' + B + 1, by omega, by omega, tail0 B E'⟩
    | 1 =>
      obtain ⟨E', rfl⟩ : ∃ E', E = E' + 1 := ⟨E - 1, by omega⟩
      exact ⟨B + 4, E' + B + 2, by omega, by omega, tail1 B E'⟩
    | 2 =>
      obtain ⟨E', rfl⟩ : ∃ E', E = E' + 1 := ⟨E - 1, by omega⟩
      exact ⟨B + 4, E' + B + 3, by omega, by omega, tail2 B E'⟩
    | D + 3 =>
      obtain ⟨E', rfl⟩ : ∃ E', E = E' + 1 := ⟨E - 1, by omega⟩
      have hround : ⟨0, B + 2, 0, D + 3, E' + 1⟩ [fm]⊢* ⟨0, B + 4, 0, D, E'⟩ := by
        rw [show B + 2 = (B + 1) + 1 from by ring]
        have h := drain_round (B + 1) D E'
        rw [show B + 1 + 3 = B + 4 from by ring] at h
        exact h
      obtain ⟨A, E'', hA, hE'', hstep⟩ := ih D (by omega) (B + 2) E' (by omega)
      exact ⟨A, E'', hA, hE'', stepStar_trans hround hstep⟩

-- Full transition: (a+2, 0, 0, 0, e+1) ⊢⁺ some (A, 0, 0, 0, E') with A ≥ 4, E' ≥ 1
theorem main_trans (a e : ℕ) :
    ∃ A E', A ≥ 4 ∧ E' ≥ 1 ∧ (⟨a + 2, 0, 0, 0, e + 1⟩ [fm]⊢⁺ ⟨A, 0, 0, 0, E'⟩) := by
  -- Build the full ⊢* chain, then convert first step to ⊢⁺
  -- R3 chain: (a+2, 0, 0, 0, e+1) →* (0, 0, a+2, 0, a+e+3)
  have h_r3 := r3_chain (a + 2) 0 0 (e + 1)
  simp only [Nat.zero_add] at h_r3
  -- R4 chain: (0, 0, a+2, 0, a+e+3) →* (0, 0, 0, 2*(a+2), a+e+3)
  have h_r4 := r4_chain (a + 2) 0 0 (a + e + 3)
  simp only [Nat.zero_add] at h_r4
  -- Normalize: 2*(a+2) = 2a+4
  -- First round: (0, 0, 0, 2a+4, a+e+3) = (0, 0, 0, (2a+1)+3, (a+e+2)+1)
  -- →* (0, 2, 0, 2a+1, a+e+2)
  -- phase3_exists: (0, 0+2, 0, 2a+1, a+e+2) →* (A, 0, 0, 0, E')
  have hcond : 3 * (a + e + 2) ≥ (2 * a + 1) + 3 := by omega
  obtain ⟨A, E', hA, hE', hstep⟩ := phase3_exists (2 * a + 1) 0 (a + e + 2) hcond
  refine ⟨A, E', hA, hE', ?_⟩
  -- First R3 step gives ⊢, rest is ⊢*
  rw [show a + 2 = (a + 1) + 1 from by ring]
  apply step_stepStar_stepPlus
  · show fm ⟨(a + 1) + 1, 0, 0, 0, e + 1⟩ = some ⟨a + 1, 0, 1, 0, e + 2⟩
    simp [fm]
  -- Remaining R3 steps
  have h_r3' := r3_chain (a + 1) 0 1 (e + 2)
  simp only [Nat.zero_add] at h_r3'
  apply stepStar_trans h_r3'
  -- Now at (0, 0, 1+(a+1), 0, e+2+(a+1))
  have h_r4' := r4_chain (1 + (a + 1)) 0 0 (e + 2 + (a + 1))
  simp only [Nat.zero_add] at h_r4'
  apply stepStar_trans h_r4'
  -- First round
  apply stepStar_trans
  · rw [show 2 * (1 + (a + 1)) = (2 * a + 1) + 3 from by ring,
        show e + 2 + (a + 1) = (a + e + 2) + 1 from by ring]
    exact first_round (2 * a + 1) (a + e + 2)
  -- phase3
  rw [show (0 : ℕ) + 2 = 2 from by ring] at hstep
  exact hstep

-- Final theorem
theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨2, 0, 0, 0, 1⟩) (by execute fm 8)
  apply progress_nonhalt (fm := fm)
    (P := fun q ↦ ∃ a e, q = ⟨a + 2, 0, 0, 0, e + 1⟩)
  · intro c ⟨a, e, hq⟩; subst hq
    obtain ⟨A, E', hA, hE', htrans⟩ := main_trans a e
    refine ⟨⟨A, 0, 0, 0, E'⟩, ⟨A - 2, E' - 1, ?_⟩, htrans⟩
    simp only [show A - 2 + 2 = A by omega, show E' - 1 + 1 = E' by omega]
  · exact ⟨0, 0, rfl⟩

end Sz21_140_unofficial_61
