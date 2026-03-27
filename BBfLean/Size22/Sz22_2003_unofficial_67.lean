import BBfLean.FM
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

/-!
# sz22_2003_unofficial #67: [1/18, 2/35, 1/5, 715/2, 21/11, 2/13]

Vector representation:
```
-1 -2  0  0  0  0
 1  0 -1 -1  0  0
 0  0 -1  0  0  0
-1  0  1  0  1  1
 0  1  0  1 -1  0
 1  0  0  0  0 -1
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_67

def Q := ℕ × ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a+1, b+2, c, d, e, f⟩ => some ⟨a, b, c, d, e, f⟩
  | ⟨a, b, c+1, d+1, e, f⟩ => some ⟨a+1, b, c, d, e, f⟩
  | ⟨a, b, c+1, d, e, f⟩ => some ⟨a, b, c, d, e, f⟩
  | ⟨a+1, b, c, d, e, f⟩ => some ⟨a, b, c+1, d, e+1, f+1⟩
  | ⟨a, b, c, d, e+1, f⟩ => some ⟨a, b+1, c, d+1, e, f⟩
  | ⟨a, b, c, d, e, f+1⟩ => some ⟨a+1, b, c, d, e, f⟩
  | _ => none

theorem r5_chain : ∀ k b d e f,
    ⟨0, b, 0, d, e+k, f⟩ [fm]⊢* ⟨(0 : ℕ), b+k, 0, d+k, e, f⟩ := by
  intro k; induction' k with k ih <;> intro b d e f
  · exists 0
  rw [show e + (k + 1) = (e + k) + 1 from by ring]
  step fm
  apply stepStar_trans (ih (b + 1) (d + 1) e f); ring_nf; finish

theorem r6r1_even_drain : ∀ k d f,
    ⟨0, 2*k, 0, d, 0, f+k⟩ [fm]⊢* ⟨(0 : ℕ), 0, 0, d, 0, f⟩ := by
  intro k; induction' k with k ih <;> intro d f
  · exists 0
  rw [show 2 * (k + 1) = (2 * k) + 1 + 1 from by ring,
      show f + (k + 1) = (f + k) + 1 from by ring]
  step fm; step fm; exact ih d f

theorem r6r1_odd_drain : ∀ k d f,
    ⟨0, 1+2*k, 0, d, 0, f+k⟩ [fm]⊢* ⟨(0 : ℕ), 1, 0, d, 0, f⟩ := by
  intro k; induction' k with k ih <;> intro d f
  · exists 0
  rw [show 1 + 2 * (k + 1) = (1 + 2 * k) + 1 + 1 from by ring,
      show f + (k + 1) = (f + k) + 1 from by ring]
  step fm; step fm; exact ih d f

theorem r2r4_chain_b0 : ∀ k d e f,
    ⟨0, 0, 1, d+k, e, f⟩ [fm]⊢* ⟨(0 : ℕ), 0, 1, d, e+k, f+k⟩ := by
  intro k; induction' k with k ih <;> intro d e f
  · exists 0
  rw [show d + (k + 1) = (d + k) + 1 from by ring]
  step fm; step fm
  apply stepStar_trans (ih d (e + 1) (f + 1)); ring_nf; finish

theorem r2r4_chain_b1 : ∀ k d e f,
    ⟨0, 1, 1, d+k, e, f⟩ [fm]⊢* ⟨(0 : ℕ), 1, 1, d, e+k, f+k⟩ := by
  intro k; induction' k with k ih <;> intro d e f
  · exists 0
  rw [show d + (k + 1) = (d + k) + 1 from by ring]
  step fm; step fm
  apply stepStar_trans (ih d (e + 1) (f + 1)); ring_nf; finish

-- Combined: odd drain + R6 + R4 + R2/R4(b=1) chain + R3
-- (0, 1+2*j, 0, D, 0, G+j+1) ⊢* (0, 1, 0, 0, D+1, G+D+1)
theorem odd_drain_cycle_b1 (j D G : ℕ) :
    ⟨0, 1+2*j, 0, D, 0, G+j+1⟩ [fm]⊢* ⟨(0 : ℕ), 1, 0, 0, D+1, G+D+1⟩ := by
  apply stepStar_trans (c₂ := ⟨0, 1, 0, D, 0, G+1⟩)
  · have h := r6r1_odd_drain j D (G+1)
    convert h using 2; all_goals ring_nf
  apply stepStar_trans (c₂ := ⟨1, 1, 0, D, 0, G⟩)
  · have : fm ⟨0, 1, 0, D, 0, G+1⟩ = some ⟨0+1, 1, 0, D, 0, G⟩ := by simp [fm]
    exact step_stepStar this
  apply stepStar_trans (c₂ := ⟨0, 1, 1, D, 1, G+1⟩)
  · have : fm ⟨0+1, 1, 0, D, 0, G⟩ = some ⟨0, 1, 0+1, D, 0+1, G+1⟩ := by simp [fm]
    exact step_stepStar this
  apply stepStar_trans (c₂ := ⟨0, 1, 1, 0, D+1, G+D+1⟩)
  · have h := r2r4_chain_b1 D 0 1 (G+1)
    simp only [Nat.zero_add] at h
    convert h using 2; all_goals ring_nf
  step fm; finish

-- Combined: even drain + R6 + R4 + R2/R4(b=0) chain + R3
-- (0, 2*j, 0, D, 0, G+j+1) ⊢* (0, 0, 0, 0, D+1, G+D+1)
theorem even_drain_cycle_b0 (j D G : ℕ) :
    ⟨0, 2*j, 0, D, 0, G+j+1⟩ [fm]⊢* ⟨(0 : ℕ), 0, 0, 0, D+1, G+D+1⟩ := by
  apply stepStar_trans (c₂ := ⟨0, 0, 0, D, 0, G+1⟩)
  · have h := r6r1_even_drain j D (G+1)
    convert h using 2; all_goals ring_nf
  apply stepStar_trans (c₂ := ⟨1, 0, 0, D, 0, G⟩)
  · have : fm ⟨0, 0, 0, D, 0, G+1⟩ = some ⟨0+1, 0, 0, D, 0, G⟩ := by simp [fm]
    exact step_stepStar this
  apply stepStar_trans (c₂ := ⟨0, 0, 1, D, 1, G+1⟩)
  · have : fm ⟨0+1, 0, 0, D, 0, G⟩ = some ⟨0, 0, 0+1, D, 0+1, G+1⟩ := by simp [fm]
    exact step_stepStar this
  apply stepStar_trans (c₂ := ⟨0, 0, 1, 0, D+1, G+D+1⟩)
  · have h := r2r4_chain_b0 D 0 1 (G+1)
    simp only [Nat.zero_add] at h
    convert h using 2; all_goals ring_nf
  step fm; finish

-- B(k) -> A(k+1)
theorem trans_B_to_A (k : ℕ) :
    ⟨0, 0, 0, 0, 4*k+4, 4*k^2+7*k+4⟩ [fm]⊢⁺ ⟨(0 : ℕ), 0, 0, 0, 4*k+5, 4*k^2+9*k+6⟩ := by
  rw [show 4 * k + 4 = (4 * k + 3) + 1 from by ring]
  apply step_stepStar_stepPlus (c₂ := ⟨0, 1, 0, 1, 4*k+3, 4*k^2+7*k+4⟩)
  · show fm ⟨0, 0, 0, 0, (4*k+3)+1, 4*k^2+7*k+4⟩ = some ⟨0, 0+1, 0, 0+1, 4*k+3, 4*k^2+7*k+4⟩
    simp [fm]
  -- R5 chain (4k+3 steps)
  apply stepStar_trans (c₂ := ⟨0, 4*k+4, 0, 4*k+4, 0, 4*k^2+7*k+4⟩)
  · have h := r5_chain (4*k+3) 1 1 0 (4*k^2+7*k+4)
    simp only [Nat.zero_add] at h
    convert h using 2; all_goals ring_nf
  -- even_drain_cycle_b0 (j=2k+2, D=4k+4, G=4k^2+5k+1)
  have h := even_drain_cycle_b0 (2*k+2) (4*k+4) (4*k^2+5*k+1)
  convert h using 2; all_goals ring_nf

-- A(k) -> B(k)
theorem trans_A_to_B (k : ℕ) :
    ⟨0, 0, 0, 0, 4*k+1, 4*k^2+k+1⟩ [fm]⊢⁺ ⟨(0 : ℕ), 0, 0, 0, 4*k+4, 4*k^2+7*k+4⟩ := by
  rw [show 4 * k + 1 = (4 * k) + 1 from by ring]
  apply step_stepStar_stepPlus (c₂ := ⟨0, 1, 0, 1, 4*k, 4*k^2+k+1⟩)
  · show fm ⟨0, 0, 0, 0, (4*k)+1, 4*k^2+k+1⟩ = some ⟨0, 0+1, 0, 0+1, 4*k, 4*k^2+k+1⟩
    simp [fm]
  -- R5 chain (4k steps)
  apply stepStar_trans (c₂ := ⟨0, 4*k+1, 0, 4*k+1, 0, 4*k^2+k+1⟩)
  · have h := r5_chain (4*k) 1 1 0 (4*k^2+k+1)
    simp only [Nat.zero_add] at h
    convert h using 2; all_goals ring_nf
  -- Cycle 1: odd_drain_cycle_b1 (j=2k, D=4k+1, G=4k^2-k)
  apply stepStar_trans (c₂ := ⟨0, 1, 0, 0, 4*k+2, 4*k^2+3*k+2⟩)
  · have hle : k ≤ 4 * k ^ 2 := by nlinarith [sq_nonneg k]
    set G := 4 * k ^ 2 - k
    have hG1 : G + 2 * k + 1 = 4 * k ^ 2 + k + 1 := by omega
    have hG2 : G + (4 * k + 1) + 1 = 4 * k ^ 2 + 3 * k + 2 := by omega
    have h := odd_drain_cycle_b1 (2*k) (4*k+1) G
    rw [show 1 + 2 * (2 * k) = 4 * k + 1 from by ring,
        show (4 * k + 1) + 1 = 4 * k + 2 from by ring,
        hG1, hG2] at h
    exact h
  -- Cycle 2: R5 chain + odd_drain_cycle_b1 (j=2k+1, D=4k+2, G=4k^2+k)
  apply stepStar_trans (c₂ := ⟨0, 1, 0, 0, 4*k+3, 4*k^2+5*k+3⟩)
  · apply stepStar_trans (c₂ := ⟨0, 4*k+3, 0, 4*k+2, 0, 4*k^2+3*k+2⟩)
    · have h := r5_chain (4*k+2) 1 0 0 (4*k^2+3*k+2)
      simp only [Nat.zero_add] at h
      convert h using 2; all_goals ring_nf
    have h := odd_drain_cycle_b1 (2*k+1) (4*k+2) (4*k^2+k)
    convert h using 2; all_goals ring_nf
  -- Cycle 3: R5 chain + even_drain_cycle_b0 (j=2k+2, D=4k+3, G=4k^2+3k)
  apply stepStar_trans (c₂ := ⟨0, 4*k+4, 0, 4*k+3, 0, 4*k^2+5*k+3⟩)
  · have h := r5_chain (4*k+3) 1 0 0 (4*k^2+5*k+3)
    simp only [Nat.zero_add] at h
    convert h using 2; all_goals ring_nf
  have h := even_drain_cycle_b0 (2*k+2) (4*k+3) (4*k^2+3*k)
  convert h using 2; all_goals ring_nf

theorem main_trans (k : ℕ) :
    ⟨0, 0, 0, 0, 4*k+1, 4*k^2+k+1⟩ [fm]⊢⁺ ⟨(0 : ℕ), 0, 0, 0, 4*k+5, 4*k^2+9*k+6⟩ :=
  stepPlus_stepStar_stepPlus (trans_A_to_B k) (stepPlus_stepStar (trans_B_to_A k))

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨0, 0, 0, 0, 1, 1⟩) (by execute fm 2)
  apply progress_nonhalt (fm := fm)
    (P := fun q ↦ ∃ k, q = ⟨0, 0, 0, 0, 4*k+1, 4*k^2+k+1⟩)
  · intro c ⟨k, hk⟩
    refine ⟨⟨0, 0, 0, 0, 4*k+5, 4*k^2+9*k+6⟩, ⟨k+1, ?_⟩, hk ▸ main_trans k⟩
    ring_nf
  · exact ⟨0, by simp⟩

end Sz22_2003_unofficial_67
