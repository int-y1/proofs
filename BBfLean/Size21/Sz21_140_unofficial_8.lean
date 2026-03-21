import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz21_140_unofficial #8: [1/45, 196/15, 3/7, 25/2, 7/5]

Vector representation:
```
 0 -2 -1  0
 2 -1 -1  2
 0  1  0 -1
-1  0  2  0
 0  0 -1  1
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz21_140_unofficial_8

def Q := ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a, b+2, c+1, d⟩ => some ⟨a, b, c, d⟩
  | ⟨a, b+1, c+1, d⟩ => some ⟨a+2, b, c, d+2⟩
  | ⟨a, b, c, d+1⟩ => some ⟨a, b+1, c, d⟩
  | ⟨a+1, b, c, d⟩ => some ⟨a, b, c+2, d⟩
  | ⟨a, b, c+1, d⟩ => some ⟨a, b, c, d+1⟩
  | _ => none

-- R4 repeated: a → c
theorem a_to_c : ∀ k, ∀ a c, ⟨a+k, 0, c, 0⟩ [fm]⊢* ⟨a, 0, c+2*k, 0⟩ := by
  intro k; induction' k with k ih <;> intro a c
  · exists 0
  rw [show a + (k + 1) = (a + k) + 1 from by ring]
  step fm
  apply stepStar_trans (ih _ _)
  ring_nf; finish

-- R3 repeated: d → b
theorem d_to_b : ∀ k, ∀ a b d, ⟨a, b, 0, d+k⟩ [fm]⊢* ⟨a, b+k, 0, d⟩ := by
  intro k; induction' k with k ih <;> intro a b d
  · exists 0
  rw [show d + (k + 1) = (d + k) + 1 from by ring]
  step fm
  apply stepStar_trans (ih _ _ _)
  ring_nf; finish

-- R2/R3 interleaved chain
theorem r2r3_chain : ∀ c, ∀ a d, ⟨a, 1, c+1, d⟩ [fm]⊢* ⟨a+2*(c+1), 0, 0, d+c+2⟩ := by
  intro c; induction' c with c ih <;> intro a d
  · step fm; finish
  · rw [show c + 1 + 1 = (c + 1) + 1 from by ring]
    step fm; step fm
    apply stepStar_trans (ih (a+2) (d+1))
    ring_nf; finish

-- Interleaved phase
theorem interleaved_phase (A : ℕ) : ⟨0, 1, 2*(A+1), 0⟩ [fm]⊢* ⟨4*(A+1), 0, 0, 2*(A+1)+1⟩ := by
  have h := r2r3_chain (2*A+1) 0 0
  simp only [Nat.zero_add] at h
  convert h using 2; ring_nf

-- b drain: 3-step round
theorem b_drain_round : ∀ k, ∀ A B, ⟨A+k, B+4*k, 0, 0⟩ [fm]⊢* ⟨A, B, 0, 0⟩ := by
  intro k; induction' k with k ih <;> intro A B
  · exists 0
  rw [show A + (k + 1) = (A + k) + 1 from by ring,
      show B + 4 * (k + 1) = (B + 4 * k) + 4 from by ring]
  step fm
  rw [show B + 4 * k + 4 = (B + 4 * k + 2) + 2 from by ring]
  step fm
  rw [show B + 4 * k + 2 = (B + 4 * k) + 2 from by ring]
  step fm
  apply stepStar_trans (ih _ _)
  ring_nf; finish

-- b drain terminal: B=3
theorem b_drain_3 (A : ℕ) : ⟨A+1, 3, 0, 0⟩ [fm]⊢* ⟨A+1, 0, 1, 0⟩ := by
  step fm
  step fm
  rw [show A + 1 = A + 1 from rfl]
  step fm
  step fm
  step fm
  step fm
  step fm
  finish

-- b drain terminal: B=1
theorem b_drain_1 (A : ℕ) : ⟨A+1, 1, 0, 0⟩ [fm]⊢* ⟨A+4, 0, 1, 0⟩ := by
  step fm
  step fm
  step fm
  rw [show A + 2 + 2 = A + 4 from by ring]
  step fm
  apply stepStar_trans (d_to_b 3 (A+4) 0 0)
  rw [show A + 4 = (A + 3) + 1 from by ring]
  exact b_drain_3 (A + 3)

-- Main transition: even A
theorem main_trans_even (K : ℕ) : ⟨2*(K+2), 0, 1, 0⟩ [fm]⊢⁺ ⟨7*(K+2)+3, 0, 1, 0⟩ := by
  -- Phase 1: a → c
  apply stepStar_stepPlus_stepPlus (c₂ := ⟨0, 0, 4*(K+2)+1, 0⟩)
  · have h := a_to_c (2*(K+2)) 0 1
    simp only [Nat.zero_add] at h
    convert h using 2; ring_nf
  -- Phase 2: R5 then R3
  apply step_stepStar_stepPlus (c₂ := ⟨0, 0, 4*(K+2), 1⟩)
  · show fm ⟨0, 0, (4*(K+2)) + 1, 0⟩ = some ⟨0, 0, 4*(K+2), 1⟩; simp [fm]
  apply stepStar_trans (c₂ := ⟨0, 1, 4*(K+2), 0⟩)
  · step fm; finish
  -- Phase 3: interleaved
  apply stepStar_trans (c₂ := ⟨8*(K+2), 0, 0, 4*(K+2)+1⟩)
  · have h := interleaved_phase (2*K+3)
    convert h using 2; ring_nf
  -- Phase 4: d → b
  apply stepStar_trans (c₂ := ⟨8*(K+2), 4*(K+2)+1, 0, 0⟩)
  · have h := d_to_b (4*(K+2)+1) (8*(K+2)) 0 0
    simp only [Nat.zero_add] at h
    convert h using 2
  -- Phase 5: b drain rounds
  apply stepStar_trans (c₂ := ⟨7*(K+2), 1, 0, 0⟩)
  · have h := b_drain_round (K+2) (7*(K+2)) 1
    convert h using 2; ring_nf
  -- Phase 6: b drain terminal
  rw [show 7*(K+2) = (7*(K+2)-1) + 1 from by omega]
  apply stepStar_trans (b_drain_1 (7*(K+2)-1))
  have : 7*(K+2)-1+4 = 7*(K+2)+3 := by omega
  rw [this]; finish

-- Main transition: odd A
theorem main_trans_odd (K : ℕ) : ⟨2*K+1, 0, 1, 0⟩ [fm]⊢⁺ ⟨7*K+4, 0, 1, 0⟩ := by
  -- Phase 1: a → c
  apply stepStar_stepPlus_stepPlus (c₂ := ⟨0, 0, 4*K+3, 0⟩)
  · have h := a_to_c (2*K+1) 0 1
    simp only [Nat.zero_add] at h
    convert h using 2; ring_nf
  -- Phase 2: R5 then R3
  apply step_stepStar_stepPlus (c₂ := ⟨0, 0, 4*K+2, 1⟩)
  · show fm ⟨0, 0, (4*K+2) + 1, 0⟩ = some ⟨0, 0, 4*K+2, 1⟩; simp [fm]
  apply stepStar_trans (c₂ := ⟨0, 1, 4*K+2, 0⟩)
  · step fm; finish
  -- Phase 3: interleaved
  apply stepStar_trans (c₂ := ⟨8*K+4, 0, 0, 4*K+3⟩)
  · have h := interleaved_phase (2*K)
    convert h using 2; ring_nf
  -- Phase 4: d → b
  apply stepStar_trans (c₂ := ⟨8*K+4, 4*K+3, 0, 0⟩)
  · have h := d_to_b (4*K+3) (8*K+4) 0 0
    simp only [Nat.zero_add] at h
    convert h using 2
  -- Phase 5: b drain rounds
  apply stepStar_trans (c₂ := ⟨7*K+4, 3, 0, 0⟩)
  · have h := b_drain_round K (7*K+4) 3
    convert h using 2; ring_nf
  -- Phase 6: b drain terminal
  rw [show 7*K+4 = (7*K+3)+1 from by ring]
  exact b_drain_3 (7*K+3)

-- Combined main transition
theorem main_trans (A : ℕ) (hA : A ≥ 4) : ∃ A', A' ≥ 4 ∧ (⟨A, 0, 1, 0⟩ [fm]⊢⁺ ⟨A', 0, 1, 0⟩) := by
  rcases Nat.even_or_odd A with ⟨K, hK⟩ | ⟨K, hK⟩
  · have hK2 : K ≥ 2 := by omega
    obtain ⟨K', rfl⟩ := Nat.exists_eq_add_of_le hK2
    subst hK
    refine ⟨7*(K'+2)+3, by omega, ?_⟩
    have h := main_trans_even K'
    convert h using 2; ring_nf
  · subst hK
    exact ⟨7*K+4, by omega, main_trans_odd K⟩

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨4, 0, 1, 0⟩) (by execute fm 24)
  apply progress_nonhalt (fm := fm)
    (P := fun q ↦ ∃ A, A ≥ 4 ∧ q = ⟨A, 0, 1, 0⟩)
  · intro c ⟨A, hA, hc⟩
    subst hc
    obtain ⟨A', hA', hstep⟩ := main_trans A hA
    exact ⟨⟨A', 0, 1, 0⟩, ⟨A', hA', rfl⟩, hstep⟩
  · exact ⟨4, by omega, rfl⟩
