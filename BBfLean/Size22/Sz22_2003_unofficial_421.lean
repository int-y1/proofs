import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #421: [27/10, 55/21, 2/3, 7/11, 165/2]

Vector representation:
```
-1  3 -1  0  0
 0 -1  1 -1  1
 1 -1  0  0  0
 0  0  0  1 -1
-1  1  1  0  1
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6 (1M context)
-/

namespace Sz22_2003_unofficial_421

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a+1, b, c+1, d, e⟩ => some ⟨a, b+3, c, d, e⟩
  | ⟨a, b+1, c, d+1, e⟩ => some ⟨a, b, c+1, d, e+1⟩
  | ⟨a, b+1, c, d, e⟩ => some ⟨a+1, b, c, d, e⟩
  | ⟨a, b, c, d, e+1⟩ => some ⟨a, b, c, d+1, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b+1, c+1, d, e+1⟩
  | _ => none

-- Rule 4 repeated: convert e to d
theorem e_to_d : ∀ k a d, ⟨a, 0, 0, d, k⟩ [fm]⊢* ⟨a, 0, 0, d + k, 0⟩ := by
  intro k; induction' k with k ih <;> intro a d
  · exists 0
  · step fm
    apply stepStar_trans (ih a (d + 1))
    ring_nf; finish

-- Inner loop: (R2, R1) repeated D times
theorem inner_loop : ∀ D A B E,
    ⟨A + D, B + 1, 0, D, E⟩ [fm]⊢* ⟨A, B + 1 + 2 * D, 0, 0, E + D⟩ := by
  intro D; induction' D with D ih <;> intro A B E
  · exists 0
  · rw [show A + (D + 1) = (A + D) + 1 from by ring]
    step fm; step fm
    apply stepStar_trans (ih A (B + 2) (E + 1))
    ring_nf; finish

-- Rule 3 repeated: convert b to a
theorem b_to_a : ∀ B a e, ⟨a, B, 0, 0, e⟩ [fm]⊢* ⟨a + B, 0, 0, 0, e⟩ := by
  intro B; induction' B with B ih <;> intro a e
  · exists 0
  · step fm
    apply stepStar_trans (ih (a + 1) e)
    ring_nf; finish

-- Full transition from (N, 0, 0, k+1, 0) onward
theorem from_d (M k : ℕ) :
    ⟨M + k + 3, 0, 0, k + 1, 0⟩ [fm]⊢⁺ ⟨M + 2 * k + 6, 0, 0, 0, k + 2⟩ := by
  -- Rule 5: (M+k+3, 0, 0, k+1, 0) → (M+k+2, 1, 1, k+1, 1)
  -- Rule 1: (M+k+2, 1, 1, k+1, 1) → (M+k+1, 4, 0, k+1, 1)
  step fm; step fm
  -- inner_loop (k+1): (M+k+1, 4, 0, k+1, 1) →* (M, 2k+6, 0, 0, k+2)
  apply stepStar_trans
  · show ⟨M + (k + 1), 3 + 1, 0, k + 1, 1⟩ [fm]⊢* ⟨M, 3 + 1 + 2 * (k + 1), 0, 0, 1 + (k + 1)⟩
    exact inner_loop (k + 1) M 3 1
  -- b_to_a: (M, 2k+6, 0, 0, k+2) →* (M+2k+6, 0, 0, 0, k+2)
  show ⟨M, 3 + 1 + 2 * (k + 1), 0, 0, 1 + (k + 1)⟩ [fm]⊢* ⟨M + 2 * k + 6, 0, 0, 0, k + 2⟩
  have h := b_to_a (3 + 1 + 2 * (k + 1)) M (1 + (k + 1))
  convert h using 2; all_goals ring_nf

-- Main step: (N, 0, 0, 0, k+1) →⁺ (N+k+3, 0, 0, 0, k+2) when N ≥ k+3
theorem main_step (N k : ℕ) (hN : N ≥ k + 3) :
    ⟨N, 0, 0, 0, k + 1⟩ [fm]⊢⁺ ⟨N + k + 3, 0, 0, 0, k + 2⟩ := by
  obtain ⟨M, rfl⟩ : ∃ M, N = M + k + 3 := ⟨N - k - 3, by omega⟩
  -- Phase 1: e_to_d
  apply stepStar_stepPlus_stepPlus
  · exact e_to_d (k + 1) (M + k + 3) 0
  -- Phases 2-5
  have h := from_d M k
  show ⟨M + k + 3, 0, 0, 0 + (k + 1), 0⟩ [fm]⊢⁺ ⟨M + k + 3 + k + 3, 0, 0, 0, k + 2⟩
  convert h using 2; all_goals ring_nf

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨3, 0, 0, 0, 1⟩) (by execute fm 6)
  apply progress_nonhalt (fm := fm)
    (P := fun q ↦ ∃ N k, q = ⟨N, 0, 0, 0, k + 1⟩ ∧ N ≥ k + 3)
  · intro c ⟨N, k, hq, hN⟩; subst hq
    exact ⟨⟨N + k + 3, 0, 0, 0, k + 2⟩, ⟨N + k + 3, k + 1, rfl, by omega⟩, main_step N k hN⟩
  · exact ⟨3, 0, rfl, by omega⟩

end Sz22_2003_unofficial_421
