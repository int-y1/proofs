import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #556: [308/15, 3/26, 35/2, 13/11, 39/7]

Vector representation:
```
 2 -1 -1  1  1  0
-1  1  0  0  0 -1
-1  0  1  1  0  0
 0  0  0  0 -1  1
 0  1  0 -1  0  1
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_556

def Q := ℕ × ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a, b+1, c+1, d, e, f⟩ => some ⟨a+2, b, c, d+1, e+1, f⟩
  | ⟨a+1, b, c, d, e, f+1⟩ => some ⟨a, b+1, c, d, e, f⟩
  | ⟨a+1, b, c, d, e, f⟩ => some ⟨a, b, c+1, d+1, e, f⟩
  | ⟨a, b, c, d, e+1, f⟩ => some ⟨a, b, c, d, e, f+1⟩
  | ⟨a, b, c, d+1, e, f⟩ => some ⟨a, b+1, c, d, e, f+1⟩
  | _ => none

-- R3 repeated: convert a to c and d
theorem r3_chain : ∀ k, ∀ c d, ⟨k, 0, c, d, e, 0⟩ [fm]⊢* ⟨0, 0, c+k, d+k, e, 0⟩ := by
  intro k; induction' k with k h <;> intro c d
  · exists 0
  step fm
  apply stepStar_trans (h _ _)
  ring_nf; finish

-- R4 repeated: convert e to f
theorem r4_chain : ∀ k, ∀ d f, ⟨0, 0, c, d, k, f⟩ [fm]⊢* ⟨0, 0, c, d, 0, f+k⟩ := by
  intro k; induction' k with k h <;> intro d f
  · exists 0
  step fm
  apply stepStar_trans (h _ _)
  ring_nf; finish

-- R1+R2 interleaved pairs
theorem r1r2_pairs : ∀ k, ∀ A C D E F,
    ⟨A, 1, C+k, D, E, F+k⟩ [fm]⊢* ⟨A+k, 1, C, D+k, E+k, F⟩ := by
  intro k; induction' k with k h <;> intro A C D E F
  · exists 0
  rw [show C + (k + 1) = (C + k) + 1 from by ring,
      show F + (k + 1) = (F + k) + 1 from by ring]
  step fm; step fm
  apply stepStar_trans (h _ _ _ _ _)
  ring_nf; finish

-- R2 repeated: convert a to b (consuming f)
theorem r2_chain : ∀ k, ∀ a b, ⟨a+k, b, 0, d, e, k⟩ [fm]⊢* ⟨a, b+k, 0, d, e, 0⟩ := by
  intro k; induction' k with k h <;> intro a b
  · exists 0
  rw [show a + (k + 1) = (a + k) + 1 from by ring]
  step fm
  apply stepStar_trans (h _ _)
  ring_nf; finish

-- R3+R1 pairs
theorem r3r1_pairs : ∀ k, ∀ a b d e,
    ⟨a+1, b+k, 0, d, e, 0⟩ [fm]⊢* ⟨a+k+1, b, 0, d+2*k, e+k, 0⟩ := by
  intro k; induction' k with k h <;> intro a b d e
  · exists 0
  rw [show b + (k + 1) = (b + k) + 1 from by ring]
  step fm; step fm
  apply stepStar_trans (h _ _ _ _)
  ring_nf; finish

-- Full star transition from canonical to next canonical
theorem full_star (n : ℕ) :
    ⟨n+1, 0, 0, 2*n^2+n, 2*n, 0⟩ [fm]⊢*
    ⟨n+2, 0, 0, 2*n^2+5*n+3, 2*n+2, 0⟩ := by
  -- Phase A: R3 x (n+1)
  apply stepStar_trans (r3_chain (n+1) 0 (2*n^2+n) (e := 2*n))
  rw [show 0 + (n+1) = n+1 from by ring, show 2*n^2+n+(n+1) = 2*n^2+2*n+1 from by ring]
  -- Phase B: R4 x 2n
  apply stepStar_trans (r4_chain (2*n) (2*n^2+2*n+1) 0 (c := n+1))
  rw [show 0 + 2*n = 2*n from by ring]
  -- Phase C1: R5 step
  rw [show 2*n^2+2*n+1 = (2*n^2+2*n) + 1 from by ring]
  apply stepStar_trans (step_stepStar
    (show fm ⟨0, 0, n+1, (2*n^2+2*n)+1, 0, 2*n⟩ = some ⟨0, 1, n+1, 2*n^2+2*n, 0, 2*n+1⟩
      from by unfold fm; simp))
  -- Phase C2: R1+R2 x n pairs
  rw [show n + 1 = 1 + n from by ring,
      show 2*n + 1 = (n+1) + n from by ring]
  apply stepStar_trans (r1r2_pairs n 0 1 (2*n^2+2*n) 0 (n+1))
  -- State: (0+n, 1, 1, 2*n^2+2*n+n, 0+n, n+1)
  -- Phase C3: Final R1 step
  -- Need to show the state matches R1 pattern
  show ⟨0 + n, 1, 1, 2 * n ^ 2 + 2 * n + n, 0 + n, n + 1⟩ [fm]⊢*
    ⟨n + 2, 0, 0, 2 * n ^ 2 + 5 * n + 3, 2 * n + 2, 0⟩
  rw [show 0 + n = n from by ring, show 2 * n ^ 2 + 2 * n + n = 2*n^2+3*n from by ring]
  apply stepStar_trans (step_stepStar
    (show fm ⟨n, 1, 1, 2*n^2+3*n, n, n+1⟩ = some ⟨n+2, 0, 0, 2*n^2+3*n+1, n+1, n+1⟩
      from by unfold fm; simp))
  -- Phases D+E: R2 chain then R3+R1 chain
  have hDE : ⟨n+2, 0, 0, 2*n^2+3*n+1, n+1, n+1⟩ [fm]⊢*
      ⟨n+2, 0, 0, 2*n^2+5*n+3, 2*n+2, 0⟩ := by
    -- Phase D: R2 x (n+1)
    rw [show n + 2 = 1 + (n + 1) from by ring]
    apply stepStar_trans (r2_chain (n+1) 1 0 (d := 2*n^2+3*n+1) (e := n+1))
    -- Clean up: goal has (1+(n+1), 0+(n+1), ...) forms
    simp only [Nat.zero_add]
    -- Phase E: R3+R1 x (n+1)
    -- Need (0+1, 0+(n+1), 0, ...) form for r3r1_pairs
    -- Current: (1, n+1, 0, 2*n^2+3*n+1, n+1, 0) ⊢* (1+(n+1), ...)
    have hE := @r3r1_pairs (n+1) 0 0 (2*n^2+3*n+1) (n+1)
    simp only [Nat.zero_add] at hE
    apply stepStar_trans hE
    ring_nf; finish
  exact hDE

-- Main transition: ⊢⁺ version
theorem main_trans (n : ℕ) :
    ⟨n+1, 0, 0, 2*n^2+n, 2*n, 0⟩ [fm]⊢⁺
    ⟨n+2, 0, 0, 2*n^2+5*n+3, 2*n+2, 0⟩ :=
  stepStar_stepPlus (full_star n) (by simp [Q])

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨2, 0, 0, 3, 2, 0⟩) (by execute fm 6)
  apply progress_nonhalt (fm := fm)
    (P := fun q ↦ ∃ n, q = ⟨n+1, 0, 0, 2*n^2+n, 2*n, 0⟩ ∧ n ≥ 1)
  · intro c ⟨n, hq, hn⟩; subst hq
    exact ⟨⟨n+2, 0, 0, 2*n^2+5*n+3, 2*n+2, 0⟩,
      ⟨n+1, by ring_nf, by omega⟩, main_trans n⟩
  · exact ⟨1, by norm_num, by omega⟩

end Sz22_2003_unofficial_556
