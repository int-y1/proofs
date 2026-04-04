import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #1820: [9/10, 55/21, 4/3, 7/11, 363/2]

Vector representation:
```
-1  2 -1  0  0
 0 -1  1 -1  1
 2 -1  0  0  0
 0  0  0  1 -1
-1  1  0  0  2
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_1820

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a+1, b, c+1, d, e⟩ => some ⟨a, b+2, c, d, e⟩
  | ⟨a, b+1, c, d+1, e⟩ => some ⟨a, b, c+1, d, e+1⟩
  | ⟨a, b+1, c, d, e⟩ => some ⟨a+2, b, c, d, e⟩
  | ⟨a, b, c, d, e+1⟩ => some ⟨a, b, c, d+1, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b+1, c, d, e+2⟩
  | _ => none

-- R4 repeated: move e to d.
theorem e_to_d : ∀ k, ⟨a, 0, 0, d, e + k⟩ [fm]⊢* ⟨a, 0, 0, d + k, e⟩ := by
  intro k; induction' k with k ih generalizing d e
  · exists 0
  · rw [show e + (k + 1) = (e + k) + 1 from by ring]
    step fm
    apply stepStar_trans (ih (d := d + 1) (e := e))
    ring_nf; finish

-- R3 repeated: move b to a (multiplied by 2).
theorem r3_chain : ∀ k, ⟨a, k, 0, 0, e⟩ [fm]⊢* ⟨a + 2 * k, 0, 0, 0, e⟩ := by
  intro k; induction' k with k ih generalizing a
  · exists 0
  · step fm
    apply stepStar_trans (ih (a := a + 2))
    ring_nf; finish

-- R2+R1 interleaved chain.
-- From (A+K, B+1, 0, D+K, E) after K rounds of (R2, R1):
-- result is (A, B+K+1, 0, D, E+K).
theorem r2r1_chain : ∀ K, ∀ A B D E, ⟨A + K, B + 1, 0, D + K, E⟩ [fm]⊢* ⟨A, B + K + 1, 0, D, E + K⟩ := by
  intro K; induction' K with K ih <;> intro A B D E
  · exists 0
  · rw [show A + (K + 1) = (A + K) + 1 from by ring,
        show D + (K + 1) = (D + K) + 1 from by ring]
    step fm
    step fm
    rw [show A + K = A + K from rfl]
    apply stepStar_trans (ih A (B + 1) D (E + 1))
    ring_nf; finish

-- Main transition: from (A+D+3, 0, 0, D+2, 0) to (A+2*D+6, 0, 0, D+4, 0).
-- Phases: R5, (R2+R1) x (D+1), R2, R1, R3 chain, R4 chain.
theorem main_trans : ⟨A + D + 3, 0, 0, D + 2, 0⟩ [fm]⊢⁺ ⟨A + 2 * D + 6, 0, 0, D + 4, 0⟩ := by
  -- Phase 1: R5
  rw [show A + D + 3 = (A + D + 2) + 1 from by ring]
  step fm
  -- Now: (A+D+2, 1, 0, D+2, 2)
  -- Phase 2: (R2, R1) x (D+1) rounds
  rw [show A + D + 2 = (A + 1) + (D + 1) from by ring,
      show D + 2 = 1 + (D + 1) from by ring,
      show (2 : ℕ) = 0 + 2 from by ring]
  apply stepStar_trans (r2r1_chain (D + 1) (A + 1) 0 1 (0 + 2))
  -- Now: (A+1, D+2, 0, 1, D+3)
  rw [show 0 + (D + 1) + 1 = D + 2 from by ring,
      show 0 + 2 + (D + 1) = D + 3 from by ring]
  -- Phase 3: R2
  step fm
  -- Now: (A+1, D+1, 1, 0, D+4)
  -- Phase 4: R1
  rw [show A + 1 = A + 1 from rfl]
  step fm
  -- Now: (A, D+3, 0, 0, D+4)
  -- Phase 5: R3 chain
  apply stepStar_trans (r3_chain (D + 3) (a := A) (e := D + 4))
  -- Now: (A+2*(D+3), 0, 0, 0, D+4)
  -- Phase 6: R4 chain
  rw [show A + 2 * (D + 3) = A + 2 * D + 6 + 0 from by ring,
      show (D : ℕ) + 4 = 0 + (D + 4) from by ring]
  apply stepStar_trans (e_to_d (D + 4) (a := A + 2 * D + 6) (d := 0) (e := 0))
  ring_nf; finish

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨5, 0, 0, 4, 0⟩) (by execute fm 16)
  apply progress_nonhalt_simple (fm := fm) (A := ℕ)
    (fun n ↦ ⟨n * n + 4 * n + 5, 0, 0, 2 * n + 4, 0⟩) 0
  intro n
  refine ⟨n + 1, ?_⟩
  show ⟨n * n + 4 * n + 5, 0, 0, 2 * n + 4, 0⟩ [fm]⊢⁺ ⟨(n + 1) * (n + 1) + 4 * (n + 1) + 5, 0, 0, 2 * (n + 1) + 4, 0⟩
  rw [show n * n + 4 * n + 5 = (n * n + 2 * n) + (2 * n + 2) + 3 from by ring,
      show 2 * n + 4 = (2 * n + 2) + 2 from by ring,
      show (n + 1) * (n + 1) + 4 * (n + 1) + 5 = (n * n + 2 * n) + 2 * (2 * n + 2) + 6 from by ring,
      show 2 * (n + 1) + 4 = (2 * n + 2) + 4 from by ring]
  exact main_trans

end Sz22_2003_unofficial_1820
