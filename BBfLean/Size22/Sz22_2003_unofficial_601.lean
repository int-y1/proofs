import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #601: [35/6, 121/2, 4/55, 3/7, 245/11]

Vector representation:
```
-1 -1  1  1  0
-1  0  0  0  2
 2  0 -1  0 -1
 0  1  0 -1  0
 0  0  1  2 -1
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_601

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a+1, b+1, c, d, e⟩ => some ⟨a, b, c+1, d+1, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b, c, d, e+2⟩
  | ⟨a, b, c+1, d, e+1⟩ => some ⟨a+2, b, c, d, e⟩
  | ⟨a, b, c, d+1, e⟩ => some ⟨a, b+1, c, d, e⟩
  | ⟨a, b, c, d, e+1⟩ => some ⟨a, b, c+1, d+2, e⟩
  | _ => none

-- R4 repeated: convert d to b
theorem d_to_b : ⟨0, b, 0, d + k, e⟩ [fm]⊢* ⟨0, b + k, 0, d, e⟩ := by
  have many_step : ∀ k b, ⟨0, b, 0, d + k, e⟩ [fm]⊢* ⟨0, b + k, 0, d, e⟩ := by
    intro k; induction' k with k h <;> intro b
    · exists 0
    rw [← Nat.add_assoc]
    step fm
    apply stepStar_trans (h _)
    ring_nf; finish
  exact many_step k b

-- R3,R2,R2 chain: each round converts one c to 3 additional e
theorem drain_c : ⟨0, 0, c + k, d, e + k⟩ [fm]⊢* ⟨0, 0, c, d, e + 4 * k⟩ := by
  have many_step : ∀ k c e, ⟨0, 0, c + k, d, e + k⟩ [fm]⊢* ⟨0, 0, c, d, e + 4 * k⟩ := by
    intro k; induction' k with k h <;> intro c e
    · exists 0
    rw [show c + (k + 1) = (c + k) + 1 from by ring,
        show e + (k + 1) = e + k + 1 from by ring]
    step fm; step fm; step fm
    rw [show e + k + 2 + 2 = (e + 4) + k from by ring]
    apply stepStar_trans (h _ _)
    ring_nf; finish
  exact many_step k c e

-- Interleaved R1,R1,R3 chain: processes b in pairs
theorem interleave : ∀ j, ∀ c d e,
    ⟨2, 2 * (j + 1), c, d, e + j⟩ [fm]⊢* ⟨0, 0, c + j + 2, d + 2 * (j + 1), e⟩ := by
  intro j; induction' j with j h <;> intro c d e
  · step fm; step fm; finish
  · rw [show 2 * (j + 1 + 1) = 2 * (j + 1) + 2 from by ring,
        show e + (j + 1) = e + j + 1 from by ring]
    step fm; step fm; step fm
    apply stepStar_trans (h _ _ _)
    ring_nf; finish

-- Main transition: C(n) →⁺ C(n+1) where C(n) = (0, 2*(n+1), 0, 0, n*n+3*n+4)
theorem main_trans :
    ⟨0, 2 * n + 2, 0, 0, n * n + 3 * n + 4⟩ [fm]⊢⁺
    ⟨0, 2 * n + 4, 0, 0, n * n + 5 * n + 8⟩ := by
  -- Phase 1: R5
  rw [show n * n + 3 * n + 4 = n * n + 3 * n + 3 + 1 from by ring]
  step fm
  -- State: (0, 2*n+2, 1, 2, n*n+3*n+3)
  -- Phase 2: R3
  rw [show n * n + 3 * n + 3 = n * n + 3 * n + 2 + 1 from by ring]
  step fm
  -- State: (2, 2*n+2, 0, 2, n*n+3*n+2)
  -- Phase 3: interleave
  rw [show 2 * n + 2 = 2 * (n + 1) from by ring,
      show n * n + 3 * n + 2 = (n * n + 2 * n + 2) + n from by ring]
  apply stepStar_trans (interleave n 0 2 (n * n + 2 * n + 2))
  -- State: (0, 0, n+2, 2*n+4, n*n+2*n+2)
  -- Phase 4: drain_c
  rw [show 0 + n + 2 = 0 + (n + 2) from by ring,
      show 2 + 2 * (n + 1) = 2 * n + 4 from by ring,
      show n * n + 2 * n + 2 = n * (n + 1) + (n + 2) from by ring]
  apply stepStar_trans (drain_c (k := n + 2) (c := 0) (d := 2 * n + 4) (e := n * (n + 1)))
  -- State: (0, 0, 0, 2*n+4, n*(n+1)+4*(n+2))
  -- Phase 5: d_to_b
  rw [show 2 * n + 4 = 0 + (2 * n + 4) from by ring,
      show n * (n + 1) + 4 * (n + 2) = n * n + 5 * n + 8 from by ring]
  exact d_to_b

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨0, 2, 0, 0, 4⟩) (by execute fm 7)
  apply progress_nonhalt_simple (fm := fm) (A := ℕ)
    (fun n ↦ ⟨0, 2 * n + 2, 0, 0, n * n + 3 * n + 4⟩) 0
  intro n; exists n + 1
  have h := @main_trans n
  convert h using 2; ring_nf

end Sz22_2003_unofficial_601
