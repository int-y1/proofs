import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #1387: [63/10, 77/2, 8/33, 5/7, 3/5]

Vector representation:
```
-1  2 -1  1  0
-1  0  0  1  1
 3 -1  0  0 -1
 0  0  1 -1  0
 0  1 -1  0  0
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_1387

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a+1, b, c+1, d, e⟩ => some ⟨a, b+2, c, d+1, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b, c, d+1, e+1⟩
  | ⟨a, b+1, c, d, e+1⟩ => some ⟨a+3, b, c, d, e⟩
  | ⟨a, b, c, d+1, e⟩ => some ⟨a, b, c+1, d, e⟩
  | ⟨a, b, c+1, d, e⟩ => some ⟨a, b+1, c, d, e⟩
  | _ => none

-- R4 chain: transfer d to c
theorem d_to_c : ∀ k c d, ⟨(0 : ℕ), 0, c, d + k, e⟩ [fm]⊢* ⟨0, 0, c + k, d, e⟩ := by
  intro k; induction' k with k ih
  · intro c d; exists 0
  · intro c d; rw [show d + (k + 1) = (d + k) + 1 from by ring]
    step fm
    apply stepStar_trans (ih (c + 1) d); ring_nf; finish

-- R3,R2x3 drain
theorem r3r2_drain : ∀ k d e, ⟨(0 : ℕ), k, 0, d, e + 1⟩ [fm]⊢* ⟨0, 0, 0, d + 3 * k, e + 2 * k + 1⟩ := by
  intro k; induction' k with k ih
  · intro d e; exists 0
  · intro d e
    step fm -- R3: (3, k, 0, d, e)
    step fm -- R2: (2, k, 0, d+1, e+1)
    step fm -- R2: (1, k, 0, d+1+1, e+1+1)
    step fm -- R2: (0, k, 0, d+1+1+1, e+1+1+1)
    rw [show d + 1 + 1 + 1 = d + 3 from by ring,
        show e + 1 + 1 + 1 = (e + 2) + 1 from by ring]
    apply stepStar_trans (ih (d + 3) (e + 2)); ring_nf; finish

-- R1x3,R3 interleaved chain: n rounds
theorem r1r3_chain : ∀ n b d f, ⟨(3 : ℕ), b, 3 * n + 2, d, f + n⟩ [fm]⊢* ⟨3, b + 5 * n, 2, d + 3 * n, f⟩ := by
  intro n; induction' n with n ih
  · intro b d f; exists 0
  · intro b d f
    rw [show 3 * (n + 1) + 2 = (3 * n + 2) + 3 from by ring,
        show f + (n + 1) = f + n + 1 from by ring]
    step fm -- R1: (2, b+2, 3n+2+2, d+1, f+n+1)
    step fm -- R1: (1, b+2+2, 3n+2+1, d+1+1, f+n+1)
    step fm -- R1: (0, b+2+2+2, 3n+2, d+1+1+1, f+n+1)
    rw [show b + 2 + 2 + 2 = (b + 5) + 1 from by ring,
        show d + 1 + 1 + 1 = d + 3 from by ring,
        show f + n + 1 = (f + n) + 1 from by ring]
    step fm -- R3: (3, b+5, 3n+2, d+3, f+n)
    apply stepStar_trans (ih (b + 5) (d + 3) f); ring_nf; finish

-- Full transition from canonical state
theorem main_trans (d e : ℕ) :
    ⟨(0 : ℕ), 0, 0, 3 * d + 3, e + d + 1⟩ [fm]⊢⁺
    ⟨0, 0, 0, 18 * d + 15, e + 10 * d + 9⟩ := by
  -- Phase 1: R4 chain
  rw [show 3 * d + 3 = 0 + (3 * d + 3) from by ring]
  apply stepStar_stepPlus_stepPlus (d_to_c (3 * d + 3) 0 (c := 0) (e := e + d + 1))
  rw [show 0 + (3 * d + 3) = (3 * d + 2) + 1 from by ring]
  -- Phase 2: R5 then R3
  step fm -- R5: (0, 1, 3d+2, 0, e+d+1)
  rw [show e + d + 1 = (e + d) + 1 from by ring]
  step fm -- R3: (3, 0, 3d+2, 0, e+d)
  -- Phase 3: R1x3,R3 interleaved chain
  apply stepStar_trans (r1r3_chain d 0 0 e)
  rw [show 0 + 5 * d = 5 * d from by ring,
      show 0 + 3 * d = 3 * d from by ring]
  -- Phase 4: R1, R1, R2
  step fm -- R1: (2, 5d+2, 1, 3d+1, e)
  step fm -- R1: (1, 5d+2+2, 0, 3d+1+1, e)
  rw [show 5 * d + 2 + 2 = 5 * d + 4 from by ring,
      show 3 * d + 1 + 1 = 3 * d + 2 from by ring]
  step fm -- R2: (0, 5d+4, 0, 3d+2+1, e+1)
  rw [show 3 * d + 2 + 1 = 3 * d + 3 from by ring]
  -- Phase 5: R3,R2x3 drain
  apply stepStar_trans (r3r2_drain (5 * d + 4) (3 * d + 3) e)
  ring_nf; finish

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨0, 0, 0, 3, 3⟩)
  · execute fm 7
  apply progress_nonhalt_simple (fm := fm) (A := ℕ × ℕ)
    (fun ⟨d, e⟩ ↦ ⟨0, 0, 0, 3 * (d + 1), e + d + 1⟩) ⟨0, 2⟩
  intro ⟨d, e⟩
  refine ⟨⟨6 * d + 4, e + 4 * d + 4⟩, ?_⟩
  show ⟨(0 : ℕ), 0, 0, 3 * (d + 1), e + d + 1⟩ [fm]⊢⁺
    ⟨0, 0, 0, 3 * (6 * d + 4 + 1), e + 4 * d + 4 + (6 * d + 4) + 1⟩
  rw [show 3 * (d + 1) = 3 * d + 3 from by ring,
      show 3 * (6 * d + 4 + 1) = 18 * d + 15 from by ring,
      show e + 4 * d + 4 + (6 * d + 4) + 1 = e + 10 * d + 9 from by ring]
  exact main_trans d e

end Sz22_2003_unofficial_1387
