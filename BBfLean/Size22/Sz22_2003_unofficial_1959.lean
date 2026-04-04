import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #1959: [945/2, 4/55, 1/45, 11/3, 5/7]

Vector representation:
```
-1  3  1  1  0
 2  0 -1  0 -1
 0 -2 -1  0  0
 0 -1  0  0  1
 0  0  1 -1  0
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_1959

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b+3, c+1, d+1, e⟩
  | ⟨a, b, c+1, d, e+1⟩ => some ⟨a+2, b, c, d, e⟩
  | ⟨a, b+2, c+1, d, e⟩ => some ⟨a, b, c, d, e⟩
  | ⟨a, b+1, c, d, e⟩ => some ⟨a, b, c, d, e+1⟩
  | ⟨a, b, c, d+1, e⟩ => some ⟨a, b, c+1, d, e⟩
  | _ => none

-- R2+R1+R1 chain: interleaved loop consuming e.
-- From (0, b, c+1, d, E) after E rounds of R2+R1+R1:
-- (0, b+6*E, c+E+1, d+2*E, 0)
theorem r2r1r1_chain : ∀ E b c d, ⟨0, b, c+1, d, E⟩ [fm]⊢* ⟨0, b + 6 * E, c + E + 1, d + 2 * E, 0⟩ := by
  intro E; induction' E with E ih <;> intro b c d
  · exists 0
  · step fm  -- R2: (2, b, c, d, E)
    step fm  -- R1: (1, b+3, c+1, d+1, E)
    step fm  -- R1: (0, b+6, c+2, d+2, E)
    rw [show c + 2 = (c + 1) + 1 from by ring]
    apply stepStar_trans (ih (b + 6) (c + 1) (d + 2))
    ring_nf; finish

-- R3 chain: drain b and c together (b -= 2, c -= 1 each step).
-- (0, b+2*k, c+k, d, 0) ⊢* (0, b, c, d, 0)
theorem r3_chain : ∀ k b c d, ⟨0, b + 2 * k, c + k, d, 0⟩ [fm]⊢* ⟨0, b, c, d, 0⟩ := by
  intro k; induction' k with k ih <;> intro b c d
  · exists 0
  · rw [show b + 2 * (k + 1) = (b + 2 * k) + 2 from by ring,
        show c + (k + 1) = (c + k) + 1 from by ring]
    step fm  -- R3
    exact ih b c d

-- R4 chain: drain b to e.
-- (0, k, 0, d, e) ⊢* (0, 0, 0, d, e+k)
theorem r4_chain : ∀ k d e, ⟨0, k, 0, d, e⟩ [fm]⊢* ⟨0, 0, 0, d, e + k⟩ := by
  intro k; induction' k with k ih <;> intro d e
  · exists 0
  · step fm  -- R4: (0, k, 0, d, e+1)
    apply stepStar_trans (ih d (e + 1))
    ring_nf; finish

-- Main transition: C(d, e) = (0, 0, 0, d+1, e+1) ⊢⁺ C(d+2e+1, 4e+1) = (0, 0, 0, d+2e+2, 4e+2)
theorem main_trans (d e : ℕ) : ⟨0, 0, 0, d + 1, e + 1⟩ [fm]⊢⁺ ⟨0, 0, 0, d + 2 * e + 2, 4 * e + 2⟩ := by
  -- R5: (0, 0, 1, d, e+1)
  step fm
  -- R2: (2, 0, 0, d, e)
  step fm
  -- R1: (1, 3, 1, d+1, e)
  step fm
  -- R1: (0, 6, 2, d+2, e)
  step fm
  -- r2r1r1_chain: (0, 6, 2, d+2, e) ⊢* (0, 6+6*e, 1+e+1+1, d+2+2*e, 0)
  rw [show (2 : ℕ) = 1 + 1 from by ring]
  apply stepStar_trans (r2r1r1_chain e 6 1 (d + 2))
  -- Now at (0, 6+6*e, 1+e+1+1, d+2+2*e, 0) = (0, 6e+6, e+2+1, d+2e+2, 0)
  -- Wait we need to match: (0, 6+6*e, 1+e+1+1, d+2+2*e, 0)
  -- Rewrite for R3 chain
  -- After r2r1r1_chain: (0, 6+6*e, 1+e+1, d+2+2*e, 0)
  -- = (0, 6*(e+1), e+2, d+2e+2, 0)
  -- R3 chain with k = e+2: (0, 6*(e+1), e+2, d+2e+2, 0)
  -- 6*(e+1) = 0 + 2*(e+2) + (4*e+2-0)... hmm let me compute
  -- 6+6*e = b + 2*k where k = e+2 and b = 6+6*e - 2*(e+2) = 4*e+2
  -- c + k where k = e+2 and c = 0
  rw [show 6 + 6 * e = (4 * e + 2) + 2 * (e + 2) from by ring,
      show 1 + e + 1 = 0 + (e + 2) from by ring]
  apply stepStar_trans (r3_chain (e + 2) (4 * e + 2) 0 (d + 2 + 2 * e))
  -- Now at (0, 4*e+2, 0, d+2+2*e, 0)
  rw [show d + 2 + 2 * e = d + 2 * e + 2 from by ring]
  apply stepStar_trans (r4_chain (4 * e + 2) (d + 2 * e + 2) 0)
  ring_nf; finish

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨0, 0, 0, 1, 1⟩) (by execute fm 3)
  apply progress_nonhalt_simple (fm := fm) (A := ℕ × ℕ)
    (fun ⟨d, e⟩ ↦ ⟨0, 0, 0, d + 1, e + 1⟩) ⟨0, 0⟩
  intro ⟨d, e⟩; exact ⟨⟨d + 2 * e + 1, 4 * e + 1⟩, main_trans d e⟩
