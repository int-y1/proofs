import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #1475: [7/15, 4/3, 99/14, 25/11, 21/2]

Vector representation:
```
 0 -1 -1  1  0
 2 -1  0  0  0
-1  2  0 -1  1
 0  0  2  0 -1
-1  1  0  1  0
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_1475

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a, b+1, c+1, d, e⟩ => some ⟨a, b, c, d+1, e⟩
  | ⟨a, b+1, c, d, e⟩ => some ⟨a+2, b, c, d, e⟩
  | ⟨a+1, b, c, d+1, e⟩ => some ⟨a, b+2, c, d, e+1⟩
  | ⟨a, b, c, d, e+1⟩ => some ⟨a, b, c+2, d, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b+1, c, d+1, e⟩
  | _ => none

-- R4 chain: transfer e to c.
theorem e_to_c : ∀ k, ⟨a, 0, c, 0, e + k⟩ [fm]⊢* ⟨a, 0, c + 2 * k, 0, e⟩ := by
  intro k; induction' k with k ih generalizing c e
  · exists 0
  · rw [show e + (k + 1) = (e + k) + 1 from by ring]; step fm
    apply stepStar_trans (ih (c := c + 2) (e := e)); ring_nf; finish

-- R3,R1,R1 interleaved chain: each round drains a by 1, c by 2, increments d and e by 1.
theorem r3r1r1_chain : ∀ k, ∀ a c d e, ⟨a + k, 0, c + 2 * k, d + 1, e⟩ [fm]⊢* ⟨a, 0, c, d + 1 + k, e + k⟩ := by
  intro k; induction' k with k ih
  · intro a c d e; exists 0
  · intro a c d e
    rw [show a + (k + 1) = (a + k) + 1 from by ring,
        show c + 2 * (k + 1) = (c + 2 * k) + 1 + 1 from by ring,
        show d + 1 = d + 1 from rfl]
    step fm; step fm; step fm
    apply stepStar_trans (ih a c (d + 1) (e + 1)); ring_nf; finish

-- R3,R2,R2 drain: each round adds 3 to a, transfers 1 from d to e.
theorem drain_d : ∀ k, ∀ a d e, ⟨a + 1, 0, 0, d + k, e⟩ [fm]⊢* ⟨a + 1 + 3 * k, 0, 0, d, e + k⟩ := by
  intro k; induction' k with k ih
  · intro a d e; exists 0
  · intro a d e
    rw [show d + (k + 1) = (d + k) + 1 from by ring]
    step fm; step fm; step fm
    apply stepStar_trans (ih (a + 3) d (e + 1)); ring_nf; finish

-- Main transition: (A, 0, 0, 0, E+1) ⊢⁺ (A + 2*E + 6, 0, 0, 0, 2*E + 3).
-- Parameterized as: (n+e+2, 0, 0, 0, e+1) ⊢⁺ (n+3*e+8, 0, 0, 0, 2*e+3).
theorem main_trans (n e : ℕ) :
    ⟨n + e + 2, 0, 0, 0, e + 1⟩ [fm]⊢⁺ ⟨n + 3 * e + 8, 0, 0, 0, 2 * e + 3⟩ := by
  -- Phase 1: R4 chain (e+1 steps): e+1 → 0, c: 0 → 2*(e+1).
  rw [show (e + 1 : ℕ) = 0 + (e + 1) from by ring]
  apply stepStar_stepPlus_stepPlus (e_to_c (e + 1) (a := n + e + 2) (c := 0) (e := 0))
  rw [show (0 : ℕ) + 2 * (e + 1) = 2 * e + 2 from by ring]
  -- Phase 2: R5 step.
  rw [show n + e + 2 = (n + e + 1) + 1 from by ring]
  step fm
  -- Phase 3: R1 step (b=1, c=2*e+2 >= 1).
  rw [show 2 * e + 2 = (2 * e + 1) + 1 from by ring]
  step fm
  -- Now at: (n+e+1, 0, 2*e+1, 2, 0).
  -- Phase 4: R3,R1,R1 interleaved chain (e rounds).
  rw [show (n + e + 1 : ℕ) = (n + 1) + e from by ring,
      show (2 * e + 1 : ℕ) = 1 + 2 * e from by ring]
  apply stepStar_trans (r3r1r1_chain e (n + 1) 1 1 0)
  rw [show 1 + 1 + e = e + 2 from by ring, show 0 + e = e from by ring]
  -- Now at: (n+1, 0, 1, e+2, e).
  -- Phase 5: R3, R1, R2 end sequence (3 steps).
  rw [show n + 1 = n + 1 from rfl, show e + 2 = (e + 1) + 1 from by ring]
  step fm  -- R3: (n, 2, 1, e+1, e+1)
  step fm  -- R1: (n, 1, 0, e+2, e+1)
  step fm  -- R2: (n+2, 0, 0, e+2, e+1)
  -- Now at: (n+2, 0, 0, e+2, e+1).
  -- Phase 6: R3,R2,R2 drain (e+2 rounds).
  rw [show n + 2 = (n + 1) + 1 from by ring,
      show (e + 2 : ℕ) = 0 + (e + 2) from by ring]
  apply stepStar_trans (drain_d (e + 2) (n + 1) 0 (e + 1))
  ring_nf; finish

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨5, 0, 0, 0, 1⟩) (by execute fm 5)
  apply progress_nonhalt_simple (fm := fm) (A := ℕ × ℕ)
    (fun ⟨n, e⟩ ↦ ⟨n + e + 2, 0, 0, 0, e + 1⟩) ⟨3, 0⟩
  intro ⟨n, e⟩; refine ⟨⟨n + e + 4, 2 * e + 2⟩, ?_⟩
  show ⟨n + e + 2, 0, 0, 0, e + 1⟩ [fm]⊢⁺ ⟨(n + e + 4) + (2 * e + 2) + 2, 0, 0, 0, (2 * e + 2) + 1⟩
  rw [show (n + e + 4) + (2 * e + 2) + 2 = n + 3 * e + 8 from by ring,
      show (2 * e + 2) + 1 = 2 * e + 3 from by ring]
  exact main_trans n e

end Sz22_2003_unofficial_1475
