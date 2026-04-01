import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #1449: [7/15, 2662/3, 3/77, 5/121, 21/2]

Vector representation:
```
 0 -1 -1  1  0
 1 -1  0  0  3
 0  1  0 -1 -1
 0  0  1  0 -2
-1  1  0  1  0
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_1449

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a, b+1, c+1, d, e⟩ => some ⟨a, b, c, d+1, e⟩
  | ⟨a, b+1, c, d, e⟩ => some ⟨a+1, b, c, d, e+3⟩
  | ⟨a, b, c, d+1, e+1⟩ => some ⟨a, b+1, c, d, e⟩
  | ⟨a, b, c, d, e+2⟩ => some ⟨a, b, c+1, d, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b+1, c, d+1, e⟩
  | _ => none

-- R3+R2 chain: each round R3 then R2. Net per round: a+1, d-1, e+2.
theorem r3r2_chain : ∀ k, ⟨a, 0, 0, d + k, e + 1⟩ [fm]⊢* ⟨a + k, 0, 0, d, e + 2 * k + 1⟩ := by
  intro k; induction' k with k ih generalizing a d e
  · exists 0
  · rw [show d + (k + 1) = (d + k) + 1 from by ring]
    step fm; step fm
    rw [show e + 3 = (e + 2) + 1 from by ring]
    apply stepStar_trans (ih (a := a + 1) (e := e + 2))
    ring_nf; finish

-- R4 chain: pair off e into c.
theorem r4_chain : ∀ k, ∀ c, ⟨a, 0, c, 0, e + 2 * k⟩ [fm]⊢* ⟨a, 0, c + k, 0, e⟩ := by
  intro k; induction' k with k ih
  · intro c; exists 0
  · intro c
    rw [show e + 2 * (k + 1) = (e + 2 * k) + 2 from by ring]
    step fm
    apply stepStar_trans (ih (c + 1))
    ring_nf; finish

-- R5+R1 chain: drain a and c, building d.
-- From (k+1, 0, k, d, 0), after k rounds: (1, 0, 0, d+2k, 0).
theorem r5r1_chain : ∀ k d, ⟨k + 1, 0, k, d, 0⟩ [fm]⊢* ⟨1, 0, 0, d + 2 * k, 0⟩ := by
  intro k; induction' k with k ih
  · intro d; exists 0
  · intro d
    step fm; step fm
    apply stepStar_trans (ih (d + 2))
    ring_nf; finish

-- Combined: 4 transition steps + R5+R1 chain.
-- (n+2, 0, n+2, 0, 1) ⊢⁺ (1, 0, 0, 2n+2, 0)
theorem mid_and_drain (n : ℕ) :
    ⟨n + 2, 0, n + 2, 0, 1⟩ [fm]⊢⁺ ⟨1, 0, 0, 2 * n + 2, 0⟩ := by
  step fm  -- R5
  step fm  -- R1
  step fm  -- R3
  step fm  -- R1: now at (n+1, 0, n, 2, 0)
  apply stepStar_trans (r5r1_chain n 2)
  ring_nf; finish

-- Main transition: (1, 0, 0, D+2, 0) ⊢⁺ (1, 0, 0, 2D+6, 0)
theorem main_trans (D : ℕ) :
    ⟨1, 0, 0, D + 2, 0⟩ [fm]⊢⁺ ⟨1, 0, 0, 2 * D + 6, 0⟩ := by
  -- R5: (0, 1, 0, D+3, 0). R2: (1, 0, 0, D+3, 3).
  step fm; step fm
  -- R3+R2 chain with k = D+3
  rw [show D + 3 = 0 + (D + 3) from by ring,
      show (3 : ℕ) = 2 + 1 from by ring]
  apply stepStar_trans (r3r2_chain (D + 3) (a := 1) (d := 0) (e := 2))
  -- Now at (D+4, 0, 0, 0, 2D+9)
  show ⟨1 + (D + 3), 0, 0, 0, 2 + 2 * (D + 3) + 1⟩ [fm]⊢* _
  rw [show 2 + 2 * (D + 3) + 1 = 1 + 2 * (D + 4) from by ring,
      show 1 + (D + 3) = D + 4 from by ring]
  -- R4 chain with k = D+4
  apply stepStar_trans (r4_chain (D + 4) (c := 0) (e := 1))
  -- Now at (D+4, 0, D+4, 0, 1)
  show ⟨D + 4, 0, 0 + (D + 4), 0, 1⟩ [fm]⊢* _
  rw [show 0 + (D + 4) = D + 4 from by ring,
      show D + 4 = (D + 2) + 2 from by ring]
  -- mid_and_drain: (D+4, 0, D+4, 0, 1) ⊢⁺ (1, 0, 0, 2*(D+2)+2, 0)
  apply stepStar_trans (stepPlus_stepStar (mid_and_drain (D + 2)))
  ring_nf; finish

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨1, 0, 0, 2, 0⟩)
  · execute fm 10
  apply progress_nonhalt_simple (fm := fm) (A := ℕ)
    (fun n ↦ ⟨1, 0, 0, n + 2, 0⟩) 0
  intro n; exact ⟨2 * n + 4, main_trans n⟩

end Sz22_2003_unofficial_1449
