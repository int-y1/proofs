import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #1870: [9/35, 25/66, 14/3, 11/7, 35/2]

Vector representation:
```
 0  2 -1 -1  0
-1 -1  2  0 -1
 1 -1  0  1  0
 0  0  0 -1  1
-1  0  1  1  0
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_1870

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a, b, c+1, d+1, e⟩ => some ⟨a, b+2, c, d, e⟩
  | ⟨a+1, b+1, c, d, e+1⟩ => some ⟨a, b, c+2, d, e⟩
  | ⟨a, b+1, c, d, e⟩ => some ⟨a+1, b, c, d+1, e⟩
  | ⟨a, b, c, d+1, e⟩ => some ⟨a, b, c, d, e+1⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b, c+1, d+1, e⟩
  | _ => none

-- R4 repeated: move d to e. General version with nonzero initial e.
theorem d_to_e : ∀ k, ∀ d, ⟨a, 0, 0, d + k, e⟩ [fm]⊢* ⟨a, 0, 0, d, e + k⟩ := by
  intro k; induction' k with k ih <;> intro d
  · exists 0
  · rw [show d + (k + 1) = (d + 1) + k from by ring]
    apply stepStar_trans (ih (d + 1))
    step fm
    rw [show e + k + 1 = e + (k + 1) from by ring]
    finish

-- R5, R1, R2, R2: one round.
theorem r5r1r2r2_step : ⟨a + 3, 0, c, 0, e + 2⟩ [fm]⊢* ⟨a, 0, c + 4, 0, e⟩ := by
  rw [show a + 3 = (a + 2) + 1 from by ring]
  step fm
  step fm
  rw [show a + 2 = (a + 1) + 1 from by ring,
      show e + 2 = (e + 1) + 1 from by ring]
  step fm
  step fm
  ring_nf; finish

-- R5, R1, R2, R2 chain: k rounds.
theorem r5r1r2r2_chain : ∀ k c, ⟨a + 3 * k, 0, c, 0, e + 2 * k⟩ [fm]⊢*
    ⟨a, 0, c + 4 * k, 0, e⟩ := by
  intro k; induction' k with k ih <;> intro c
  · exists 0
  · rw [show a + 3 * (k + 1) = (a + 3 * k) + 3 from by ring,
        show e + 2 * (k + 1) = (e + 2 * k) + 2 from by ring]
    apply stepStar_trans (r5r1r2r2_step (a := a + 3 * k) (c := c) (e := e + 2 * k))
    apply stepStar_trans (ih (c + 4))
    ring_nf; finish

-- R5 + R1: 2 steps.
theorem r5_r1 : ⟨a + 1, 0, c + 1, 0, 0⟩ [fm]⊢* ⟨a, 2, c + 1, 0, 0⟩ := by
  apply stepStar_trans (step_stepStar (c₂ := ⟨a, 0, c + 2, 1, 0⟩) (by simp [fm]))
  rw [show c + 2 = (c + 1) + 1 from by ring, show (1 : ℕ) = 0 + 1 from by ring]
  step fm; finish

-- R3 + R1 chain: each round a += 1, b += 1, c -= 1.
theorem r3r1_chain : ∀ k, ∀ a b c, ⟨a, b + 1, c + k, 0, 0⟩ [fm]⊢*
    ⟨a + k, b + k + 1, c, 0, 0⟩ := by
  intro k; induction' k with k ih <;> intro a b c
  · exists 0
  · rw [show c + (k + 1) = (c + k) + 1 from by ring]
    step fm
    step fm
    apply stepStar_trans (ih (a + 1) (b + 1) c)
    ring_nf; finish

-- R3 repeated: drain b to a and d.
theorem b_to_ad : ∀ k, ∀ a d, ⟨a, k, 0, d, 0⟩ [fm]⊢* ⟨a + k, 0, 0, d + k, 0⟩ := by
  intro k; induction' k with k ih <;> intro a d
  · exists 0
  · step fm
    apply stepStar_trans (ih (a + 1) (d + 1))
    ring_nf; finish

-- Main transition
theorem main_trans (G F : ℕ) :
    (⟨G + 3 * F + 7, 0, 0, 2 * F + 4, 0⟩ : Q) [fm]⊢⁺
    ⟨G + 8 * F + 18, 0, 0, 4 * F + 10, 0⟩ := by
  -- Phase 1: first R4 step for ⊢⁺.
  rw [show (2 * F + 4 : ℕ) = (2 * F + 3) + 1 from by ring]
  step fm
  -- Now at (G+3F+7, 0, 0, 2F+3, 1). Continue R4 drain.
  rw [show (1 : ℕ) = 0 + 1 from by ring,
      show (2 * F + 3 : ℕ) = 0 + (2 * F + 3) from by ring]
  apply stepStar_trans (d_to_e (2 * F + 3) 0 (a := G + 3 * F + 7) (e := 0 + 1))
  -- Now at (G+3F+7, 0, 0, 0, 2F+4).
  rw [show 0 + 1 + (2 * F + 3) = 2 * F + 4 from by ring]
  -- Phase 2: F+2 rounds of R5,R1,R2,R2.
  rw [show G + 3 * F + 7 = (G + 1) + 3 * (F + 2) from by ring,
      show 2 * F + 4 = 0 + 2 * (F + 2) from by ring]
  apply stepStar_trans (r5r1r2r2_chain (F + 2) 0 (a := G + 1) (e := 0))
  -- Now at (G+1, 0, 4F+8, 0, 0).
  rw [show 0 + 4 * (F + 2) = (4 * F + 7) + 1 from by ring,
      show G + 1 = G + 1 from rfl]
  -- Phase 3: R5 + R1.
  apply stepStar_trans (r5_r1 (a := G) (c := 4 * F + 7))
  -- Now at (G, 2, 4F+8, 0, 0).
  rw [show 4 * F + 7 + 1 = 4 * F + 8 from by ring]
  -- Phase 4: R3+R1 chain for 4F+8 rounds.
  rw [show (2 : ℕ) = 1 + 1 from by ring,
      show 4 * F + 8 = 0 + (4 * F + 8) from by ring]
  apply stepStar_trans (r3r1_chain (4 * F + 8) G 1 0)
  -- Now at (G+4F+8, 4F+10, 0, 0, 0).
  rw [show 1 + (4 * F + 8) + 1 = 4 * F + 10 from by ring,
      show G + (4 * F + 8) = G + 4 * F + 8 from by ring]
  -- Phase 5: R3 drain b.
  apply stepStar_trans (b_to_ad (4 * F + 10) (G + 4 * F + 8) 0)
  ring_nf; finish

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨7, 0, 0, 4, 0⟩) (by execute fm 22)
  apply progress_nonhalt_simple (fm := fm) (A := ℕ × ℕ)
    (fun ⟨G, F⟩ ↦ ⟨G + 3 * F + 7, 0, 0, 2 * F + 4, 0⟩) ⟨0, 0⟩
  intro ⟨G, F⟩
  refine ⟨⟨G + 2 * F + 2, 2 * F + 3⟩, ?_⟩
  show (⟨G + 3 * F + 7, 0, 0, 2 * F + 4, 0⟩ : Q) [fm]⊢⁺
    ⟨(G + 2 * F + 2) + 3 * (2 * F + 3) + 7, 0, 0, 2 * (2 * F + 3) + 4, 0⟩
  rw [show (G + 2 * F + 2) + 3 * (2 * F + 3) + 7 = G + 8 * F + 18 from by ring,
      show 2 * (2 * F + 3) + 4 = 4 * F + 10 from by ring]
  exact main_trans G F
