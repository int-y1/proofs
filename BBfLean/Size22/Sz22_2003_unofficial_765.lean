import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #765: [35/6, 4/55, 9317/2, 3/7, 5/3]

Vector representation:
```
-1 -1  1  1  0
 2  0 -1  0 -1
-1  0  0  1  3
 0  1  0 -1  0
 0 -1  1  0  0
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_765

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a+1, b+1, c, d, e⟩ => some ⟨a, b, c+1, d+1, e⟩
  | ⟨a, b, c+1, d, e+1⟩ => some ⟨a+2, b, c, d, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b, c, d+1, e+3⟩
  | ⟨a, b, c, d+1, e⟩ => some ⟨a, b+1, c, d, e⟩
  | ⟨a, b+1, c, d, e⟩ => some ⟨a, b, c+1, d, e⟩
  | _ => none

-- R4 chain: move d to b
theorem r4_chain : ∀ k, ⟨0, b, 0, d + k, e⟩ [fm]⊢* ⟨0, b + k, 0, d, e⟩ := by
  intro k; induction' k with k ih generalizing b d
  · exists 0
  · rw [show d + (k + 1) = (d + k) + 1 from by ring]
    step fm
    apply stepStar_trans (ih (b := b + 1))
    ring_nf; finish

-- R2 drain: drain c into a (b must be 0)
theorem r2_drain : ∀ k, ⟨a, 0, k, d, e + k⟩ [fm]⊢* ⟨a + 2 * k, 0, 0, d, e⟩ := by
  intro k; induction' k with k ih generalizing a e
  · exists 0
  · rw [show e + (k + 1) = (e + k) + 1 from by ring]
    step fm
    apply stepStar_trans (ih (a := a + 2))
    ring_nf; finish

-- R3 chain: drain a, incrementing d and e
theorem r3_chain : ∀ k, ⟨a + k, 0, 0, d, e⟩ [fm]⊢* ⟨a, 0, 0, d + k, e + 3 * k⟩ := by
  intro k; induction' k with k ih generalizing a d e
  · exists 0
  · rw [show a + (k + 1) = (a + k) + 1 from by ring]
    step fm
    apply stepStar_trans (ih (d := d + 1) (e := e + 3))
    ring_nf; finish

-- Spiral by strong induction on B.
-- (2, B, c, d, e + B + c) →* (B + 2c + 2, 0, 0, d + B, e)
theorem spiral : ∀ B, ∀ c d e, ⟨2, B, c, d, e + B + c⟩ [fm]⊢* ⟨B + 2 * c + 2, 0, 0, d + B, e⟩ := by
  intro B; induction' B using Nat.strongRecOn with B ih; intro c d e
  rcases B with _ | _ | B
  · -- B = 0: R2 drain
    rw [show e + 0 + c = e + c from by ring,
        show 0 + 2 * c + 2 = 2 + 2 * c from by ring,
        show d + 0 = d from by ring]
    exact r2_drain c
  · -- B = 1: R1, R2, R2 drain
    rw [show e + 1 + c = e + c + 1 from by ring,
        show 1 + 2 * c + 2 = 2 * c + 3 from by ring,
        show d + 1 = d + 1 from rfl]
    step fm
    rw [show e + c + 1 = (e + c) + 1 from by ring]
    step fm
    rw [show (2 * c + 3 : ℕ) = 3 + 2 * c from by ring]
    exact r2_drain c
  · -- B + 2: R1, R1, R2, then IH for B
    rw [show e + (B + 2) + c = e + c + (B + 2) from by ring]
    step fm -- R1: (1, B+1, c+1, d+1, e+c+(B+2))
    step fm -- R1: (0, B, c+2, d+2, e+c+(B+2))
    -- Now need R2: pattern (a, b, c+1, d, e+1) with a=0, b=B, c'=c+1, d'=d+2, e'=e+c+(B+2)
    -- e+c+(B+2) must be ≥ 1 (always true), and c+2 ≥ 1 (always true)
    -- After R2: (2, B, c+1, d+2, e+c+(B+2)-1)
    -- Need to show e+c+(B+2) has the form ...+1 for the R2 match
    rw [show e + c + (B + 2) = (e + c + B + 1) + 1 from by ring]
    step fm -- R2: (2, B, c+1, d+2, e+c+B+1)
    -- Now at (2, B, c+1, d+2, e+c+B+1)
    -- IH for B: need e' + B + (c+1) = e+c+B+1, so e' = e. ✓
    rw [show e + c + B + 1 = e + B + (c + 1) from by ring,
        show B + 2 + 2 * c + 2 = B + 2 * (c + 1) + 2 from by ring,
        show d + (B + 2) = (d + 2) + B from by ring]
    exact ih B (by omega) (c + 1) (d + 2) e

-- Main transition: (0, 0, 0, k+1, F+k+1) ⊢⁺ (0, 0, 0, 2k+2, F+3k+6)
theorem main_transition (k F : ℕ) :
    ⟨0, 0, 0, k + 1, F + k + 1⟩ [fm]⊢⁺ ⟨0, 0, 0, 2 * k + 2, F + 3 * k + 6⟩ := by
  -- Phase 1: R4 chain + R5 + R2 + Spiral + R3 chain
  -- We compose everything via stepStar/stepPlus.
  -- Use a helper for the middle part.
  -- First, go from (0, 0, 0, k+1, F+k+1) to (0, k+1, 0, 0, F+k+1) via R4.
  have hr4 : ⟨0, 0, 0, k + 1, F + k + 1⟩ [fm]⊢* ⟨0, k + 1, 0, 0, F + k + 1⟩ := by
    rw [show (k + 1 : ℕ) = 0 + (k + 1) from by ring]
    have := r4_chain (k + 1) (b := 0) (d := 0) (e := F + k + 1)
    simpa using this
  apply stepStar_stepPlus_stepPlus hr4
  -- R5: (0, k+1, 0, 0, F+k+1) → (0, k, 1, 0, F+k+1)
  step fm
  -- R2: (0, k, 1, 0, F+k+1) → (2, k, 0, 0, F+k)
  rw [show F + k + 1 = (F + k) + 1 from by ring]
  step fm
  -- Spiral: (2, k, 0, 0, F+k) →* (k+2, 0, 0, k, F)
  rw [show F + k = F + k + 0 from by ring]
  have hs := spiral k 0 0 F
  rw [show k + 2 * 0 + 2 = k + 2 from by ring, show 0 + k = k from by ring] at hs
  apply stepStar_trans hs
  -- R3 chain: (k+2, 0, 0, k, F) →* (0, 0, 0, 2k+2, F+3k+6)
  rw [show (k + 2 : ℕ) = 0 + (k + 2) from by ring]
  apply stepStar_trans (r3_chain (k + 2) (a := 0) (d := k) (e := F))
  ring_nf; finish

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨0, 0, 0, 1, 3⟩)
  · execute fm 1
  apply progress_nonhalt_simple (fm := fm) (A := ℕ × ℕ)
    (fun ⟨k, F⟩ ↦ ⟨0, 0, 0, k + 1, F + k + 1⟩) ⟨0, 2⟩
  intro ⟨k, F⟩
  exact ⟨⟨2 * k + 1, F + k + 4⟩, by
    show ⟨0, 0, 0, k + 1, F + k + 1⟩ [fm]⊢⁺ ⟨0, 0, 0, 2 * k + 1 + 1, F + k + 4 + (2 * k + 1) + 1⟩
    rw [show 2 * k + 1 + 1 = 2 * k + 2 from by ring,
        show F + k + 4 + (2 * k + 1) + 1 = F + 3 * k + 6 from by ring]
    exact main_transition k F⟩

end Sz22_2003_unofficial_765
