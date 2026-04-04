import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #1730: [8/15, 33/14, 275/2, 7/11, 2/5]

Vector representation:
```
 3 -1 -1  0  0
-1  1  0 -1  1
-1  0  2  0  1
 0  0  0  1 -1
 1  0 -1  0  0
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_1730

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a, b+1, c+1, d, e⟩ => some ⟨a+3, b, c, d, e⟩
  | ⟨a+1, b, c, d+1, e⟩ => some ⟨a, b+1, c, d, e+1⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b, c+2, d, e+1⟩
  | ⟨a, b, c, d, e+1⟩ => some ⟨a, b, c, d+1, e⟩
  | ⟨a, b, c+1, d, e⟩ => some ⟨a+1, b, c, d, e⟩
  | _ => none

-- R2+R1 interleaved chain: k rounds.
-- Each round: R2 (a+1>=1, d>=1) then R1 (b=1>=1, c>=1).
-- (a+1, 0, c+k, d+k, e) →* (a+2k+1, 0, c, d, e+k)
theorem r2r1_chain : ∀ k a c d e, ⟨a + 1, 0, c + k, d + k, e⟩ [fm]⊢* ⟨a + 2 * k + 1, 0, c, d, e + k⟩ := by
  intro k; induction k with
  | zero => intro a c d e; exists 0
  | succ k ih =>
    intro a c d e
    rw [show c + (k + 1) = (c + k) + 1 from by ring,
        show d + (k + 1) = (d + k) + 1 from by ring]
    step fm
    step fm
    show ⟨(a + 2) + 1, 0, c + k, d + k, e + 1⟩ [fm]⊢* ⟨a + 2 * (k + 1) + 1, 0, c, d, e + (k + 1)⟩
    apply stepStar_trans (ih (a + 2) c d (e + 1))
    ring_nf; finish

-- R3 chain: convert a to c+e. (a+k, 0, c, 0, e) →* (a, 0, c+2k, 0, e+k)
theorem r3_chain : ∀ k a c e, ⟨a + k, 0, c, 0, e⟩ [fm]⊢* ⟨a, 0, c + 2 * k, 0, e + k⟩ := by
  intro k; induction k with
  | zero => intro a c e; exists 0
  | succ k ih =>
    intro a c e
    rw [show a + (k + 1) = (a + k) + 1 from by ring]
    step fm
    apply stepStar_trans (ih a (c + 2) (e + 1))
    ring_nf; finish

-- R4 chain: convert e to d. (0, 0, c, d, e+k) →* (0, 0, c, d+k, e)
theorem r4_chain : ∀ k c d e, ⟨0, 0, c, d, e + k⟩ [fm]⊢* ⟨0, 0, c, d + k, e⟩ := by
  intro k; induction k with
  | zero => intro c d e; exists 0
  | succ k ih =>
    intro c d e
    rw [show e + (k + 1) = (e + k) + 1 from by ring]
    step fm
    apply stepStar_trans (ih c (d + 1) e)
    ring_nf; finish

-- Full transition from (0, 0, d+F+2, d+1, 0) ⊢⁺ (0, 0, F+4d+6, 3d+4, 0)
-- Combines R5 + R2R1 chain + R3 chain + R4 chain
theorem phase_all : ⟨0, 0, d + F + 2, d + 1, 0⟩ [fm]⊢⁺ ⟨0, 0, F + 4 * d + 6, 3 * d + 4, 0⟩ := by
  -- R5 step
  apply step_stepStar_stepPlus
    (show (0, 0, d + F + 2, d + 1, 0) [fm]⊢ (1, 0, d + F + 1, d + 1, 0) from rfl)
  -- R2R1 chain
  have h1 := r2r1_chain (d + 1) 0 F 0 0
  simp only [Nat.zero_add] at h1
  rw [show F + (d + 1) = d + F + 1 from by ring,
      show 2 * (d + 1) + 1 = 2 * d + 3 from by ring] at h1
  apply stepStar_trans h1
  -- R3 chain
  have h2 := r3_chain (2 * d + 3) 0 F (d + 1)
  simp only [Nat.zero_add] at h2
  rw [show F + 2 * (2 * d + 3) = F + 4 * d + 6 from by ring,
      show d + 1 + (2 * d + 3) = 3 * d + 4 from by ring] at h2
  apply stepStar_trans h2
  -- R4 chain
  have h3 := r4_chain (3 * d + 4) (F + 4 * d + 6) 0 0
  simp only [Nat.zero_add] at h3
  exact h3

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨0, 0, 0 + 0 + 2, 0 + 1, 0⟩) (by execute fm 2)
  apply progress_nonhalt_simple (fm := fm) (A := ℕ × ℕ)
    (fun ⟨F, d⟩ ↦ ⟨0, 0, d + F + 2, d + 1, 0⟩) ⟨0, 0⟩
  intro ⟨F, d⟩
  refine ⟨⟨F + d + 1, 3 * d + 3⟩, ?_⟩
  show ⟨0, 0, d + F + 2, d + 1, 0⟩ [fm]⊢⁺ ⟨0, 0, (3 * d + 3) + (F + d + 1) + 2, (3 * d + 3) + 1, 0⟩
  rw [show (3 * d + 3) + (F + d + 1) + 2 = F + 4 * d + 6 from by ring,
      show (3 * d + 3) + 1 = 3 * d + 4 from by ring]
  exact phase_all
