import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #1210: [5/6, 539/2, 4/35, 9/11, 22/7]

Vector representation:
```
-1 -1  1  0  0
-1  0  0  2  1
 2  0 -1 -1  0
 0  2  0  0 -1
 1  0  0 -1  1
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_1210

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a+1, b+1, c, d, e⟩ => some ⟨a, b, c+1, d, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b, c, d+2, e+1⟩
  | ⟨a, b, c+1, d+1, e⟩ => some ⟨a+2, b, c, d, e⟩
  | ⟨a, b, c, d, e+1⟩ => some ⟨a, b+2, c, d, e⟩
  | ⟨a, b, c, d+1, e⟩ => some ⟨a+1, b, c, d, e+1⟩
  | _ => none

-- R4 chain: (0, b, 0, d, k) →* (0, b+2k, 0, d, 0)
theorem e_to_b : ∀ k b d, ⟨0, b, 0, d, k⟩ [fm]⊢* ⟨0, b + 2 * k, 0, d, 0⟩ := by
  intro k; induction' k with k ih <;> intro b d
  · exists 0
  · step fm
    apply stepStar_trans (ih (b + 2) d)
    ring_nf; finish

-- R1R1R3 chain: (2, b+2k, c, d+k, 1) →* (2, b, c+k, d, 1)
theorem r1r1r3_chain : ∀ k b c d, ⟨2, b + 2 * k, c, d + k, 1⟩ [fm]⊢* ⟨2, b, c + k, d, 1⟩ := by
  intro k; induction' k with k ih <;> intro b c d
  · exists 0
  · rw [show b + 2 * (k + 1) = (b + 2) + 2 * k from by ring,
        show d + (k + 1) = (d + 1) + k from by ring]
    apply stepStar_trans (ih (b + 2) c (d + 1))
    rw [show b + 2 = (b + 1) + 1 from by ring]
    step fm
    step fm
    step fm
    rw [show c + k + 1 = c + (k + 1) from by ring]
    finish

-- R3R2R2 chain: (0, 0, c+k, d+1, e) →* (0, 0, c, d+1+3k, e+2k)
theorem r3r2r2_chain : ∀ k c d e, ⟨0, 0, c + k, d + 1, e⟩ [fm]⊢* ⟨0, 0, c, d + 1 + 3 * k, e + 2 * k⟩ := by
  intro k; induction' k with k ih <;> intro c d e
  · exists 0
  · rw [show c + (k + 1) = (c + k) + 1 from by ring]
    step fm
    step fm
    step fm
    rw [show d + 4 = (d + 3) + 1 from by ring]
    apply stepStar_trans (ih c (d + 3) (e + 2))
    ring_nf; finish

-- Full transition: (0, 0, 0, d+e+2, e+1) →⁺ (0, 0, 0, d+3e+5, 2e+4)
theorem main_trans (d e : ℕ) :
    ⟨(0 : ℕ), 0, 0, d + e + 2, e + 1⟩ [fm]⊢⁺ ⟨(0 : ℕ), 0, 0, d + 3 * e + 5, 2 * e + 4⟩ := by
  -- First R4 step to establish ⊢⁺
  step fm
  -- State: (0, 2, 0, d+e+2, e). Goal is ⊢*
  -- Remaining R4 steps (e rounds): (0, 2, 0, d+e+2, e) →* (0, 2+2e, 0, d+e+2, 0)
  apply stepStar_trans (e_to_b e 2 (d + e + 2))
  rw [show 2 + 2 * e = 2 * e + 2 from by ring]
  -- State: (0, 2e+2, 0, d+e+2, 0)
  -- R5
  rw [show d + e + 2 = (d + e + 1) + 1 from by ring]
  step fm
  -- State: (1, 2e+2, 0, d+e+1, 1)
  -- R1
  rw [show 2 * e + 2 = (2 * e + 1) + 1 from by ring]
  step fm
  -- State: (0, 2e+1, 1, d+e+1, 1)
  -- R3
  rw [show d + e + 1 = (d + e) + 1 from by ring]
  step fm
  -- State: (2, 2e+1, 0, d+e, 1)
  -- R1R1R3 chain (e rounds)
  rw [show 2 * e + 1 = 1 + 2 * e from by ring]
  apply stepStar_trans (r1r1r3_chain e 1 0 d)
  rw [show 0 + e = e from by ring]
  -- State: (2, 1, e, d, 1)
  -- R1
  step fm
  -- State: (1, 0, e+1, d, 1)
  -- R2
  step fm
  -- State: (0, 0, e+1, d+2, 2)
  -- R3R2R2 chain (e+1 rounds)
  rw [show e + 1 = 0 + (e + 1) from by ring,
      show d + 2 = (d + 1) + 1 from by ring]
  apply stepStar_trans (r3r2r2_chain (e + 1) 0 (d + 1) 2)
  have h1 : d + 1 + 1 + 3 * (e + 1) = d + 3 * e + 5 := by ring
  have h2 : 2 + 2 * (e + 1) = 2 * e + 4 := by ring
  rw [h1, h2]; finish

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨0, 0, 0, 5, 4⟩)
  · execute fm 10
  apply progress_nonhalt_simple (fm := fm) (A := ℕ × ℕ)
    (fun ⟨d, e⟩ ↦ ⟨0, 0, 0, d + e + 2, e + 1⟩) ⟨0, 3⟩
  intro ⟨d, e⟩
  refine ⟨⟨d + e, 2 * e + 3⟩, ?_⟩
  show ⟨(0 : ℕ), 0, 0, d + e + 2, e + 1⟩ [fm]⊢⁺
    ⟨0, 0, 0, (d + e) + (2 * e + 3) + 2, (2 * e + 3) + 1⟩
  rw [show (d + e) + (2 * e + 3) + 2 = d + 3 * e + 5 from by ring,
      show (2 * e + 3) + 1 = 2 * e + 4 from by ring]
  exact main_trans d e

end Sz22_2003_unofficial_1210
