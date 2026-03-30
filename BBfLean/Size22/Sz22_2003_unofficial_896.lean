import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #896: [4/15, 1617/2, 11/21, 5/77, 3/11]

Vector representation:
```
 2 -1 -1  0  0
-1  1  0  2  1
 0 -1  0 -1  1
 0  0  1 -1 -1
 0  1  0  0 -1
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_896

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a, b+1, c+1, d, e⟩ => some ⟨a+2, b, c, d, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b+1, c, d+2, e+1⟩
  | ⟨a, b+1, c, d+1, e⟩ => some ⟨a, b, c, d, e+1⟩
  | ⟨a, b, c, d+1, e+1⟩ => some ⟨a, b, c+1, d, e⟩
  | ⟨a, b, c, d, e+1⟩ => some ⟨a, b+1, c, d, e⟩
  | _ => none

-- R4 chain: move min(d,e) to c
theorem r4_chain : ∀ k c d e, ⟨0, 0, c, d + k, e + k⟩ [fm]⊢* ⟨0, 0, c + k, d, e⟩ := by
  intro k; induction' k with k ih <;> intro c d e
  · exists 0
  · rw [show d + (k + 1) = (d + k) + 1 from by ring,
        show e + (k + 1) = (e + k) + 1 from by ring]
    step fm
    apply stepStar_trans (ih (c + 1) d e)
    ring_nf; finish

-- R2 chain: drain a, build b/d/e
theorem r2_chain : ∀ k a b d e, ⟨a + k, b, 0, d, e⟩ [fm]⊢* ⟨a, b + k, 0, d + 2 * k, e + k⟩ := by
  intro k; induction' k with k ih <;> intro a b d e
  · exists 0
  · rw [show a + (k + 1) = (a + k) + 1 from by ring]
    step fm
    apply stepStar_trans (ih a (b + 1) (d + 2) (e + 1))
    ring_nf; finish

-- R3 chain: drain b using d, build e
theorem r3_chain : ∀ k b d e, ⟨0, b + k, 0, d + k, e⟩ [fm]⊢* ⟨0, b, 0, d, e + k⟩ := by
  intro k; induction' k with k ih <;> intro b d e
  · exists 0
  · rw [show b + (k + 1) = (b + k) + 1 from by ring,
        show d + (k + 1) = (d + k) + 1 from by ring]
    step fm
    apply stepStar_trans (ih b d (e + 1))
    ring_nf; finish

-- R2+R1 interleaved: each pair does R2 then R1
theorem r2r1_chain : ∀ k a c d e, ⟨a + 1, 0, c + k, d, e⟩ [fm]⊢* ⟨a + k + 1, 0, c, d + 2 * k, e + k⟩ := by
  intro k; induction' k with k ih <;> intro a c d e
  · exists 0
  · rw [show c + (k + 1) = (c + k) + 1 from by ring,
        show a + 1 = (a + 0) + 1 from by ring]
    step fm
    rw [show (c + k) + 1 = c + k + 1 from by ring]
    step fm
    rw [show a + 0 + 2 = (a + 1) + 1 from by ring]
    apply stepStar_trans (ih (a + 1) c (d + 2) (e + 1))
    ring_nf; finish

-- Spiral: R1 then r2r1_chain
theorem spiral : ∀ c f, ⟨0, 0 + 1, c + 1, 0, f⟩ [fm]⊢* ⟨c + 2, 0, 0, 2 * c, f + c⟩ := by
  intro c f
  step fm
  rw [show (2 : ℕ) = 1 + 1 from by ring,
      show c = 0 + c from by ring]
  apply stepStar_trans (r2r1_chain c 1 0 0 f)
  ring_nf; finish

-- Remaining phases after R4+R5+spiral: R2 chain then R3 chain
theorem r2_r3_phase (D f : ℕ) :
    ⟨D + 2, 0, 0, 2 * D, f + D⟩ [fm]⊢* ⟨0, 0, 0, 3 * D + 2, 3 * D + f + 4⟩ := by
  have h1 := r2_chain (D + 2) 0 0 (2 * D) (f + D)
  rw [show (0 : ℕ) + (D + 2) = D + 2 from by ring] at h1
  apply stepStar_trans h1
  have h2 := r3_chain (D + 2) 0 (3 * D + 2) (f + 2 * D + 2)
  rw [show (0 : ℕ) + (D + 2) = D + 2 from by ring,
      show (3 * D + 2) + (D + 2) = 4 * D + 4 from by ring] at h2
  rw [show 2 * D + 2 * (D + 2) = 4 * D + 4 from by ring,
      show f + D + (D + 2) = f + 2 * D + 2 from by ring]
  apply stepStar_trans h2
  rw [show f + 2 * D + 2 + (D + 2) = 3 * D + f + 4 from by ring]
  finish

-- Full transition: (0,0,0,D+1,D+f+2) →⁺ (0,0,0,3D+2,3D+f+4)
theorem main_trans (D f : ℕ) :
    ⟨0, 0, 0, D + 1, D + f + 2⟩ [fm]⊢⁺ ⟨0, 0, 0, 3 * D + 2, 3 * D + f + 4⟩ := by
  -- First R4 step to get ⊢⁺
  rw [show D + 1 = (D + 0) + 1 from by ring,
      show D + f + 2 = (D + f + 1) + 1 from by ring]
  step fm
  -- Remaining R4 steps: (0, 0, 1, D, D+f+1) →* (0, 0, D+1, 0, f+1)
  have h_r4 : ⟨0, 0, 1, D, D + f + 1⟩ [fm]⊢* ⟨0, 0, D + 1, 0, (f + 1 : ℕ)⟩ := by
    have := r4_chain D 1 0 (f + 1)
    rw [show (1 : ℕ) + D = D + 1 from by ring,
        show (0 : ℕ) + D = D from by ring,
        show f + 1 + D = D + f + 1 from by ring] at this
    exact this
  apply stepStar_trans h_r4
  -- R5
  step fm
  -- Spiral
  apply stepStar_trans (spiral D f)
  -- R2 + R3
  exact r2_r3_phase D f

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨0, 0, 0, 1, 2⟩) (by execute fm 2)
  apply progress_nonhalt (fm := fm)
    (P := fun q ↦ ∃ D f, q = ⟨0, 0, 0, D + 1, D + f + 2⟩)
  · intro c ⟨D, f, hq⟩; subst hq
    exact ⟨⟨0, 0, 0, 3 * D + 2, 3 * D + f + 4⟩,
      ⟨3 * D + 1, f + 1, by ring_nf⟩, main_trans D f⟩
  · exact ⟨0, 0, by ring_nf⟩
