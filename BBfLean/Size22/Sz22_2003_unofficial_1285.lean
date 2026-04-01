import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #1285: [56/15, 9/7, 1/6, 25/2, 6/5]

Vector representation:
```
 3 -1 -1  1
 0  2  0 -1
-1 -1  0  0
-1  0  2  0
 1  1 -1  0
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_1285

def Q := ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a, b+1, c+1, d⟩ => some ⟨a+3, b, c, d+1⟩
  | ⟨a, b, c, d+1⟩ => some ⟨a, b+2, c, d⟩
  | ⟨a+1, b+1, c, d⟩ => some ⟨a, b, c, d⟩
  | ⟨a+1, b, c, d⟩ => some ⟨a, b, c+2, d⟩
  | ⟨a, b, c+1, d⟩ => some ⟨a+1, b+1, c, d⟩
  | _ => none

-- R4 chain: (a+k, 0, c, 0) →* (a, 0, c+2*k, 0)
theorem r4_chain : ∀ k, ⟨a + k, 0, c, 0⟩ [fm]⊢* ⟨a, 0, c + 2 * k, 0⟩ := by
  intro k; induction' k with k ih generalizing a c
  · exists 0
  · rw [show a + (k + 1) = (a + k) + 1 from by ring]
    step fm
    apply stepStar_trans (ih (a := a) (c := c + 2))
    ring_nf; finish

-- R2 chain: (a, b, 0, d+k) →* (a, b+2*k, 0, d)
theorem r2_chain : ∀ k, ⟨a, b, 0, d + k⟩ [fm]⊢* ⟨a, b + 2 * k, 0, d⟩ := by
  intro k; induction' k with k ih generalizing a b d
  · exists 0
  · rw [show d + (k + 1) = (d + k) + 1 from by ring]
    step fm
    apply stepStar_trans (ih (b := b + 2))
    ring_nf; finish

-- R3 drain: (a+k, k, 0, 0) →* (a, 0, 0, 0)
theorem r3_drain : ∀ k, ⟨a + k, k, 0, 0⟩ [fm]⊢* ⟨a, 0, 0, 0⟩ := by
  intro k; induction' k with k ih generalizing a
  · exists 0
  · rw [show a + (k + 1) = (a + k) + 1 from by ring]
    step fm
    exact ih

-- Interleaved R2-R1-R1 chain: (A, 0, 2*k, D+1) →* (A+6*k, 0, 0, D+1+k)
theorem interleaved : ∀ k, ⟨A, 0, 2 * k, D + 1⟩ [fm]⊢* ⟨A + 6 * k, 0, 0, D + 1 + k⟩ := by
  intro k; induction' k with k ih generalizing A D
  · exists 0
  · rw [show 2 * (k + 1) = (2 * k + 1) + 1 from by ring]
    step fm
    step fm
    step fm
    apply stepStar_trans (ih (A := A + 6) (D := D + 1))
    ring_nf; finish

-- R5+R1 opening: (0, 0, c+2, 0) →* (4, 0, c, 1)
theorem r5_r1 : ⟨0, 0, c + 2, 0⟩ [fm]⊢* ⟨4, 0, c, 1⟩ := by
  rw [show c + 2 = (c + 1) + 1 from by ring]
  step fm
  step fm
  finish

-- Full transition from (a+2, 0, 0, 0) ⊢⁺ (4*a+6, 0, 0, 0)
theorem main_trans : ⟨a + 2, 0, 0, 0⟩ [fm]⊢⁺ ⟨4 * a + 6, 0, 0, 0⟩ := by
  have h1 : ⟨a + 2, 0, 0, 0⟩ [fm]⊢* ⟨0, 0, 2 * a + 4, 0⟩ := by
    rw [show a + 2 = 0 + (a + 2) from by ring]
    apply stepStar_trans (r4_chain (a + 2) (a := 0) (c := 0))
    ring_nf; finish
  have h2 : ⟨0, 0, 2 * a + 4, 0⟩ [fm]⊢* ⟨4, 0, 2 * a + 2, 1⟩ := by
    rw [show 2 * a + 4 = (2 * a + 2) + 2 from by ring]
    exact r5_r1
  have h3 : ⟨4, 0, 2 * a + 2, 1⟩ [fm]⊢* ⟨6 * a + 10, 0, 0, a + 2⟩ := by
    rw [show 2 * a + 2 = 2 * (a + 1) from by ring,
        show (1 : ℕ) = 0 + 1 from by ring]
    apply stepStar_trans (interleaved (a + 1) (A := 4) (D := 0))
    ring_nf; finish
  have h4 : ⟨6 * a + 10, 0, 0, a + 2⟩ [fm]⊢* ⟨6 * a + 10, 2 * a + 4, 0, 0⟩ := by
    rw [show a + 2 = 0 + (a + 2) from by ring]
    apply stepStar_trans (r2_chain (a + 2) (a := 6 * a + 10) (b := 0) (d := 0))
    ring_nf; finish
  have h5 : ⟨6 * a + 10, 2 * a + 4, 0, 0⟩ [fm]⊢* ⟨4 * a + 6, 0, 0, 0⟩ := by
    rw [show 6 * a + 10 = (4 * a + 6) + (2 * a + 4) from by ring]
    exact r3_drain (2 * a + 4) (a := 4 * a + 6)
  have h12 : ⟨a + 2, 0, 0, 0⟩ [fm]⊢* ⟨4, 0, 2 * a + 2, 1⟩ :=
    stepStar_trans h1 h2
  have h345 : ⟨4, 0, 2 * a + 2, 1⟩ [fm]⊢* ⟨4 * a + 6, 0, 0, 0⟩ :=
    stepStar_trans h3 (stepStar_trans h4 h5)
  have hall : ⟨a + 2, 0, 0, 0⟩ [fm]⊢* ⟨4 * a + 6, 0, 0, 0⟩ :=
    stepStar_trans h12 h345
  exact stepStar_stepPlus hall (by intro h; have := congr_arg Prod.fst h; simp at this; omega)

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨2, 0, 0, 0⟩) (by execute fm 6)
  apply progress_nonhalt_simple (fm := fm) (A := ℕ)
    (fun a ↦ ⟨a + 2, 0, 0, 0⟩) 0
  intro a; exact ⟨4 * a + 4, main_trans⟩
