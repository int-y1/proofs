import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #1597: [77/15, 13/3, 18/91, 5/11, 231/2]

Vector representation:
```
 0 -1 -1  1  1  0
 0 -1  0  0  0  1
 1  2  0 -1  0 -1
 0  0  1  0 -1  0
-1  1  0  1  1  0
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_1597

def Q := ℕ × ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a, b+1, c+1, d, e, f⟩ => some ⟨a, b, c, d+1, e+1, f⟩
  | ⟨a, b+1, c, d, e, f⟩ => some ⟨a, b, c, d, e, f+1⟩
  | ⟨a, b, c, d+1, e, f+1⟩ => some ⟨a+1, b+2, c, d, e, f⟩
  | ⟨a, b, c, d, e+1, f⟩ => some ⟨a, b, c+1, d, e, f⟩
  | ⟨a+1, b, c, d, e, f⟩ => some ⟨a, b+1, c, d+1, e+1, f⟩
  | _ => none

-- R4 chain: transfer e to c.
theorem r4_chain : ∀ k, ∀ a c e f, ⟨a, 0, c, 0, e + k, f⟩ [fm]⊢* ⟨a, 0, c + k, 0, e, f⟩ := by
  intro k; induction' k with k ih <;> intro a c e f
  · exists 0
  · rw [show e + (k + 1) = (e + k) + 1 from by ring]
    step fm
    apply stepStar_trans (ih a (c + 1) e f)
    ring_nf; finish

-- R3R1R1 chain: k rounds. Each round uses 2 from c, adds 1 to d, adds 2 to e, removes 1 from f.
theorem r311_chain : ∀ k, ∀ a c d e f,
    ⟨a, 0, c + 2 * k, d + 1, e, f + k⟩ [fm]⊢* ⟨a + k, 0, c, d + 1 + k, e + 2 * k, f⟩ := by
  intro k; induction' k with k ih <;> intro a c d e f
  · exists 0
  · rw [show c + 2 * (k + 1) = (c + 2 * k) + 1 + 1 from by ring,
        show f + (k + 1) = (f + k) + 1 from by ring]
    step fm; step fm; step fm
    rw [show d + 1 + 1 = (d + 1) + 1 from by ring]
    apply stepStar_trans (ih (a + 1) c (d + 1) (e + 2) f)
    ring_nf; finish

-- R3R1R2 step: handles the remaining c = 1 case.
theorem r31r2_step : ∀ a d e f,
    ⟨a, 0, 1, d + 1, e, f + 1⟩ [fm]⊢* ⟨a + 1, 0, 0, d + 1, e + 1, f + 1⟩ := by
  intro a d e f
  step fm; step fm; step fm; finish

-- R3R2R2 chain: k rounds. Each round adds 1 to a, removes 1 from d, adds 1 to f.
theorem r322_chain : ∀ k, ∀ a e f,
    ⟨a, 0, 0, k, e, f + k⟩ [fm]⊢* ⟨a + k, 0, 0, 0, e, f + 2 * k⟩ := by
  intro k; induction' k with k ih <;> intro a e f
  · exists 0
  · rw [show (k + 1 : ℕ) = k + 1 from rfl,
        show f + (k + 1) = (f + k) + 1 from by ring]
    step fm; step fm; step fm
    rw [show f + k + 2 = (f + 2) + k from by ring]
    apply stepStar_trans (ih (a + 1) e (f + 2))
    ring_nf; finish

-- Main transition for even n = 2m.
-- Canonical: (a+1, 0, 0, 0, 2m+1, 4m+2) ⊢⁺ (a+2m+2, 0, 0, 0, 2m+2, 4m+4)
theorem main_trans_even : ∀ m, ∀ a,
    ⟨a + 1, 0, 0, 0, 2 * m + 1, 4 * m + 2⟩ [fm]⊢⁺
    ⟨a + 2 * m + 2, 0, 0, 0, 2 * m + 2, 4 * m + 4⟩ := by
  intro m a
  -- R4 x (2m+1)
  have h1 : ⟨a + 1, 0, 0, 0, 2 * m + 1, 4 * m + 2⟩ [fm]⊢*
      ⟨a + 1, 0, 2 * m + 1, 0, 0, 4 * m + 2⟩ := by
    have := r4_chain (2 * m + 1) (a + 1) 0 0 (4 * m + 2)
    simp only [Nat.zero_add] at this; exact this
  -- R5
  have h2 : ⟨a + 1, 0, 2 * m + 1, 0, 0, 4 * m + 2⟩ [fm]⊢⁺
      ⟨a, 1, 2 * m + 1, 1, 1, 4 * m + 2⟩ := by
    step fm; finish
  -- R1
  have h3 : ⟨a, 1, 2 * m + 1, 1, 1, 4 * m + 2⟩ [fm]⊢*
      ⟨a, 0, 2 * m, 2, 2, 4 * m + 2⟩ := by
    rw [show 2 * m + 1 = (2 * m) + 1 from by ring]
    step fm; finish
  -- R3R1R1 x m
  have h4 : ⟨a, 0, 2 * m, 2, 2, 4 * m + 2⟩ [fm]⊢*
      ⟨a + m, 0, 0, m + 2, 2 * m + 2, 3 * m + 2⟩ := by
    rw [show 2 * m = 0 + 2 * m from by ring,
        show (2 : ℕ) = 1 + 1 from by ring,
        show 4 * m + 2 = (3 * m + 2) + m from by ring]
    have := r311_chain m a 0 1 2 (3 * m + 2)
    apply stepStar_trans this; ring_nf; finish
  -- R3R2R2 x (m+2)
  have h5 : ⟨a + m, 0, 0, m + 2, 2 * m + 2, 3 * m + 2⟩ [fm]⊢*
      ⟨a + 2 * m + 2, 0, 0, 0, 2 * m + 2, 4 * m + 4⟩ := by
    rw [show 3 * m + 2 = (2 * m) + (m + 2) from by ring]
    have := r322_chain (m + 2) (a + m) (2 * m + 2) (2 * m)
    apply stepStar_trans this; ring_nf; finish
  apply stepStar_stepPlus_stepPlus h1
  exact stepPlus_stepStar_stepPlus h2 (stepStar_trans h3 (stepStar_trans h4 h5))

-- Main transition for odd n = 2m+1.
-- Canonical: (a+1, 0, 0, 0, 2m+2, 4m+4) ⊢⁺ (a+2m+3, 0, 0, 0, 2m+3, 4m+6)
theorem main_trans_odd : ∀ m, ∀ a,
    ⟨a + 1, 0, 0, 0, 2 * m + 2, 4 * m + 4⟩ [fm]⊢⁺
    ⟨a + 2 * m + 3, 0, 0, 0, 2 * m + 3, 4 * m + 6⟩ := by
  intro m a
  -- R4 x (2m+2)
  have h1 : ⟨a + 1, 0, 0, 0, 2 * m + 2, 4 * m + 4⟩ [fm]⊢*
      ⟨a + 1, 0, 2 * m + 2, 0, 0, 4 * m + 4⟩ := by
    have := r4_chain (2 * m + 2) (a + 1) 0 0 (4 * m + 4)
    simp only [Nat.zero_add] at this; exact this
  -- R5
  have h2 : ⟨a + 1, 0, 2 * m + 2, 0, 0, 4 * m + 4⟩ [fm]⊢⁺
      ⟨a, 1, 2 * m + 2, 1, 1, 4 * m + 4⟩ := by
    step fm; finish
  -- R1
  have h3 : ⟨a, 1, 2 * m + 2, 1, 1, 4 * m + 4⟩ [fm]⊢*
      ⟨a, 0, 2 * m + 1, 2, 2, 4 * m + 4⟩ := by
    rw [show 2 * m + 2 = (2 * m + 1) + 1 from by ring]
    step fm; finish
  -- R3R1R1 x m
  have h4 : ⟨a, 0, 2 * m + 1, 2, 2, 4 * m + 4⟩ [fm]⊢*
      ⟨a + m, 0, 1, m + 2, 2 * m + 2, 3 * m + 4⟩ := by
    rw [show 2 * m + 1 = 1 + 2 * m from by ring,
        show (2 : ℕ) = 1 + 1 from by ring,
        show 4 * m + 4 = (3 * m + 4) + m from by ring]
    have := r311_chain m a 1 1 2 (3 * m + 4)
    apply stepStar_trans this; ring_nf; finish
  -- R3R1R2
  have h5 : ⟨a + m, 0, 1, m + 2, 2 * m + 2, 3 * m + 4⟩ [fm]⊢*
      ⟨a + m + 1, 0, 0, m + 2, 2 * m + 3, 3 * m + 4⟩ := by
    rw [show m + 2 = (m + 1) + 1 from by ring,
        show 3 * m + 4 = (3 * m + 3) + 1 from by ring]
    have := r31r2_step (a + m) (m + 1) (2 * m + 2) (3 * m + 3)
    apply stepStar_trans this; ring_nf; finish
  -- R3R2R2 x (m+2)
  have h6 : ⟨a + m + 1, 0, 0, m + 2, 2 * m + 3, 3 * m + 4⟩ [fm]⊢*
      ⟨a + 2 * m + 3, 0, 0, 0, 2 * m + 3, 4 * m + 6⟩ := by
    rw [show 3 * m + 4 = (2 * m + 2) + (m + 2) from by ring]
    have := r322_chain (m + 2) (a + m + 1) (2 * m + 3) (2 * m + 2)
    apply stepStar_trans this; ring_nf; finish
  apply stepStar_stepPlus_stepPlus h1
  exact stepPlus_stepStar_stepPlus h2 (stepStar_trans h3 (stepStar_trans h4 (stepStar_trans h5 h6)))

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨1, 0, 0, 0, 1, 2⟩) (by execute fm 5)
  apply progress_nonhalt_simple (fm := fm) (A := ℕ × ℕ)
    (fun ⟨a, n⟩ ↦ ⟨a + 1, 0, 0, 0, n + 1, 2 * n + 2⟩) ⟨0, 0⟩
  intro ⟨a, n⟩
  rcases Nat.even_or_odd n with ⟨m, hm⟩ | ⟨m, hm⟩
  · -- n = 2*m (even case)
    subst hm
    refine ⟨⟨a + 2 * m + 1, 2 * m + 1⟩, ?_⟩
    simp only [Q]
    rw [show 2 * (m + m) + 2 = 4 * m + 2 from by ring,
        show (m + m) + 1 = 2 * m + 1 from by ring,
        show 2 * (2 * m + 1) + 2 = 4 * m + 4 from by ring,
        show a + 2 * m + 1 + 1 = a + 2 * m + 2 from by ring]
    exact main_trans_even m a
  · -- n = 2*m+1 (odd case)
    subst hm
    refine ⟨⟨a + 2 * m + 2, 2 * m + 2⟩, ?_⟩
    simp only [Q]
    rw [show 2 * (2 * m + 1) + 2 = 4 * m + 4 from by ring,
        show (2 * m + 1) + 1 = 2 * m + 2 from by ring,
        show 2 * (2 * m + 2) + 2 = 4 * m + 6 from by ring,
        show a + 2 * m + 2 + 1 = a + 2 * m + 3 from by ring]
    exact main_trans_odd m a
