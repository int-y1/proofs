import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #860: [385/6, 65/2, 4/91, 3/11, 21/5]

Vector representation:
```
-1 -1  1  1  1  0
-1  0  1  0  0  1
 2  0  0 -1  0 -1
 0  1  0  0 -1  0
 0  1 -1  1  0  0
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_860

def Q := ℕ × ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a+1, b+1, c, d, e, f⟩ => some ⟨a, b, c+1, d+1, e+1, f⟩
  | ⟨a+1, b, c, d, e, f⟩ => some ⟨a, b, c+1, d, e, f+1⟩
  | ⟨a, b, c, d+1, e, f+1⟩ => some ⟨a+2, b, c, d, e, f⟩
  | ⟨a, b, c, d, e+1, f⟩ => some ⟨a, b+1, c, d, e, f⟩
  | ⟨a, b, c+1, d, e, f⟩ => some ⟨a, b+1, c, d+1, e, f⟩
  | _ => none

-- R4 repeated: move e to b.
theorem e_to_b : ∀ k b e, ⟨(0 : ℕ), b, c, 0, e + k, f⟩ [fm]⊢* ⟨0, b + k, c, 0, e, f⟩ := by
  intro k; induction' k with k ih <;> intro b e
  · exists 0
  · rw [show e + (k + 1) = (e + k) + 1 from by ring]
    step fm
    apply stepStar_trans (ih (b + 1) e)
    ring_nf; finish

-- R3+R2+R2 drain.
theorem r3r2r2_drain : ∀ k c d e f, ⟨(0 : ℕ), 0, c, d + k, e, f + 1⟩ [fm]⊢* ⟨0, 0, c + 2 * k, d, e, f + 1 + k⟩ := by
  intro k; induction' k with k ih <;> intro c d e f
  · exists 0
  · rw [show d + (k + 1) = (d + k) + 1 from by ring]
    step fm; step fm; step fm
    apply stepStar_trans (ih (c + 2) d e (f + 1))
    ring_nf; finish

-- Spiral full rounds (R3+R1+R1 repeated).
theorem spiral_rounds : ∀ k b c d e, ⟨(0 : ℕ), b + 2 * k, c, d + 1, e, f + k⟩ [fm]⊢* ⟨0, b, c + 2 * k, d + 1 + k, e + 2 * k, f⟩ := by
  intro k; induction' k with k ih <;> intro b c d e
  · exists 0
  · rw [show b + 2 * (k + 1) = (b + 2 * k) + 2 from by ring,
        show f + (k + 1) = (f + k) + 1 from by ring]
    step fm; step fm; step fm
    apply stepStar_trans (ih b (c + 2) (d + 1) (e + 2))
    ring_nf; finish

-- Partial round: R3+R1+R2.
theorem spiral_partial : ⟨(0 : ℕ), 1, c, d + 1, e, f + 1⟩ [fm]⊢* ⟨0, 0, c + 2, d + 1, e + 1, f + 1⟩ := by
  step fm; step fm; step fm; ring_nf; finish

-- Opening: R5 + R3 + R1 + R1, producing ⊢⁺.
theorem opening_plus : ⟨(0 : ℕ), n + 1, C + 1, 0, 0, n + 2⟩ [fm]⊢⁺ ⟨0, n, C + 2, 2, 2, n + 1⟩ := by
  step fm; step fm; step fm; step fm; ring_nf; finish

-- Even-case combined spiral+drain.
theorem even_spiral_drain (m c : ℕ) :
    ⟨(0 : ℕ), 2*m, c, 2, 2, 2*m + 1⟩ [fm]⊢* ⟨0, 0, c + 4*m + 4, 0, 2*m + 2, 2*m + 3⟩ := by
  have h1 : ⟨(0 : ℕ), 2*m, c, 2, 2, 2*m + 1⟩ [fm]⊢* ⟨0, 0, c + 2*m, m + 2, 2*m + 2, m + 1⟩ := by
    have := spiral_rounds (f := m + 1) m 0 c 1 2
    rw [show 0 + 2 * m = 2 * m from by omega,
        show (1 : ℕ) + 1 = 2 from by omega,
        show m + 1 + m = 2 * m + 1 from by omega,
        show 1 + 1 + m = m + 2 from by omega,
        show 2 + 2 * m = 2 * m + 2 from by omega] at this
    exact this
  have h2 : ⟨(0 : ℕ), 0, c + 2*m, m + 2, 2*m + 2, m + 1⟩ [fm]⊢* ⟨0, 0, c + 4*m + 4, 0, 2*m + 2, 2*m + 3⟩ := by
    have := r3r2r2_drain (m+2) (c + 2*m) 0 (2*m+2) m
    rw [show 0 + (m + 2) = m + 2 from by omega,
        show c + 2 * m + 2 * (m + 2) = c + 4 * m + 4 from by omega,
        show m + 0 + 1 = m + 1 from by omega,
        show m + 0 + 1 + (m + 2) = 2 * m + 3 from by omega] at this
    exact this
  exact stepStar_trans h1 h2

-- Odd-case combined spiral+partial+drain.
theorem odd_spiral_drain (m c : ℕ) :
    ⟨(0 : ℕ), 2*m + 1, c, 2, 2, 2*m + 2⟩ [fm]⊢* ⟨0, 0, c + 4*m + 6, 0, 2*m + 3, 2*m + 4⟩ := by
  have h1 : ⟨(0 : ℕ), 2*m + 1, c, 2, 2, 2*m + 2⟩ [fm]⊢* ⟨0, 1, c + 2*m, m + 2, 2*m + 2, m + 2⟩ := by
    have := spiral_rounds (f := m + 2) m 1 c 1 2
    rw [show 1 + 2 * m = 2 * m + 1 from by omega,
        show (1 : ℕ) + 1 = 2 from by omega,
        show m + 2 + m = 2 * m + 2 from by omega,
        show 1 + 1 + m = m + 2 from by omega,
        show 2 + 2 * m = 2 * m + 2 from by omega] at this
    exact this
  have h2 : ⟨(0 : ℕ), 1, c + 2*m, m + 2, 2*m + 2, m + 2⟩ [fm]⊢* ⟨0, 0, c + 2*m + 2, m + 2, 2*m + 3, m + 2⟩ := by
    have := spiral_partial (c := c + 2*m) (d := m + 1) (e := 2*m + 2) (f := m + 1)
    rw [show m + 1 + 1 = m + 2 from by omega,
        show 2 * m + 2 + 1 = 2 * m + 3 from by omega] at this
    exact this
  have h3 : ⟨(0 : ℕ), 0, c + 2*m + 2, m + 2, 2*m + 3, m + 2⟩ [fm]⊢* ⟨0, 0, c + 4*m + 6, 0, 2*m + 3, 2*m + 4⟩ := by
    have := r3r2r2_drain (m + 2) (c + 2*m + 2) 0 (2*m + 3) (m + 1)
    rw [show 0 + (m + 2) = m + 2 from by omega,
        show c + 2 * m + 2 + 2 * (m + 2) = c + 4 * m + 6 from by omega,
        show m + 1 + 0 + 1 = m + 2 from by omega,
        show m + 1 + 0 + 1 + (m + 2) = 2 * m + 4 from by omega] at this
    exact this
  exact stepStar_trans h1 (stepStar_trans h2 h3)

-- Even transition.
theorem transition_even (m : ℕ) :
    ⟨(0 : ℕ), 0, 4*m*m + 8*m + 4, 0, 2*m + 1, 2*m + 2⟩ [fm]⊢⁺
    ⟨0, 0, 4*m*m + 12*m + 9, 0, 2*m + 2, 2*m + 3⟩ := by
  have h1 : ⟨(0 : ℕ), 0, 4*m*m + 8*m + 4, 0, 2*m + 1, 2*m + 2⟩ [fm]⊢*
             ⟨0, 2*m + 1, 4*m*m + 8*m + 4, 0, 0, 2*m + 2⟩ := by
    have := e_to_b (c := 4*m*m + 8*m + 4) (f := 2*m + 2) (2*m + 1) 0 0
    simp only [Nat.zero_add] at this; exact this
  have h2 : ⟨(0 : ℕ), 2*m + 1, 4*m*m + 8*m + 4, 0, 0, 2*m + 2⟩ [fm]⊢⁺
             ⟨0, 2*m, 4*m*m + 8*m + 5, 2, 2, 2*m + 1⟩ := by
    have := opening_plus (n := 2*m) (C := 4*m*m + 8*m + 3)
    rw [show 4 * m * m + 8 * m + 3 + 1 = 4 * m * m + 8 * m + 4 from by omega,
        show 4 * m * m + 8 * m + 3 + 2 = 4 * m * m + 8 * m + 5 from by omega] at this
    exact this
  have h3 : ⟨(0 : ℕ), 2*m, 4*m*m + 8*m + 5, 2, 2, 2*m + 1⟩ [fm]⊢*
             ⟨0, 0, 4*m*m + 12*m + 9, 0, 2*m + 2, 2*m + 3⟩ := by
    have := even_spiral_drain m (4*m*m + 8*m + 5)
    rw [show 4 * m * m + 8 * m + 5 + 4 * m + 4 = 4 * m * m + 12 * m + 9 from by omega] at this
    exact this
  exact stepStar_stepPlus_stepPlus h1 (stepPlus_stepStar_stepPlus h2 h3)

-- Odd transition.
theorem transition_odd (m : ℕ) :
    ⟨(0 : ℕ), 0, 4*m*m + 12*m + 9, 0, 2*m + 2, 2*m + 3⟩ [fm]⊢⁺
    ⟨0, 0, 4*m*m + 16*m + 16, 0, 2*m + 3, 2*m + 4⟩ := by
  have h1 : ⟨(0 : ℕ), 0, 4*m*m + 12*m + 9, 0, 2*m + 2, 2*m + 3⟩ [fm]⊢*
             ⟨0, 2*m + 2, 4*m*m + 12*m + 9, 0, 0, 2*m + 3⟩ := by
    have := e_to_b (c := 4*m*m + 12*m + 9) (f := 2*m + 3) (2*m + 2) 0 0
    simp only [Nat.zero_add] at this; exact this
  have h2 : ⟨(0 : ℕ), 2*m + 2, 4*m*m + 12*m + 9, 0, 0, 2*m + 3⟩ [fm]⊢⁺
             ⟨0, 2*m + 1, 4*m*m + 12*m + 10, 2, 2, 2*m + 2⟩ := by
    have := opening_plus (n := 2*m + 1) (C := 4*m*m + 12*m + 8)
    rw [show 2 * m + 1 + 1 = 2 * m + 2 from by omega,
        show 4 * m * m + 12 * m + 8 + 1 = 4 * m * m + 12 * m + 9 from by omega,
        show 2 * m + 1 + 2 = 2 * m + 3 from by omega,
        show 4 * m * m + 12 * m + 8 + 2 = 4 * m * m + 12 * m + 10 from by omega] at this
    exact this
  have h3 : ⟨(0 : ℕ), 2*m + 1, 4*m*m + 12*m + 10, 2, 2, 2*m + 2⟩ [fm]⊢*
             ⟨0, 0, 4*m*m + 16*m + 16, 0, 2*m + 3, 2*m + 4⟩ := by
    have := odd_spiral_drain m (4*m*m + 12*m + 10)
    rw [show 4 * m * m + 12 * m + 10 + 4 * m + 6 = 4 * m * m + 16 * m + 16 from by omega] at this
    exact this
  exact stepStar_stepPlus_stepPlus h1 (stepPlus_stepStar_stepPlus h2 h3)

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨0, 0, 4, 0, 1, 2⟩)
  · execute fm 8
  apply progress_nonhalt_simple (fm := fm) (A := ℕ)
    (fun n ↦ ⟨0, 0, 4*n*n + 8*n + 4, 0, 2*n + 1, 2*n + 2⟩) 0
  intro n
  exists n + 1
  rw [show 4*(n+1)*(n+1) + 8*(n+1) + 4 = 4*n*n + 16*n + 16 from by ring,
      show 2*(n+1) + 1 = 2*n + 3 from by ring,
      show 2*(n+1) + 2 = 2*n + 4 from by ring]
  exact stepPlus_trans (transition_even n) (transition_odd n)

end Sz22_2003_unofficial_860
