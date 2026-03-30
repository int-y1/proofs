import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #1033: [4/45, 55/14, 9/2, 7/11, 22/3]

Vector representation:
```
 2 -2 -1  0  0
-1  0  1 -1  1
-1  2  0  0  0
 0  0  0  1 -1
 1 -1  0  0  1
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_1033

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a, b+2, c+1, d, e⟩ => some ⟨a+2, b, c, d, e⟩
  | ⟨a+1, b, c, d+1, e⟩ => some ⟨a, b, c+1, d, e+1⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b+2, c, d, e⟩
  | ⟨a, b, c, d, e+1⟩ => some ⟨a, b, c, d+1, e⟩
  | ⟨a, b+1, c, d, e⟩ => some ⟨a+1, b, c, d, e+1⟩
  | _ => none

theorem e_to_d : ∀ k, ∀ b d,
    ⟨(0 : ℕ), b, 0, d, k⟩ [fm]⊢* ⟨0, b, 0, d + k, 0⟩ := by
  intro k; induction' k with k ih <;> intro b d
  · ring_nf; finish
  · rw [show d + (k + 1) = (d + 1) + k from by ring]
    step fm
    apply stepStar_trans (ih b (d + 1))
    ring_nf; finish

theorem r2r1_chain : ∀ k, ∀ A B D E,
    ⟨A + 1, B + 2 * k, (0 : ℕ), D + k, E⟩ [fm]⊢* ⟨A + k + 1, B, 0, D, E + k⟩ := by
  intro k; induction' k with k ih <;> intro A B D E
  · ring_nf; finish
  · rw [show B + 2 * (k + 1) = (B + 2 * k) + 2 from by ring,
        show D + (k + 1) = (D + k) + 1 from by ring]
    step fm; step fm
    apply stepStar_trans (ih (A + 1) B D (E + 1))
    ring_nf; finish

theorem r2_chain_b0 : ∀ k, ∀ A C D E,
    ⟨A + k, (0 : ℕ), C, D + k, E⟩ [fm]⊢* ⟨A, 0, C + k, D, E + k⟩ := by
  intro k; induction' k with k ih <;> intro A C D E
  · ring_nf; finish
  · rw [show A + (k + 1) = (A + k) + 1 from by ring,
        show D + (k + 1) = (D + k) + 1 from by ring,
        show C + (k + 1) = (C + 1) + k from by ring,
        show E + (k + 1) = (E + 1) + k from by ring]
    step fm
    apply stepStar_trans (ih A (C + 1) D (E + 1))
    ring_nf; finish

theorem r2_chain_b1 : ∀ k, ∀ A C D E,
    ⟨A + k, (1 : ℕ), C, D + k, E⟩ [fm]⊢* ⟨A, 1, C + k, D, E + k⟩ := by
  intro k; induction' k with k ih <;> intro A C D E
  · ring_nf; finish
  · rw [show A + (k + 1) = (A + k) + 1 from by ring,
        show D + (k + 1) = (D + k) + 1 from by ring,
        show C + (k + 1) = (C + 1) + k from by ring,
        show E + (k + 1) = (E + 1) + k from by ring]
    step fm
    apply stepStar_trans (ih A (C + 1) D (E + 1))
    ring_nf; finish

theorem r3r1_b1_chain : ∀ k, ∀ A E,
    ⟨A + 1, (1 : ℕ), k, (0 : ℕ), E⟩ [fm]⊢* ⟨A + k + 1, 1, 0, 0, E⟩ := by
  intro k; induction' k with k ih <;> intro A E
  · ring_nf; finish
  · rw [show A + (k + 1) + 1 = (A + 1) + k + 1 from by ring]
    step fm; step fm
    apply stepStar_trans (ih (A + 1) E)
    ring_nf; finish

theorem r3r1_b0_chain : ∀ k, ∀ A E,
    ⟨A + 2, (0 : ℕ), k, (0 : ℕ), E⟩ [fm]⊢* ⟨A + k + 2, 0, 0, 0, E⟩ := by
  intro k; induction' k with k ih <;> intro A E
  · ring_nf; finish
  · rw [show A + (k + 1) + 2 = (A + 1) + k + 2 from by ring]
    step fm; step fm
    apply stepStar_trans (ih (A + 1) E)
    ring_nf; finish

theorem r3_chain : ∀ k, ∀ b e,
    ⟨k, b, (0 : ℕ), (0 : ℕ), e⟩ [fm]⊢* ⟨0, b + 2 * k, 0, 0, e⟩ := by
  intro k; induction' k with k ih <;> intro b e
  · ring_nf; finish
  · rw [show b + 2 * (k + 1) = (b + 2) + 2 * k from by ring]
    step fm
    apply stepStar_trans (ih (b + 2) e)
    ring_nf; finish

theorem main_trans_even (p : ℕ) :
    ⟨(0 : ℕ), 2 * p + 2, 0, 0, 2 * p⟩ [fm]⊢⁺ ⟨0, 2 * p + 3, 0, 0, 2 * p + 1⟩ := by
  have h1 : ⟨(0 : ℕ), 2 * p + 2, 0, 0, 2 * p⟩ [fm]⊢*
      ⟨0, 2 * p + 2, 0, 2 * p, 0⟩ := by
    have := e_to_d (2 * p) (2 * p + 2) 0
    rw [show (0 : ℕ) + (2 * p) = 2 * p from by ring] at this
    exact this
  have h2 : ⟨(0 : ℕ), 2 * p + 2, 0, 2 * p, 0⟩ [fm]⊢⁺
      ⟨1, 2 * p + 1, 0, 2 * p, 1⟩ := by
    rw [show 2 * p + 2 = (2 * p + 1) + 1 from by ring]
    step fm; finish
  have h3 : ⟨(1 : ℕ), 2 * p + 1, 0, 2 * p, 1⟩ [fm]⊢*
      ⟨p + 1, 1, 0, p, p + 1⟩ := by
    have := r2r1_chain p 0 1 p 1
    rw [show (0 : ℕ) + 1 = 1 from by ring,
        show 1 + 2 * p = 2 * p + 1 from by ring,
        show p + p = 2 * p from by ring,
        show 0 + p + 1 = p + 1 from by ring,
        show 1 + p = p + 1 from by ring] at this
    exact this
  have h4 : ⟨p + 1, (1 : ℕ), 0, p, p + 1⟩ [fm]⊢*
      ⟨1, 1, p, 0, 2 * p + 1⟩ := by
    have := r2_chain_b1 p 1 0 0 (p + 1)
    rw [show 1 + p = p + 1 from by ring,
        show (0 : ℕ) + p = p from by ring,
        show p + 1 + p = 2 * p + 1 from by ring] at this
    exact this
  have h5 : ⟨(1 : ℕ), 1, p, 0, 2 * p + 1⟩ [fm]⊢*
      ⟨p + 1, 1, 0, 0, 2 * p + 1⟩ := by
    have := r3r1_b1_chain p 0 (2 * p + 1)
    rw [show (0 : ℕ) + 1 = 1 from by ring,
        show 0 + p + 1 = p + 1 from by ring] at this
    exact this
  have h6 : ⟨p + 1, (1 : ℕ), 0, 0, 2 * p + 1⟩ [fm]⊢*
      ⟨0, 2 * p + 3, 0, 0, 2 * p + 1⟩ := by
    have := r3_chain (p + 1) 1 (2 * p + 1)
    rw [show 1 + 2 * (p + 1) = 2 * p + 3 from by ring] at this
    exact this
  exact stepStar_stepPlus_stepPlus h1
    (stepPlus_stepStar_stepPlus h2
      (stepStar_trans h3
        (stepStar_trans h4
          (stepStar_trans h5 h6))))

theorem main_trans_odd (p : ℕ) :
    ⟨(0 : ℕ), 2 * p + 3, 0, 0, 2 * p + 1⟩ [fm]⊢⁺ ⟨0, 2 * p + 4, 0, 0, 2 * p + 2⟩ := by
  have h1 : ⟨(0 : ℕ), 2 * p + 3, 0, 0, 2 * p + 1⟩ [fm]⊢*
      ⟨0, 2 * p + 3, 0, 2 * p + 1, 0⟩ := by
    have := e_to_d (2 * p + 1) (2 * p + 3) 0
    rw [show (0 : ℕ) + (2 * p + 1) = 2 * p + 1 from by ring] at this
    exact this
  have h2 : ⟨(0 : ℕ), 2 * p + 3, 0, 2 * p + 1, 0⟩ [fm]⊢⁺
      ⟨1, 2 * p + 2, 0, 2 * p + 1, 1⟩ := by
    rw [show 2 * p + 3 = (2 * p + 2) + 1 from by ring]
    step fm; finish
  have h3 : ⟨(1 : ℕ), 2 * p + 2, 0, 2 * p + 1, 1⟩ [fm]⊢*
      ⟨p + 2, 0, 0, p, p + 2⟩ := by
    have := r2r1_chain (p + 1) 0 0 p 1
    rw [show (0 : ℕ) + 1 = 1 from by ring,
        show 0 + 2 * (p + 1) = 2 * p + 2 from by ring,
        show p + (p + 1) = 2 * p + 1 from by ring,
        show 0 + (p + 1) + 1 = p + 2 from by ring,
        show 1 + (p + 1) = p + 2 from by ring] at this
    exact this
  have h4 : ⟨p + 2, (0 : ℕ), 0, p, p + 2⟩ [fm]⊢*
      ⟨2, 0, p, 0, 2 * p + 2⟩ := by
    have := r2_chain_b0 p 2 0 0 (p + 2)
    rw [show 2 + p = p + 2 from by ring,
        show (0 : ℕ) + p = p from by ring,
        show p + 2 + p = 2 * p + 2 from by ring] at this
    exact this
  have h5 : ⟨(2 : ℕ), 0, p, 0, 2 * p + 2⟩ [fm]⊢*
      ⟨p + 2, 0, 0, 0, 2 * p + 2⟩ := by
    have := r3r1_b0_chain p 0 (2 * p + 2)
    rw [show (0 : ℕ) + 2 = 2 from by ring,
        show 0 + p + 2 = p + 2 from by ring] at this
    exact this
  have h6 : ⟨p + 2, (0 : ℕ), 0, 0, 2 * p + 2⟩ [fm]⊢*
      ⟨0, 2 * p + 4, 0, 0, 2 * p + 2⟩ := by
    have := r3_chain (p + 2) 0 (2 * p + 2)
    rw [show 0 + 2 * (p + 2) = 2 * p + 4 from by ring] at this
    exact this
  exact stepStar_stepPlus_stepPlus h1
    (stepPlus_stepStar_stepPlus h2
      (stepStar_trans h3
        (stepStar_trans h4
          (stepStar_trans h5 h6))))

theorem main_trans (n : ℕ) :
    ⟨(0 : ℕ), n + 2, 0, 0, n⟩ [fm]⊢⁺ ⟨0, n + 3, 0, 0, n + 1⟩ := by
  rcases Nat.even_or_odd n with ⟨p, hp⟩ | ⟨p, hp⟩
  · have := main_trans_even p
    rw [show n = 2 * p from by omega] at *
    exact this
  · have := main_trans_odd p
    rw [show n = 2 * p + 1 from by omega] at *
    exact this

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨0, 2, 0, 0, 0⟩) (by execute fm 1)
  apply progress_nonhalt_simple (fm := fm) (A := ℕ)
    (fun n ↦ ⟨0, n + 2, 0, 0, n⟩) 0
  intro n
  exact ⟨n + 1, main_trans n⟩
