import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #735: [35/6, 4/55, 143/2, 3/7, 66/13]

Vector representation:
```
-1 -1  1  1  0  0
 2  0 -1  0 -1  0
-1  0  0  0  1  1
 0  1  0 -1  0  0
 1  1  0  0  1 -1
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_735

def Q := ℕ × ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a+1, b+1, c, d, e, f⟩ => some ⟨a, b, c+1, d+1, e, f⟩
  | ⟨a, b, c+1, d, e+1, f⟩ => some ⟨a+2, b, c, d, e, f⟩
  | ⟨a+1, b, c, d, e, f⟩ => some ⟨a, b, c, d, e+1, f+1⟩
  | ⟨a, b, c, d+1, e, f⟩ => some ⟨a, b+1, c, d, e, f⟩
  | ⟨a, b, c, d, e, f+1⟩ => some ⟨a+1, b+1, c, d, e+1, f⟩
  | _ => none

theorem r2r1r1_chain : ∀ k, ∀ b c d e f,
    ⟨0, b + 2 * k, c + 1, d, e + k, f⟩ [fm]⊢*
    ⟨0, b, c + k + 1, d + 2 * k, e, f⟩ := by
  intro k; induction' k with k ih <;> intro b c d e f
  · exists 0
  · rw [show b + 2 * (k + 1) = (b + 2 * k) + 2 from by ring,
        show e + (k + 1) = (e + k) + 1 from by ring]
    step fm; step fm; step fm
    apply stepStar_trans (ih b (c + 1) (d + 2) e f)
    ring_nf; finish

theorem r2_chain : ∀ k, ∀ a d e f,
    ⟨a, 0, k, d, e + k, f⟩ [fm]⊢*
    ⟨a + 2 * k, 0, 0, d, e, f⟩ := by
  intro k; induction' k with k ih <;> intro a d e f
  · exists 0
  · rw [show (k + 1 : ℕ) = k + 1 from rfl,
        show e + (k + 1) = (e + k) + 1 from by ring]
    step fm
    apply stepStar_trans (ih (a + 2) d e f)
    ring_nf; finish

theorem r3_chain : ∀ k, ∀ d e f,
    ⟨k, 0, 0, d, e, f⟩ [fm]⊢*
    ⟨0, 0, 0, d, e + k, f + k⟩ := by
  intro k; induction' k with k ih <;> intro d e f
  · exists 0
  · rw [show (k + 1 : ℕ) = k + 1 from rfl]
    step fm
    apply stepStar_trans (ih d (e + 1) (f + 1))
    ring_nf; finish

theorem r4_chain : ∀ k, ∀ b e f,
    ⟨0, b, 0, k, e, f⟩ [fm]⊢*
    ⟨0, b + k, 0, 0, e, f⟩ := by
  intro k; induction' k with k ih <;> intro b e f
  · exists 0
  · rw [show (k + 1 : ℕ) = k + 1 from rfl]
    step fm
    apply stepStar_trans (ih (b + 1) e f)
    ring_nf; finish

theorem phase_even (m f : ℕ) :
    ⟨0, 2 * m, 1, 1, 4 * m + 2, f⟩ [fm]⊢*
    ⟨0, 2 * m + 1, 0, 0, 4 * m + 3, f + 2 * m + 2⟩ := by
  -- r2r1r1_chain m rounds: (0, 2m, 1, 1, 4m+2, f) ⊢* (0, 0, m+1, 2m+1, 3m+2, f)
  have h1 : ⟨0, 2 * m, 1, 1, 4 * m + 2, f⟩ [fm]⊢* ⟨0, 0, m + 1, 2 * m + 1, 3 * m + 2, f⟩ := by
    have := r2r1r1_chain m 0 0 1 (3 * m + 2) f
    rw [show 0 + 2 * m = 2 * m from by ring,
        show 0 + 1 = 1 from by ring,
        show 3 * m + 2 + m = 4 * m + 2 from by ring,
        show 0 + m + 1 = m + 1 from by ring,
        show 1 + 2 * m = 2 * m + 1 from by ring] at this
    exact this
  -- r2_chain (m+1): (0, 0, m+1, 2m+1, 3m+2, f) ⊢* (2m+2, 0, 0, 2m+1, 2m+1, f)
  have h2 : ⟨0, 0, m + 1, 2 * m + 1, 3 * m + 2, f⟩ [fm]⊢* ⟨2 * m + 2, 0, 0, 2 * m + 1, 2 * m + 1, f⟩ := by
    have := r2_chain (m + 1) 0 (2 * m + 1) (2 * m + 1) f
    rw [show 2 * m + 1 + (m + 1) = 3 * m + 2 from by ring,
        show 0 + 2 * (m + 1) = 2 * m + 2 from by ring] at this
    exact this
  -- r3_chain (2m+2): (2m+2, 0, 0, 2m+1, 2m+1, f) ⊢* (0, 0, 0, 2m+1, 4m+3, f+2m+2)
  have h3 : ⟨2 * m + 2, 0, 0, 2 * m + 1, 2 * m + 1, f⟩ [fm]⊢* ⟨0, 0, 0, 2 * m + 1, 4 * m + 3, f + 2 * m + 2⟩ := by
    have := r3_chain (2 * m + 2) (2 * m + 1) (2 * m + 1) f
    rw [show 2 * m + 1 + (2 * m + 2) = 4 * m + 3 from by ring,
        show f + (2 * m + 2) = f + 2 * m + 2 from by ring] at this
    exact this
  -- r4_chain (2m+1): (0, 0, 0, 2m+1, 4m+3, f+2m+2) ⊢* (0, 2m+1, 0, 0, 4m+3, f+2m+2)
  have h4 : ⟨0, 0, 0, 2 * m + 1, 4 * m + 3, f + 2 * m + 2⟩ [fm]⊢* ⟨0, 2 * m + 1, 0, 0, 4 * m + 3, f + 2 * m + 2⟩ := by
    have := r4_chain (2 * m + 1) 0 (4 * m + 3) (f + 2 * m + 2)
    rw [show 0 + (2 * m + 1) = 2 * m + 1 from by ring] at this
    exact this
  exact stepStar_trans h1 (stepStar_trans h2 (stepStar_trans h3 h4))

theorem phase_odd (m f : ℕ) :
    ⟨0, 2 * m + 1, 1, 1, 4 * m + 4, f⟩ [fm]⊢*
    ⟨0, 2 * m + 2, 0, 0, 4 * m + 5, f + 2 * m + 3⟩ := by
  -- r2r1r1_chain m rounds: (0, 2m+1, 1, 1, 4m+4, f) ⊢* (0, 1, m+1, 2m+1, 3m+4, f)
  have h1 : ⟨0, 2 * m + 1, 1, 1, 4 * m + 4, f⟩ [fm]⊢* ⟨0, 1, m + 1, 2 * m + 1, 3 * m + 4, f⟩ := by
    have := r2r1r1_chain m 1 0 1 (3 * m + 4) f
    rw [show 1 + 2 * m = 2 * m + 1 from by ring,
        show 0 + 1 = 1 from by ring,
        show 3 * m + 4 + m = 4 * m + 4 from by ring,
        show 0 + m + 1 = m + 1 from by ring] at this
    exact this
  -- R2 + R1: (0, 1, m+1, 2m+1, 3m+4, f) -> (2, 1, m, 2m+1, 3m+3, f) -> (1, 0, m+1, 2m+2, 3m+3, f)
  have h2 : ⟨0, 1, m + 1, 2 * m + 1, 3 * m + 4, f⟩ [fm]⊢* ⟨1, 0, m + 1, 2 * m + 2, 3 * m + 3, f⟩ := by
    rw [show m + 1 = m + 1 from rfl,
        show 3 * m + 4 = (3 * m + 3) + 1 from by ring]
    step fm; step fm
    rw [show 2 * m + 1 + 1 = 2 * m + 2 from by ring]
    finish
  -- r2_chain (m+1): (1, 0, m+1, 2m+2, 3m+3, f) ⊢* (2m+3, 0, 0, 2m+2, 2m+2, f)
  have h3 : ⟨1, 0, m + 1, 2 * m + 2, 3 * m + 3, f⟩ [fm]⊢* ⟨2 * m + 3, 0, 0, 2 * m + 2, 2 * m + 2, f⟩ := by
    have := r2_chain (m + 1) 1 (2 * m + 2) (2 * m + 2) f
    rw [show 2 * m + 2 + (m + 1) = 3 * m + 3 from by ring,
        show 1 + 2 * (m + 1) = 2 * m + 3 from by ring] at this
    exact this
  -- r3_chain (2m+3): (2m+3, 0, 0, 2m+2, 2m+2, f) ⊢* (0, 0, 0, 2m+2, 4m+5, f+2m+3)
  have h4 : ⟨2 * m + 3, 0, 0, 2 * m + 2, 2 * m + 2, f⟩ [fm]⊢* ⟨0, 0, 0, 2 * m + 2, 4 * m + 5, f + 2 * m + 3⟩ := by
    have := r3_chain (2 * m + 3) (2 * m + 2) (2 * m + 2) f
    rw [show 2 * m + 2 + (2 * m + 3) = 4 * m + 5 from by ring,
        show f + (2 * m + 3) = f + 2 * m + 3 from by ring] at this
    exact this
  -- r4_chain (2m+2): (0, 0, 0, 2m+2, 4m+5, f+2m+3) ⊢* (0, 2m+2, 0, 0, 4m+5, f+2m+3)
  have h5 : ⟨0, 0, 0, 2 * m + 2, 4 * m + 5, f + 2 * m + 3⟩ [fm]⊢* ⟨0, 2 * m + 2, 0, 0, 4 * m + 5, f + 2 * m + 3⟩ := by
    have := r4_chain (2 * m + 2) 0 (4 * m + 5) (f + 2 * m + 3)
    rw [show 0 + (2 * m + 2) = 2 * m + 2 from by ring] at this
    exact this
  exact stepStar_trans h1 (stepStar_trans h2 (stepStar_trans h3 (stepStar_trans h4 h5)))

theorem main_even (m f : ℕ) :
    ⟨0, 2 * m, 0, 0, 4 * m + 1, f + 1⟩ [fm]⊢⁺
    ⟨0, 2 * m + 1, 0, 0, 4 * m + 3, f + 2 * m + 2⟩ := by
  step fm
  rw [show 2 * m + 1 = (2 * m) + 1 from by ring]
  step fm
  exact phase_even m f

theorem main_odd (m f : ℕ) :
    ⟨0, 2 * m + 1, 0, 0, 4 * m + 3, f + 1⟩ [fm]⊢⁺
    ⟨0, 2 * m + 2, 0, 0, 4 * m + 5, f + 2 * m + 3⟩ := by
  step fm
  rw [show 2 * m + 2 = (2 * m + 1) + 1 from by ring]
  step fm
  exact phase_odd m f

theorem main_trans (n f : ℕ) :
    ⟨0, n, 0, 0, 2 * n + 1, f + 1⟩ [fm]⊢⁺
    ⟨0, n + 1, 0, 0, 2 * n + 3, f + n + 2⟩ := by
  rcases Nat.even_or_odd n with ⟨m, hm⟩ | ⟨m, hm⟩
  · rw [show m + m = 2 * m from by ring] at hm; subst hm
    rw [show 2 * (2 * m) + 1 = 4 * m + 1 from by ring,
        show 2 * (2 * m) + 3 = 4 * m + 3 from by ring,
        show 2 * m + 1 = 2 * m + 1 from rfl,
        show f + 2 * m + 2 = f + 2 * m + 2 from rfl]
    exact main_even m f
  · subst hm
    rw [show 2 * (2 * m + 1) + 1 = 4 * m + 3 from by ring,
        show 2 * (2 * m + 1) + 3 = 4 * m + 5 from by ring,
        show 2 * m + 1 + 1 = 2 * m + 2 from by ring,
        show f + (2 * m + 1) + 2 = f + 2 * m + 3 from by ring]
    exact main_odd m f

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨0, 0, 0, 0, 1, 1⟩) (by execute fm 1)
  apply progress_nonhalt_simple (fm := fm) (A := ℕ × ℕ)
    (fun ⟨n, f⟩ ↦ ⟨0, n, 0, 0, 2 * n + 1, f + 1⟩) ⟨0, 0⟩
  intro ⟨n, f⟩
  exact ⟨⟨n + 1, f + n + 1⟩, main_trans n f⟩

end Sz22_2003_unofficial_735
