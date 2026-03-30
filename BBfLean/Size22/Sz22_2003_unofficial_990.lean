import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #990: [4/15, 33/14, 65/2, 7/11, 66/13]

Vector representation:
```
 2 -1 -1  0  0  0
-1  1  0 -1  1  0
-1  0  1  0  0  1
 0  0  0  1 -1  0
 1  1  0  0  1 -1
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_990

def Q := ℕ × ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a, b+1, c+1, d, e, f⟩ => some ⟨a+2, b, c, d, e, f⟩
  | ⟨a+1, b, c, d+1, e, f⟩ => some ⟨a, b+1, c, d, e+1, f⟩
  | ⟨a+1, b, c, d, e, f⟩ => some ⟨a, b, c+1, d, e, f+1⟩
  | ⟨a, b, c, d, e+1, f⟩ => some ⟨a, b, c, d+1, e, f⟩
  | ⟨a, b, c, d, e, f+1⟩ => some ⟨a+1, b+1, c, d, e+1, f⟩
  | _ => none

theorem r4_drain : ∀ k c d f,
    ⟨(0 : ℕ), 0, c, d, k, f⟩ [fm]⊢* ⟨0, 0, c, d + k, 0, f⟩ := by
  intro k; induction k with
  | zero => intro c d f; ring_nf; finish
  | succ k ih =>
    intro c d f; step fm
    apply stepStar_trans (ih c (d + 1) f); ring_nf; finish

theorem r1r2_chain : ∀ k a c d e f,
    ⟨a + 1, (0 : ℕ), c + k, d + k, e, f⟩ [fm]⊢* ⟨a + k + 1, 0, c, d, e + k, f⟩ := by
  intro k; induction k with
  | zero => intro a c d e f; ring_nf; finish
  | succ k ih =>
    intro a c d e f
    rw [show c + (k + 1) = (c + k) + 1 from by ring,
        show d + (k + 1) = (d + k) + 1 from by ring]
    step fm; step fm
    apply stepStar_trans (ih (a + 1) c d (e + 1) f); ring_nf; finish

theorem r3_drain : ∀ k c e f,
    ⟨k, (0 : ℕ), c, 0, e, f⟩ [fm]⊢* ⟨0, 0, c + k, 0, e, f + k⟩ := by
  intro k; induction k with
  | zero => intro c e f; ring_nf; finish
  | succ k ih =>
    intro c e f; step fm
    apply stepStar_trans (ih (c + 1) e (f + 1)); ring_nf; finish

theorem main_trans (n f : ℕ) :
    ⟨(0 : ℕ), 0, 2 * n + 1, 0, n, f + 1⟩ [fm]⊢⁺ ⟨0, 0, 2 * n + 3, 0, n + 1, f + n + 3⟩ := by
  rcases n with _ | n
  · step fm; step fm; step fm; step fm; step fm; ring_nf; finish
  · have h1 : ⟨(0 : ℕ), 0, 2 * (n + 1) + 1, 0, n + 1, f + 1⟩ [fm]⊢*
              ⟨0, 0, 2 * (n + 1) + 1, n + 1, 0, f + 1⟩ := by
      have := r4_drain (n + 1) (2 * (n + 1) + 1) 0 (f + 1)
      rw [show 0 + (n + 1) = n + 1 from by ring] at this
      exact this
    have h2 : ⟨(0 : ℕ), 0, 2 * (n + 1) + 1, n + 1, 0, f + 1⟩ [fm]⊢⁺
              ⟨3, 0, 2 * n + 2, n + 1, 1, f⟩ := by
      step fm; step fm; ring_nf; finish
    have h3 : ⟨3, (0 : ℕ), 2 * n + 2, n + 1, 1, f⟩ [fm]⊢*
              ⟨n + 4, 0, n + 1, 0, n + 2, f⟩ := by
      have := r1r2_chain (n + 1) 2 (n + 1) 0 1 f
      simp only [show (n + 1) + (n + 1) = 2 * n + 2 from by ring,
                  show 0 + (n + 1) = n + 1 from by ring,
                  show 2 + (n + 1) = n + 3 from by ring,
                  show 1 + (n + 1) = n + 2 from by ring,
                  show n + 3 + 1 = n + 4 from by ring] at this
      exact this
    have h4 : ⟨n + 4, (0 : ℕ), n + 1, 0, n + 2, f⟩ [fm]⊢*
              ⟨0, 0, 2 * n + 5, 0, n + 2, f + n + 4⟩ := by
      have := r3_drain (n + 4) (n + 1) (n + 2) f
      rw [show (n + 1) + (n + 4) = 2 * n + 5 from by ring,
          show f + (n + 4) = f + n + 4 from by ring] at this
      exact this
    show ⟨(0 : ℕ), 0, 2 * (n + 1) + 1, 0, n + 1, f + 1⟩ [fm]⊢⁺
         ⟨0, 0, 2 * (n + 1) + 3, 0, (n + 1) + 1, f + (n + 1) + 3⟩
    rw [show 2 * (n + 1) + 3 = 2 * n + 5 from by ring,
        show (n + 1) + 1 = n + 2 from by ring,
        show f + (n + 1) + 3 = f + n + 4 from by ring]
    exact stepStar_stepPlus_stepPlus h1
      (stepPlus_stepStar_stepPlus h2 (stepStar_trans h3 h4))

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨0, 0, 1, 0, 0, 1⟩) (by execute fm 1)
  apply progress_nonhalt_simple (fm := fm) (A := ℕ × ℕ)
    (fun ⟨n, f⟩ ↦ ⟨0, 0, 2 * n + 1, 0, n, f + 1⟩) ⟨0, 0⟩
  intro ⟨n, f⟩
  refine ⟨⟨n + 1, f + n + 2⟩, ?_⟩
  show ⟨(0 : ℕ), 0, 2 * n + 1, 0, n, f + 1⟩ [fm]⊢⁺ ⟨0, 0, 2 * (n + 1) + 1, 0, n + 1, f + n + 2 + 1⟩
  rw [show f + n + 2 + 1 = f + n + 3 from by ring,
      show 2 * (n + 1) + 1 = 2 * n + 3 from by ring]
  exact main_trans n f
