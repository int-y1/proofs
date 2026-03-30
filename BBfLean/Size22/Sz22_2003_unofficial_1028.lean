import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #1028: [4/15, 99/14, 65/2, 7/11, 33/13]

Vector representation:
```
 2 -1 -1  0  0  0
-1  2  0 -1  1  0
-1  0  1  0  0  1
 0  0  0  1 -1  0
 0  1  0  0  1 -1
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_1028

def Q := ℕ × ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a, b+1, c+1, d, e, f⟩ => some ⟨a+2, b, c, d, e, f⟩
  | ⟨a+1, b, c, d+1, e, f⟩ => some ⟨a, b+2, c, d, e+1, f⟩
  | ⟨a+1, b, c, d, e, f⟩ => some ⟨a, b, c+1, d, e, f+1⟩
  | ⟨a, b, c, d, e+1, f⟩ => some ⟨a, b, c, d+1, e, f⟩
  | ⟨a, b, c, d, e, f+1⟩ => some ⟨a, b+1, c, d, e+1, f⟩
  | _ => none

theorem r3_chain : ∀ k, ∀ a c e f,
    ⟨a + k, (0 : ℕ), c, 0, e, f⟩ [fm]⊢* ⟨a, 0, c + k, 0, e, f + k⟩ := by
  intro k; induction' k with k ih <;> intro a c e f
  · ring_nf; finish
  · rw [show a + (k + 1) = (a + k) + 1 from by ring,
        show c + (k + 1) = (c + 1) + k from by ring,
        show f + (k + 1) = (f + 1) + k from by ring]
    step fm
    apply stepStar_trans (ih a (c + 1) e (f + 1))
    ring_nf; finish

theorem r4_chain : ∀ k, ∀ c d f,
    ⟨(0 : ℕ), 0, c, d, k, f⟩ [fm]⊢* ⟨0, 0, c, d + k, 0, f⟩ := by
  intro k; induction' k with k ih <;> intro c d f
  · ring_nf; finish
  · rw [show d + (k + 1) = (d + 1) + k from by ring]
    step fm
    apply stepStar_trans (ih c (d + 1) f)
    ring_nf; finish

theorem r2r1r1_chain : ∀ k, ∀ j c d f,
    ⟨3 * j + 2, (0 : ℕ), c + 2 * k, d + k, j + 1, f⟩ [fm]⊢*
    ⟨3 * (j + k) + 2, 0, c, d, j + k + 1, f⟩ := by
  intro k; induction' k with k ih <;> intro j c d f
  · ring_nf; finish
  · rw [show c + 2 * (k + 1) = (c + 2 * k) + 2 from by ring,
        show d + (k + 1) = (d + k) + 1 from by ring,
        show 3 * (j + (k + 1)) + 2 = 3 * ((j + 1) + k) + 2 from by ring,
        show j + (k + 1) + 1 = (j + 1) + k + 1 from by ring]
    step fm; step fm; step fm
    apply stepStar_trans (ih (j + 1) c d f)
    ring_nf; finish

theorem main_trans (c n f : ℕ) :
    ⟨3 * n + 11, (0 : ℕ), c, 0, n + 4, f⟩ [fm]⊢⁺
    ⟨3 * n + 14, 0, c + n + 2, 0, n + 5, f + 3 * n + 10⟩ := by
  have h1 : ⟨3 * n + 11, (0 : ℕ), c, 0, n + 4, f⟩ [fm]⊢*
      ⟨0, 0, c + (3 * n + 11), 0, n + 4, f + (3 * n + 11)⟩ := by
    have := r3_chain (3 * n + 11) 0 c (n + 4) f
    convert this using 2; ring_nf
  have h2 : ⟨(0 : ℕ), 0, c + (3 * n + 11), 0, n + 4, f + (3 * n + 11)⟩ [fm]⊢*
      ⟨0, 0, c + (3 * n + 11), n + 4, 0, f + (3 * n + 11)⟩ := by
    have := r4_chain (n + 4) (c + (3 * n + 11)) 0 (f + (3 * n + 11))
    rw [show (0 : ℕ) + (n + 4) = n + 4 from by ring] at this
    exact this
  have h3 : ⟨(0 : ℕ), 0, c + (3 * n + 11), n + 4, 0, f + (3 * n + 11)⟩ [fm]⊢⁺
      ⟨2, 0, c + 3 * n + 10, n + 4, 1, f + 3 * n + 10⟩ := by
    rw [show f + (3 * n + 11) = (f + 3 * n + 10) + 1 from by ring,
        show c + (3 * n + 11) = (c + 3 * n + 10) + 1 from by ring]
    step fm; step fm; finish
  have h4 : ⟨(2 : ℕ), 0, c + 3 * n + 10, n + 4, 1, f + 3 * n + 10⟩ [fm]⊢*
      ⟨3 * n + 14, 0, c + n + 2, 0, n + 5, f + 3 * n + 10⟩ := by
    have := r2r1r1_chain (n + 4) 0 (c + n + 2) 0 (f + 3 * n + 10)
    convert this using 2; ring_nf
  exact stepStar_stepPlus_stepPlus h1
    (stepStar_stepPlus_stepPlus h2
      (stepPlus_stepStar_stepPlus h3 h4))

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨11, 0, 0, 0, 4, 12⟩) (by execute fm 48)
  apply progress_nonhalt_simple (fm := fm) (A := ℕ × ℕ × ℕ)
    (fun ⟨c, n, f⟩ ↦ ⟨3 * n + 11, 0, c, 0, n + 4, f⟩) ⟨0, 0, 12⟩
  intro ⟨c, n, f⟩
  exact ⟨⟨c + n + 2, n + 1, f + 3 * n + 10⟩, main_trans c n f⟩
