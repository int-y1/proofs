import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #1646: [77/15, 27/91, 286/3, 5/11, 3/2]

Vector representation:
```
 0 -1 -1  1  1  0
 0  3  0 -1  0 -1
 1 -1  0  0  1  1
 0  0  1  0 -1  0
-1  1  0  0  0  0
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_1646

def Q := ℕ × ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a, b+1, c+1, d, e, f⟩ => some ⟨a, b, c, d+1, e+1, f⟩
  | ⟨a, b, c, d+1, e, f+1⟩ => some ⟨a, b+3, c, d, e, f⟩
  | ⟨a, b+1, c, d, e, f⟩ => some ⟨a+1, b, c, d, e+1, f+1⟩
  | ⟨a, b, c, d, e+1, f⟩ => some ⟨a, b, c+1, d, e, f⟩
  | ⟨a+1, b, c, d, e, f⟩ => some ⟨a, b+1, c, d, e, f⟩
  | _ => none

theorem r4_chain : ∀ k a c e fv, ⟨a, 0, c, 0, e + k, fv⟩ [fm]⊢* ⟨a, 0, c + k, 0, e, fv⟩ := by
  intro k; induction' k with k ih <;> intro a c e fv
  · exists 0
  · rw [show e + (k + 1) = (e + k) + 1 from by ring]
    step fm
    apply stepStar_trans (ih a (c + 1) e fv)
    ring_nf; finish

theorem r3_chain : ∀ k a e f, ⟨a, k, 0, 0, e, f⟩ [fm]⊢* ⟨a + k, 0, 0, 0, e + k, f + k⟩ := by
  intro k; induction' k with k ih <;> intro a e f
  · exists 0
  · rw [show (k : ℕ) + 1 = k + 1 from rfl]
    step fm
    apply stepStar_trans (ih (a + 1) (e + 1) (f + 1))
    ring_nf; finish

theorem r2_drain : ∀ k a b d e f, ⟨a, b, 0, d + k, e, f + k⟩ [fm]⊢* ⟨a, b + 3 * k, 0, d, e, f⟩ := by
  intro k; induction' k with k ih <;> intro a b d e f
  · exists 0
  · rw [show d + (k + 1) = (d + k) + 1 from by ring, show f + (k + 1) = (f + k) + 1 from by ring]
    step fm
    apply stepStar_trans (ih a (b + 3) d e f)
    ring_nf; finish

theorem r3r2_chain : ∀ k a b e, ⟨a, b + 1, 0, k, e, 0⟩ [fm]⊢* ⟨a + k, b + 2 * k + 1, 0, 0, e + k, 0⟩ := by
  intro k; induction' k with k ih <;> intro a b e
  · exists 0
  · rw [show (k : ℕ) + 1 = k + 1 from rfl]
    step fm; step fm
    apply stepStar_trans (ih (a + 1) (b + 2) (e + 1))
    ring_nf; finish

theorem r1r2_interleave : ∀ k, ∀ a d e g,
    ⟨a, 1, 3 * k + 1, d, e, g + k⟩ [fm]⊢* ⟨a, 0, 0, d + 2 * k + 1, e + 3 * k + 1, g⟩ := by
  intro k; induction' k with k ih <;> intro a d e g
  · simp; step fm; finish
  · rw [show 3 * (k + 1) + 1 = (3 * k + 3) + 1 from by ring,
        show g + (k + 1) = (g + k) + 1 from by ring]
    step fm
    rw [show d + 1 = d + 1 from rfl, show (g + k) + 1 = (g + k) + 1 from rfl]
    step fm
    rw [show 3 * k + 3 = (3 * k + 2) + 1 from by ring]
    step fm
    rw [show 3 * k + 2 = (3 * k + 1) + 1 from by ring]
    step fm
    apply stepStar_trans (ih a (d + 2) (e + 3) g)
    ring_nf; finish

theorem main_trans (a k g : ℕ) (hg : g ≤ 2 * k) :
    ⟨a + 1, 0, 0, 0, 3 * k + 1, g + k + 1⟩ [fm]⊢⁺ ⟨a + 6 * k + 3, 0, 0, 0, 9 * k + 4, g + 4 * k + 3⟩ := by
  have phase1 : ⟨a + 1, 0, 0, 0, 3 * k + 1, g + k + 1⟩ [fm]⊢*
      ⟨a + 1, 0, 3 * k + 1, 0, 0, g + k + 1⟩ := by
    have := r4_chain (3 * k + 1) (a + 1) 0 0 (g + k + 1); simp at this; exact this
  have phase2 : ⟨a + 1, 0, 3 * k + 1, 0, 0, g + k + 1⟩ [fm]⊢⁺
      ⟨a, 1, 3 * k + 1, 0, 0, g + k + 1⟩ := by
    rw [show 3 * k + 1 = 0 + (3 * k + 1) from by ring]; step fm; finish
  have phase3 : ⟨a, 1, 3 * k + 1, 0, 0, g + k + 1⟩ [fm]⊢*
      ⟨a, 0, 0, 2 * k + 1, 3 * k + 1, g + 1⟩ := by
    rw [show g + k + 1 = (g + 1) + k from by ring]
    have := r1r2_interleave k a 0 0 (g + 1)
    simp at this; exact this
  have phase4 : ⟨a, 0, 0, 2 * k + 1, 3 * k + 1, g + 1⟩ [fm]⊢*
      ⟨a, 3 * g + 3, 0, 2 * k - g, 3 * k + 1, 0⟩ := by
    have := r2_drain (g + 1) a 0 (2 * k - g) (3 * k + 1) 0
    rw [show (2 * k - g) + (g + 1) = 2 * k + 1 from by omega,
        show 0 + (g + 1) = g + 1 from by ring,
        show 0 + 3 * (g + 1) = 3 * g + 3 from by ring] at this
    exact this
  have phase5 : ⟨a, 3 * g + 3, 0, 2 * k - g, 3 * k + 1, 0⟩ [fm]⊢*
      ⟨a + (2 * k - g), g + 4 * k + 3, 0, 0, 5 * k + 1 - g, 0⟩ := by
    rw [show 3 * g + 3 = (3 * g + 2) + 1 from by ring]
    have := r3r2_chain (2 * k - g) a (3 * g + 2) (3 * k + 1)
    rw [show 3 * g + 2 + 2 * (2 * k - g) + 1 = g + 4 * k + 3 from by omega,
        show 3 * k + 1 + (2 * k - g) = 5 * k + 1 - g from by omega] at this
    exact this
  have phase6 : ⟨a + (2 * k - g), g + 4 * k + 3, 0, 0, 5 * k + 1 - g, 0⟩ [fm]⊢*
      ⟨a + 6 * k + 3, 0, 0, 0, 9 * k + 4, g + 4 * k + 3⟩ := by
    have := r3_chain (g + 4 * k + 3) (a + (2 * k - g)) (5 * k + 1 - g) 0
    rw [show a + (2 * k - g) + (g + 4 * k + 3) = a + 6 * k + 3 from by omega,
        show 5 * k + 1 - g + (g + 4 * k + 3) = 9 * k + 4 from by omega,
        show 0 + (g + 4 * k + 3) = g + 4 * k + 3 from by ring] at this
    exact this
  have compose12 := stepStar_stepPlus_stepPlus phase1 phase2
  have compose123 := stepPlus_stepStar_stepPlus compose12 phase3
  have compose1234 := stepPlus_stepStar_stepPlus compose123 phase4
  have compose12345 := stepPlus_stepStar_stepPlus compose1234 phase5
  exact stepPlus_stepStar_stepPlus compose12345 phase6

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨1, 0, 0, 0, 1, 1⟩)
  · execute fm 2
  apply progress_nonhalt (fm := fm)
    (P := fun q ↦ ∃ a k g, q = ⟨a + 1, 0, 0, 0, 3 * k + 1, g + k + 1⟩ ∧ g ≤ 2 * k)
  · intro c ⟨a, k, g, hq, hg⟩; subst hq
    refine ⟨⟨a + 6 * k + 3, 0, 0, 0, 9 * k + 4, g + 4 * k + 3⟩,
        ⟨a + 6 * k + 2, 3 * k + 1, g + k + 1, ?_, ?_⟩, main_trans a k g hg⟩
    · show (a + 6 * k + 3, 0, 0, 0, 9 * k + 4, g + 4 * k + 3) =
        (a + 6 * k + 2 + 1, 0, 0, 0, 3 * (3 * k + 1) + 1, g + k + 1 + (3 * k + 1) + 1)
      rw [show a + 6 * k + 2 + 1 = a + 6 * k + 3 from by ring,
          show 3 * (3 * k + 1) + 1 = 9 * k + 4 from by ring,
          show g + k + 1 + (3 * k + 1) + 1 = g + 4 * k + 3 from by ring]
    · omega
  · exact ⟨0, 0, 0, by simp, by omega⟩
