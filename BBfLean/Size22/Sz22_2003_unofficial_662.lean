import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #662: [35/6, 1573/2, 4/65, 3/7, 6/11]

Vector representation:
```
-1 -1  1  1  0  0
-1  0  0  0  2  1
 2  0 -1  0  0 -1
 0  1  0 -1  0  0
 1  1  0  0 -1  0
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_662

def Q := ℕ × ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a+1, b+1, c, d, e, f⟩ => some ⟨a, b, c+1, d+1, e, f⟩
  | ⟨a+1, b, c, d, e, f⟩ => some ⟨a, b, c, d, e+2, f+1⟩
  | ⟨a, b, c+1, d, e, f+1⟩ => some ⟨a+2, b, c, d, e, f⟩
  | ⟨a, b, c, d+1, e, f⟩ => some ⟨a, b+1, c, d, e, f⟩
  | ⟨a, b, c, d, e+1, f⟩ => some ⟨a+1, b+1, c, d, e, f⟩
  | _ => none

theorem d_to_b (e f : ℕ) : ∀ k, ∀ b d,
    ⟨0, b, 0, d + k, e, f⟩ [fm]⊢* ⟨0, b + k, 0, d, e, f⟩ := by
  intro k; induction' k with k ih <;> intro b d
  · exists 0
  · rw [show d + (k + 1) = (d + k) + 1 from by ring]; step fm
    apply stepStar_trans (ih (b + 1) d); ring_nf; finish

theorem r5r1r3 (n e : ℕ) :
    ⟨0, n, 0, 0, e + 1, n + 1⟩ [fm]⊢* ⟨2, n, 0, 1, e, n⟩ := by
  step fm; step fm; step fm; finish

theorem r1r1r3_chain (e : ℕ) : ∀ k, ∀ b c d f,
    ⟨2, b + 2 * k, c, d, e, f + k⟩ [fm]⊢* ⟨2, b, c + k, d + 2 * k, e, f⟩ := by
  intro k; induction' k with k ih <;> intro b c d f
  · exists 0
  · rw [show b + 2 * (k + 1) = (b + 2 * k) + 1 + 1 from by ring,
        show f + (k + 1) = (f + k) + 1 from by ring]
    step fm; step fm; step fm
    apply stepStar_trans (ih b (c + 1) (d + 2) f); ring_nf; finish

theorem r2r2r3_chain : ∀ k, ∀ c d e f,
    ⟨2, 0, c + k, d, e, f + k⟩ [fm]⊢* ⟨2, 0, c, d, e + 4 * k, f + 2 * k⟩ := by
  intro k; induction' k with k ih <;> intro c d e f
  · exists 0
  · rw [show c + (k + 1) = (c + k) + 1 from by ring,
        show f + (k + 1) = (f + k) + 1 from by ring]
    step fm; step fm; step fm
    rw [show e + 2 + 2 = (e + 4) + 0 from by ring,
        show f + k + 2 = (f + 2) + k from by ring]
    apply stepStar_trans (ih c d (e + 4) (f + 2)); ring_nf; finish

theorem r2r2_finish (d e f : ℕ) :
    ⟨2, 0, 0, d, e, f⟩ [fm]⊢⁺ ⟨0, 0, 0, d, e + 4, f + 2⟩ := by
  step fm; step fm; finish

-- Full even cycle.
theorem even_trans (m : ℕ) :
    ⟨0, 0, 0, 2 * m, 4 * m ^ 2 + 4 * m + 2, 2 * m + 1⟩ [fm]⊢⁺
    ⟨0, 0, 0, 2 * m + 1, 4 * m ^ 2 + 8 * m + 5, 2 * m + 2⟩ := by
  have h1 : ⟨0, 0, 0, 2 * m, 4 * m ^ 2 + 4 * m + 2, 2 * m + 1⟩ [fm]⊢*
      ⟨0, 2 * m, 0, 0, 4 * m ^ 2 + 4 * m + 2, 2 * m + 1⟩ := by
    convert d_to_b (4 * m ^ 2 + 4 * m + 2) (2 * m + 1) (2 * m) 0 0 using 6
    all_goals (first | rfl | ring_nf)
  have h2 : ⟨0, 2 * m, 0, 0, 4 * m ^ 2 + 4 * m + 2, 2 * m + 1⟩ [fm]⊢*
      ⟨2, 2 * m, 0, 1, 4 * m ^ 2 + 4 * m + 1, 2 * m⟩ := by
    convert r5r1r3 (2 * m) (4 * m ^ 2 + 4 * m + 1) using 6
  have h3 : ⟨2, 2 * m, 0, 1, 4 * m ^ 2 + 4 * m + 1, 2 * m⟩ [fm]⊢*
      ⟨2, 0, m, 1 + 2 * m, 4 * m ^ 2 + 4 * m + 1, m⟩ := by
    convert r1r1r3_chain (4 * m ^ 2 + 4 * m + 1) m 0 0 1 m using 6
    all_goals (first | rfl | ring_nf)
  have h4 : ⟨2, 0, m, 1 + 2 * m, 4 * m ^ 2 + 4 * m + 1, m⟩ [fm]⊢*
      ⟨2, 0, 0, 1 + 2 * m, 4 * m ^ 2 + 8 * m + 1, 2 * m⟩ := by
    convert r2r2r3_chain m 0 (1 + 2 * m) (4 * m ^ 2 + 4 * m + 1) 0 using 6
    all_goals (first | rfl | ring_nf)
  have h5 : ⟨2, 0, 0, 1 + 2 * m, 4 * m ^ 2 + 8 * m + 1, 2 * m⟩ [fm]⊢⁺
      ⟨0, 0, 0, 1 + 2 * m, 4 * m ^ 2 + 8 * m + 5, 2 * m + 2⟩ := by
    convert r2r2_finish (1 + 2 * m) (4 * m ^ 2 + 8 * m + 1) (2 * m) using 6
  exact stepStar_stepPlus_stepPlus
    (stepStar_trans h1 (stepStar_trans h2 (stepStar_trans h3 h4)))
    (stepPlus_stepStar_stepPlus h5 (by ring_nf; finish))

-- Full odd cycle.
theorem odd_trans (m : ℕ) :
    ⟨0, 0, 0, 2 * m + 1, 4 * m ^ 2 + 8 * m + 5, 2 * m + 2⟩ [fm]⊢⁺
    ⟨0, 0, 0, 2 * m + 2, 4 * m ^ 2 + 12 * m + 10, 2 * m + 3⟩ := by
  have h1 : ⟨0, 0, 0, 2 * m + 1, 4 * m ^ 2 + 8 * m + 5, 2 * m + 2⟩ [fm]⊢*
      ⟨0, 2 * m + 1, 0, 0, 4 * m ^ 2 + 8 * m + 5, 2 * m + 2⟩ := by
    convert d_to_b (4 * m ^ 2 + 8 * m + 5) (2 * m + 2) (2 * m + 1) 0 0 using 6
    all_goals (first | rfl | ring_nf)
  have h2 : ⟨0, 2 * m + 1, 0, 0, 4 * m ^ 2 + 8 * m + 5, 2 * m + 2⟩ [fm]⊢*
      ⟨2, 2 * m + 1, 0, 1, 4 * m ^ 2 + 8 * m + 4, 2 * m + 1⟩ := by
    convert r5r1r3 (2 * m + 1) (4 * m ^ 2 + 8 * m + 4) using 6
  have h3 : ⟨2, 2 * m + 1, 0, 1, 4 * m ^ 2 + 8 * m + 4, 2 * m + 1⟩ [fm]⊢*
      ⟨2, 1, m, 1 + 2 * m, 4 * m ^ 2 + 8 * m + 4, m + 1⟩ := by
    convert r1r1r3_chain (4 * m ^ 2 + 8 * m + 4) m 1 0 1 (m + 1) using 6
    all_goals (first | rfl | ring_nf)
  have h4 : ⟨2, 1, m, 1 + 2 * m, 4 * m ^ 2 + 8 * m + 4, m + 1⟩ [fm]⊢*
      ⟨2, 0, m, 2 + 2 * m, 4 * m ^ 2 + 8 * m + 6, m + 1⟩ := by
    rw [show 1 + 2 * m = (2 * m) + 1 from by ring]
    step fm; step fm; step fm
    rw [show 4 * m ^ 2 + 8 * m + 4 + 2 = 4 * m ^ 2 + 8 * m + 6 from by ring,
        show 2 * m + 2 = 2 + 2 * m from by ring]
    finish
  have h5 : ⟨2, 0, m, 2 + 2 * m, 4 * m ^ 2 + 8 * m + 6, m + 1⟩ [fm]⊢*
      ⟨2, 0, 0, 2 + 2 * m, 4 * m ^ 2 + 12 * m + 6, 1 + 2 * m⟩ := by
    convert r2r2r3_chain m 0 (2 + 2 * m) (4 * m ^ 2 + 8 * m + 6) 1 using 6
    all_goals (first | rfl | ring_nf)
  have h6 : ⟨2, 0, 0, 2 + 2 * m, 4 * m ^ 2 + 12 * m + 6, 1 + 2 * m⟩ [fm]⊢⁺
      ⟨0, 0, 0, 2 + 2 * m, 4 * m ^ 2 + 12 * m + 10, 3 + 2 * m⟩ := by
    convert r2r2_finish (2 + 2 * m) (4 * m ^ 2 + 12 * m + 6) (1 + 2 * m) using 6
    all_goals (first | rfl | ring_nf)
  exact stepStar_stepPlus_stepPlus
    (stepStar_trans h1 (stepStar_trans h2 (stepStar_trans h3 (stepStar_trans h4 h5))))
    (stepPlus_stepStar_stepPlus h6 (by ring_nf; finish))

-- Main transition.
theorem main_trans (n : ℕ) :
    ⟨0, 0, 0, n, n ^ 2 + 2 * n + 2, n + 1⟩ [fm]⊢⁺
    ⟨0, 0, 0, n + 1, (n + 1) ^ 2 + 2 * (n + 1) + 2, n + 2⟩ := by
  rcases Nat.even_or_odd n with ⟨m, hm⟩ | ⟨m, hm⟩
  · rw [show m + m = 2 * m from by ring] at hm; subst hm
    show ⟨0, 0, 0, 2 * m, (2 * m) ^ 2 + 2 * (2 * m) + 2, 2 * m + 1⟩ [fm]⊢⁺ _
    rw [show (2 * m) ^ 2 + 2 * (2 * m) + 2 = 4 * m ^ 2 + 4 * m + 2 from by ring]
    apply stepPlus_stepStar_stepPlus (even_trans m)
    rw [show (2 * m + 1) ^ 2 + 2 * (2 * m + 1) + 2 = 4 * m ^ 2 + 8 * m + 5 from by ring]
    finish
  · subst hm
    show ⟨0, 0, 0, 2 * m + 1, (2 * m + 1) ^ 2 + 2 * (2 * m + 1) + 2, 2 * m + 2⟩ [fm]⊢⁺ _
    rw [show (2 * m + 1) ^ 2 + 2 * (2 * m + 1) + 2 = 4 * m ^ 2 + 8 * m + 5 from by ring]
    apply stepPlus_stepStar_stepPlus (odd_trans m)
    rw [show (2 * m + 2) ^ 2 + 2 * (2 * m + 2) + 2 = 4 * m ^ 2 + 12 * m + 10 from by ring]
    finish

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨0, 0, 0, 0, 2, 1⟩) (by execute fm 1)
  have key : ∀ n : ℕ, ∃ n', (⟨0, 0, 0, n, n ^ 2 + 2 * n + 2, n + 1⟩ : Q) [fm]⊢⁺
      ⟨0, 0, 0, n', n' ^ 2 + 2 * n' + 2, n' + 1⟩ :=
    fun n ↦ ⟨n + 1, main_trans n⟩
  exact progress_nonhalt_simple (fm := fm) (A := ℕ)
    (fun n ↦ ⟨0, 0, 0, n, n ^ 2 + 2 * n + 2, n + 1⟩) 0 key
