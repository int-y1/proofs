import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #910: [4/15, 3/14, 3025/2, 7/11, 22/5]

Vector representation:
```
 2 -1 -1  0  0
-1  1  0 -1  0
-1  0  2  0  2
 0  0  0  1 -1
 1  0 -1  0  1
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_910

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a, b+1, c+1, d, e⟩ => some ⟨a+2, b, c, d, e⟩
  | ⟨a+1, b, c, d+1, e⟩ => some ⟨a, b+1, c, d, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b, c+2, d, e+2⟩
  | ⟨a, b, c, d, e+1⟩ => some ⟨a, b, c, d+1, e⟩
  | ⟨a, b, c+1, d, e⟩ => some ⟨a+1, b, c, d, e+1⟩
  | _ => none

theorem e_to_d : ∀ k, ∀ c d, ⟨0, 0, c, d, e + k⟩ [fm]⊢* ⟨0, 0, c, d + k, e⟩ := by
  intro k; induction' k with k ih <;> intro c d
  · exists 0
  · rw [show e + (k + 1) = (e + k) + 1 from by ring]
    step fm; apply stepStar_trans (ih c (d + 1)); ring_nf; finish

theorem r2r1_chain : ∀ k, ∀ a c d,
    ⟨a + 1, 0, c + k, d + k, 1⟩ [fm]⊢* ⟨a + k + 1, 0, c, d, 1⟩ := by
  intro k; induction' k with k ih <;> intro a c d
  · exists 0
  · rw [show c + (k + 1) = (c + k) + 1 from by ring,
        show d + (k + 1) = (d + k) + 1 from by ring]
    step fm; step fm
    apply stepStar_trans (ih (a + 1) c d); ring_nf; finish

theorem r2_chain : ∀ k, ∀ a b d,
    ⟨a + k, b, 0, d + k, 1⟩ [fm]⊢* ⟨a, b + k, 0, d, 1⟩ := by
  intro k; induction' k with k ih <;> intro a b d
  · exists 0
  · rw [show a + (k + 1) = (a + k) + 1 from by ring,
        show d + (k + 1) = (d + k) + 1 from by ring]
    step fm; apply stepStar_trans (ih a (b + 1) d); ring_nf; finish

theorem r3r1r1_chain : ∀ k, ∀ a b e,
    ⟨a + 1, b + 2 * k, 0, 0, e⟩ [fm]⊢* ⟨a + 3 * k + 1, b, 0, 0, e + 2 * k⟩ := by
  intro k; induction' k with k ih <;> intro a b e
  · exists 0
  · rw [show b + 2 * (k + 1) = (b + 2 * k) + 2 from by ring]
    step fm; step fm; step fm
    apply stepStar_trans (ih (a + 3) b (e + 2)); ring_nf; finish

theorem r3r1_tail : ⟨a + 1, 1, 0, 0, e⟩ [fm]⊢* ⟨a + 2, 0, 1, 0, e + 2⟩ := by
  step fm; step fm; finish

theorem r3_drain : ∀ j, ∀ c e,
    ⟨j, 0, c, 0, e⟩ [fm]⊢* ⟨0, 0, c + 2 * j, 0, e + 2 * j⟩ := by
  intro j; induction' j with j ih <;> intro c e
  · exists 0
  · step fm; apply stepStar_trans (ih (c + 2) (e + 2)); ring_nf; finish

-- Spiral: R5 + r2r1_chain. (0,0,c+1,(c+1)+D,0) ⊢⁺ (c+1, 0, 0, D+1, 1)
theorem spiral (c D : ℕ) :
    ⟨0, 0, c + 1, (c + 1) + D, 0⟩ [fm]⊢⁺ ⟨c + 1, 0, 0, D + 1, 1⟩ := by
  apply step_stepStar_stepPlus
  · show fm ⟨0, 0, c + 1, (c + 1) + D, 0⟩ = some ⟨1, 0, c, (c + 1) + D, 1⟩
    unfold fm; simp only
  have := r2r1_chain c 0 0 (D + 1)
  ring_nf at this ⊢; exact this

theorem main_trans (A f : ℕ) :
    ⟨0, 0, A + 2 * f + 2, 0, A + 4 * f + 2⟩ [fm]⊢⁺
    ⟨0, 0, 2 * A + 6 * f + 5, 0, 2 * A + 8 * f + 7⟩ := by
  have h1 : ⟨0, 0, A + 2 * f + 2, 0, A + 4 * f + 2⟩ [fm]⊢*
      ⟨0, 0, A + 2 * f + 2, A + 4 * f + 2, 0⟩ := by
    rw [show A + 4 * f + 2 = 0 + (A + 4 * f + 2) from by ring]
    exact e_to_d (A + 4 * f + 2) (A + 2 * f + 2) 0 (e := 0)
  have h2 : ⟨0, 0, A + 2 * f + 2, A + 4 * f + 2, 0⟩ [fm]⊢⁺
      ⟨A + 2 * f + 2, 0, 0, 2 * f + 1, 1⟩ := by
    have := spiral (A + 2 * f + 1) (2 * f)
    rw [show A + 2 * f + 1 + 1 = A + 2 * f + 2 from by ring,
        show (A + 2 * f + 1 + 1) + (2 * f) = A + 4 * f + 2 from by ring,
        show 2 * f + 1 = 2 * f + 1 from rfl] at this
    exact this
  have h3 : ⟨A + 2 * f + 2, 0, 0, 2 * f + 1, 1⟩ [fm]⊢*
      ⟨A + 1, 2 * f + 1, 0, 0, 1⟩ := by
    have := r2_chain (2 * f + 1) (A + 1) 0 0
    rw [show (A + 1) + (2 * f + 1) = A + 2 * f + 2 from by ring,
        show 0 + (2 * f + 1) = 2 * f + 1 from by ring] at this
    exact this
  have h4 : ⟨A + 1, 2 * f + 1, 0, 0, 1⟩ [fm]⊢*
      ⟨A + 3 * f + 1, 1, 0, 0, 2 * f + 1⟩ := by
    have := r3r1r1_chain f A 1 1
    ring_nf at this ⊢; exact this
  have h5 : ⟨A + 3 * f + 1, 1, 0, 0, 2 * f + 1⟩ [fm]⊢*
      ⟨A + 3 * f + 2, 0, 1, 0, 2 * f + 3⟩ := by
    have := r3r1_tail (a := A + 3 * f) (e := 2 * f + 1)
    ring_nf at this ⊢; exact this
  have h6 : ⟨A + 3 * f + 2, 0, 1, 0, 2 * f + 3⟩ [fm]⊢*
      ⟨0, 0, 2 * A + 6 * f + 5, 0, 2 * A + 8 * f + 7⟩ := by
    have := r3_drain (A + 3 * f + 2) 1 (2 * f + 3)
    rw [show 1 + 2 * (A + 3 * f + 2) = 2 * A + 6 * f + 5 from by ring,
        show (2 * f + 3) + 2 * (A + 3 * f + 2) = 2 * A + 8 * f + 7 from by ring] at this
    exact this
  exact stepStar_stepPlus_stepPlus h1
    (stepPlus_stepStar_stepPlus h2
      (stepStar_trans h3 (stepStar_trans h4 (stepStar_trans h5 h6))))

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨0, 0, 2, 0, 2⟩)
  · execute fm 1
  apply progress_nonhalt_simple (fm := fm) (A := ℕ × ℕ)
    (fun p ↦ ⟨0, 0, p.1 + 2 * p.2 + 2, 0, p.1 + 4 * p.2 + 2⟩) ⟨0, 0⟩
  intro ⟨A, f⟩
  refine ⟨⟨2 * A + 4 * f + 1, f + 1⟩, ?_⟩
  show ⟨0, 0, A + 2 * f + 2, 0, A + 4 * f + 2⟩ [fm]⊢⁺
    ⟨0, 0, (2 * A + 4 * f + 1) + 2 * (f + 1) + 2, 0,
     (2 * A + 4 * f + 1) + 4 * (f + 1) + 2⟩
  rw [show (2 * A + 4 * f + 1) + 2 * (f + 1) + 2 = 2 * A + 6 * f + 5 from by ring,
      show (2 * A + 4 * f + 1) + 4 * (f + 1) + 2 = 2 * A + 8 * f + 7 from by ring]
  exact main_trans A f

end Sz22_2003_unofficial_910
