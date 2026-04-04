import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #1739: [8/15, 33/14, 55/2, 91/11, 3/13]

Vector representation:
```
 3 -1 -1  0  0  0
-1  1  0 -1  1  0
-1  0  1  0  1  0
 0  0  0  1 -1  1
 0  1  0  0  0 -1
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_1739

def Q := ℕ × ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a, b+1, c+1, d, e, f⟩ => some ⟨a+3, b, c, d, e, f⟩
  | ⟨a+1, b, c, d+1, e, f⟩ => some ⟨a, b+1, c, d, e+1, f⟩
  | ⟨a+1, b, c, d, e, f⟩ => some ⟨a, b, c+1, d, e+1, f⟩
  | ⟨a, b, c, d, e+1, f⟩ => some ⟨a, b, c, d+1, e, f+1⟩
  | ⟨a, b, c, d, e, f+1⟩ => some ⟨a, b+1, c, d, e, f⟩
  | _ => none

private theorem r3_s (a c e f : ℕ) :
    (⟨a + 1, 0, c, 0, e, f⟩ : Q) [fm]⊢ ⟨a, 0, c + 1, 0, e + 1, f⟩ := by simp [fm]

private theorem r4_s (c d e f : ℕ) :
    (⟨0, 0, c, d, e + 1, f⟩ : Q) [fm]⊢ ⟨0, 0, c, d + 1, e, f + 1⟩ := by simp [fm]

private theorem r2_s (a b d e f : ℕ) :
    (⟨a + 1, b, 0, d + 1, e, f⟩ : Q) [fm]⊢ ⟨a, b + 1, 0, d, e + 1, f⟩ := by simp [fm]

private theorem r3b_s (a b e f : ℕ) :
    (⟨a + 1, b, 0, 0, e, f⟩ : Q) [fm]⊢ ⟨a, b, 1, 0, e + 1, f⟩ := by simp [fm]

private theorem r1_s (a b c d e f : ℕ) :
    (⟨a, b + 1, c + 1, d, e, f⟩ : Q) [fm]⊢ ⟨a + 3, b, c, d, e, f⟩ := by simp [fm]

theorem r3_chain (a f : ℕ) : ∀ k c e : ℕ,
    (⟨a + k, 0, c, 0, e, f⟩ : Q) [fm]⊢* ⟨a, 0, c + k, 0, e + k, f⟩ := by
  intro k; induction k with
  | zero => intro c e; finish
  | succ k ih =>
    intro c e
    rw [show a + (k + 1) = (a + k) + 1 from by ring]
    apply stepStar_trans (step_stepStar (r3_s (a + k) c e f))
    rw [show c + (k + 1) = (c + 1) + k from by ring,
        show e + (k + 1) = (e + 1) + k from by ring]
    exact ih (c + 1) (e + 1)

theorem r4_chain (c : ℕ) : ∀ k d f : ℕ,
    (⟨0, 0, c, d, e + k, f⟩ : Q) [fm]⊢* ⟨0, 0, c, d + k, e, f + k⟩ := by
  intro k; induction k with
  | zero => intro d f; finish
  | succ k ih =>
    intro d f
    rw [show e + (k + 1) = (e + k) + 1 from by ring]
    apply stepStar_trans (step_stepStar (r4_s c d (e + k) f))
    rw [show d + (k + 1) = (d + 1) + k from by ring,
        show f + (k + 1) = (f + 1) + k from by ring]
    exact ih (d + 1) (f + 1)

theorem r2r1 (a c d e f : ℕ) :
    (⟨a + 1, 0, c + 1, d + 1, e, f⟩ : Q) [fm]⊢⁺ ⟨a + 3, 0, c, d, e + 1, f⟩ := by
  step fm; step fm; finish

theorem r2r1_chain (f : ℕ) : ∀ k a d e : ℕ,
    (⟨a + 1, 0, k, d + k, e, f⟩ : Q) [fm]⊢* ⟨a + 2 * k + 1, 0, 0, d, e + k, f⟩ := by
  intro k; induction k with
  | zero => intro a d e; finish
  | succ k ih =>
    intro a d e
    rw [show d + (k + 1) = (d + k) + 1 from by ring]
    apply stepStar_trans (stepPlus_stepStar (r2r1 a k (d + k) e f))
    rw [show a + 3 = (a + 2) + 1 from by ring,
        show a + 2 * (k + 1) + 1 = (a + 2) + 2 * k + 1 from by ring,
        show e + (k + 1) = (e + 1) + k from by ring]
    exact ih (a + 2) d (e + 1)

theorem r2_chain (f : ℕ) : ∀ k a b d e : ℕ,
    (⟨a + k, b, 0, d + k, e, f⟩ : Q) [fm]⊢* ⟨a, b + k, 0, d, e + k, f⟩ := by
  intro k; induction k with
  | zero => intro a b d e; finish
  | succ k ih =>
    intro a b d e
    rw [show a + (k + 1) = (a + k) + 1 from by ring,
        show d + (k + 1) = (d + k) + 1 from by ring]
    apply stepStar_trans (step_stepStar (r2_s (a + k) b (d + k) e f))
    rw [show b + (k + 1) = (b + 1) + k from by ring,
        show e + (k + 1) = (e + 1) + k from by ring]
    exact ih a (b + 1) d (e + 1)

theorem r3r1 (a k e f : ℕ) :
    (⟨a + 1, k + 1, 0, 0, e, f⟩ : Q) [fm]⊢⁺ ⟨a + 3, k, 0, 0, e + 1, f⟩ := by
  apply stepStar_step_stepPlus (step_stepStar (r3b_s a (k + 1) e f))
  exact r1_s a k 0 0 (e + 1) f

theorem r3r1_chain (f : ℕ) : ∀ k a e : ℕ,
    (⟨a + 1, k, 0, 0, e, f⟩ : Q) [fm]⊢* ⟨a + 2 * k + 1, 0, 0, 0, e + k, f⟩ := by
  intro k; induction k with
  | zero => intro a e; finish
  | succ k ih =>
    intro a e
    apply stepStar_trans (stepPlus_stepStar (r3r1 a k e f))
    rw [show a + 3 = (a + 2) + 1 from by ring,
        show a + 2 * (k + 1) + 1 = (a + 2) + 2 * k + 1 from by ring,
        show e + (k + 1) = (e + 1) + k from by ring]
    exact ih (a + 2) (e + 1)

theorem phase3 (c d F : ℕ) :
    (⟨0, 0, c + 1, d + c, 0, F + 1⟩ : Q) [fm]⊢⁺ ⟨2 * c + 3, 0, 0, d, c, F⟩ := by
  apply stepPlus_stepStar_stepPlus
    (show (⟨0, 0, c + 1, d + c, 0, F + 1⟩ : Q) [fm]⊢⁺ ⟨3, 0, c, d + c, 0, F⟩ from by
      step fm; step fm; finish)
  have h := r2r1_chain F c 2 d 0
  rw [show (2 : ℕ) + 1 = 3 from by ring,
      show 2 + 2 * c + 1 = 2 * c + 3 from by ring,
      show (0 : ℕ) + c = c from by ring] at h
  exact h

theorem main_trans (g e f : ℕ) :
    (⟨e + g + 4, 0, 0, 0, e + 2, f⟩ : Q) [fm]⊢⁺
      ⟨3 * e + 2 * g + 12, 0, 0, 0, 3 * e + g + 9, f + 2 * e + g + 5⟩ := by
  apply stepStar_stepPlus_stepPlus
  · have h := r3_chain 0 f (e + g + 4) 0 (e + 2)
    rw [show (0 : ℕ) + (e + g + 4) = e + g + 4 from by ring,
        show (e + 2) + (e + g + 4) = 2 * e + g + 6 from by ring] at h
    exact h
  apply stepStar_stepPlus_stepPlus
  · have h := r4_chain (e + g + 4) (2 * e + g + 6) 0 f (e := 0)
    rw [show (0 : ℕ) + (2 * e + g + 6) = 2 * e + g + 6 from by ring] at h
    exact h
  apply stepPlus_stepStar_stepPlus
  · have h := phase3 (e + g + 3) (e + 3) (f + 2 * e + g + 5)
    rw [show (e + g + 3) + 1 = e + g + 4 from by ring,
        show (e + 3) + (e + g + 3) = 2 * e + g + 6 from by ring,
        show (f + 2 * e + g + 5) + 1 = f + (2 * e + g + 6) from by ring,
        show 2 * (e + g + 3) + 3 = 2 * e + 2 * g + 9 from by ring] at h
    exact h
  have h4 := r2_chain (f + 2 * e + g + 5) (e + 3) (e + 2 * g + 6) 0 0 (e + g + 3)
  rw [show (e + 2 * g + 6) + (e + 3) = 2 * e + 2 * g + 9 from by ring,
      show (0 : ℕ) + (e + 3) = e + 3 from by ring,
      show (e + g + 3) + (e + 3) = 2 * e + g + 6 from by ring] at h4
  apply stepStar_trans h4
  have h5 := r3r1_chain (f + 2 * e + g + 5) (e + 3) (e + 2 * g + 5) (2 * e + g + 6)
  rw [show (e + 2 * g + 5) + 1 = e + 2 * g + 6 from by ring,
      show (e + 2 * g + 5) + 2 * (e + 3) + 1 = 3 * e + 2 * g + 12 from by ring,
      show (2 * e + g + 6) + (e + 3) = 3 * e + g + 9 from by ring] at h5
  exact h5

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨4, 0, 0, 0, 2, 0⟩)
  · execute fm 7
  · apply progress_nonhalt_simple (fm := fm) (A := ℕ × ℕ × ℕ)
      (fun ⟨g, e, f⟩ ↦ ⟨e + g + 4, 0, 0, 0, e + 2, f⟩) ⟨0, 0, 0⟩
    intro ⟨g, e, f⟩
    refine ⟨⟨g + 1, 3 * e + g + 7, f + 2 * e + g + 5⟩, ?_⟩
    show (⟨e + g + 4, 0, 0, 0, e + 2, f⟩ : Q) [fm]⊢⁺
      ⟨(3 * e + g + 7) + (g + 1) + 4, 0, 0, 0, (3 * e + g + 7) + 2, f + 2 * e + g + 5⟩
    rw [show (3 * e + g + 7) + (g + 1) + 4 = 3 * e + 2 * g + 12 from by ring,
        show (3 * e + g + 7) + 2 = 3 * e + g + 9 from by ring]
    exact main_trans g e f
