import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #410: [25/63, 1/55, 18/5, 11/3, 175/2]

Vector representation:
```
 0 -2  2 -1  0
 0  0 -1  0 -1
 1  2 -1  0  0
 0 -1  0  0  1
-1  0  2  1  0
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_410

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a, b+2, c, d+1, e⟩ => some ⟨a, b, c+2, d, e⟩
  | ⟨a, b, c+1, d, e+1⟩ => some ⟨a, b, c, d, e⟩
  | ⟨a, b, c+1, d, e⟩ => some ⟨a+1, b+2, c, d, e⟩
  | ⟨a, b+1, c, d, e⟩ => some ⟨a, b, c, d, e+1⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b, c+2, d+1, e⟩
  | _ => none

lemma r4_step (a b e : ℕ) : (⟨a, b+1, 0, 0, e⟩ : Q) [fm]⊢ ⟨a, b, 0, 0, e+1⟩ := by
  simp [fm]

lemma r5_step (a d e : ℕ) : (⟨a+1, 0, 0, d, e⟩ : Q) [fm]⊢ ⟨a, 0, 2, d+1, e⟩ := by
  simp [fm]

lemma r2_b0 (a c d e : ℕ) : (⟨a, 0, c+1, d, e+1⟩ : Q) [fm]⊢ ⟨a, 0, c, d, e⟩ := by
  simp [fm]

lemma r3_b0 (a c d : ℕ) : (⟨a, 0, c+1, d, 0⟩ : Q) [fm]⊢ ⟨a+1, 2, c, d, 0⟩ := by
  simp [fm]

lemma r1_b2_e0 (a c d : ℕ) : (⟨a, 2, c, d+1, 0⟩ : Q) [fm]⊢ ⟨a, 0, c+2, d, 0⟩ := by
  simp [fm]

lemma r3_d0 (a b c : ℕ) : (⟨a, b, c+1, 0, 0⟩ : Q) [fm]⊢ ⟨a+1, b+2, c, 0, 0⟩ := by
  rcases b with _ | _ | b <;> simp [fm]

theorem b_to_e : ∀ k a e, ⟨a, k, 0, 0, e⟩ [fm]⊢* ⟨a, 0, 0, 0, e+k⟩ := by
  intro k; induction' k with k ih <;> intro a e
  · exists 0
  apply stepStar_trans (step_stepStar (r4_step a k e))
  have h := ih a (e + 1)
  rw [show e + 1 + k = e + (k + 1) from by ring] at h; exact h

lemma drain_cycle (a d e : ℕ) : (⟨a+1, 0, 0, d, e+2⟩ : Q) [fm]⊢* ⟨a, 0, 0, d+1, e⟩ := by
  apply stepStar_trans (step_stepStar (r5_step a d (e + 2)))
  apply stepStar_trans (step_stepStar (r2_b0 a 1 (d + 1) (e + 1)))
  exact step_stepStar (r2_b0 a 0 (d + 1) e)

theorem drain : ∀ k a d, ⟨a+k, 0, 0, d, 2*k⟩ [fm]⊢* ⟨a, 0, 0, d+k, 0⟩ := by
  intro k; induction' k with k ih <;> intro a d
  · exists 0
  have h1 : (⟨(a+k)+1, 0, 0, d, (2*k)+2⟩ : Q) [fm]⊢* ⟨a+k, 0, 0, d+1, 2*k⟩ :=
    drain_cycle (a+k) d (2*k)
  rw [show (a + k) + 1 = a + (k + 1) from by ring,
      show 2 * k + 2 = 2 * (k + 1) from by ring] at h1
  apply stepStar_trans h1
  have h2 := ih a (d + 1)
  rw [show d + 1 + k = d + (k + 1) from by ring] at h2; exact h2

lemma r3r1_pair (a c d : ℕ) : (⟨a, 0, c+1, d+1, 0⟩ : Q) [fm]⊢* ⟨a+1, 0, c+2, d, 0⟩ := by
  apply stepStar_trans (step_stepStar (r3_b0 a c (d + 1)))
  exact step_stepStar (r1_b2_e0 (a + 1) c d)

theorem r3r1_loop : ∀ k a c d, ⟨a, 0, c+1, d+k, 0⟩ [fm]⊢* ⟨a+k, 0, c+1+k, d, 0⟩ := by
  intro k; induction' k with k ih <;> intro a c d
  · exists 0
  rw [show d + (k + 1) = (d + k) + 1 from by ring]
  apply stepStar_trans (r3r1_pair a c (d + k))
  have h := ih (a + 1) (c + 1) d
  rw [show c + 1 + 1 = (c + 1) + 1 from by ring,
      show (c + 1) + 1 + k = c + 1 + (k + 1) from by ring,
      show (a + 1) + k = a + (k + 1) from by ring] at h; exact h

theorem r3_chain : ∀ k a b, ⟨a, b, k, 0, 0⟩ [fm]⊢* ⟨a+k, b+2*k, 0, 0, 0⟩ := by
  intro k; induction' k with k ih <;> intro a b
  · exists 0
  apply stepStar_trans (step_stepStar (r3_d0 a b k))
  have h := ih (a + 1) (b + 2)
  rw [show (a + 1) + k = a + (k + 1) from by ring,
      show b + 2 + 2 * k = b + 2 * (k + 1) from by ring] at h; exact h

lemma pivot (a h : ℕ) : (⟨a+1, 0, 0, h, 0⟩ : Q) [fm]⊢* ⟨a+1, 0, 3, h, 0⟩ := by
  apply stepStar_trans (step_stepStar (r5_step a h 0))
  apply stepStar_trans (step_stepStar (r3_b0 a 1 (h + 1)))
  exact step_stepStar (r1_b2_e0 (a + 1) 1 h)

theorem main_step (a h : ℕ) :
    ⟨a+h+1, 2*h, 0, 0, 0⟩ [fm]⊢⁺ ⟨a+2*h+4, 2*h+6, 0, 0, 0⟩ := by
  -- Phase 1: b_to_e
  apply stepStar_stepPlus_stepPlus
  · have t := b_to_e (2*h) (a+h+1) 0
    rw [show 0 + 2 * h = 2 * h from by ring] at t; exact t
  -- Phase 2: drain
  apply stepStar_stepPlus_stepPlus
  · have t := drain h (a+1) 0
    rw [show (a + 1) + h = a + h + 1 from by ring,
        show 0 + h = h from by ring] at t; exact t
  -- Phase 3: pivot
  apply stepStar_stepPlus_stepPlus (pivot a h)
  -- Phase 4: r3r1_loop
  apply stepStar_stepPlus_stepPlus
  · rw [show (3 : ℕ) = 2 + 1 from rfl]
    have t := r3r1_loop h (a + 1) 2 0
    rw [show 0 + h = h from by ring,
        show 2 + 1 + h = h + 3 from by ring,
        show (a + 1) + h = a + h + 1 from by ring] at t; exact t
  -- Phase 5: r3_chain
  apply step_stepStar_stepPlus
  · rw [show h + 3 = (h + 2) + 1 from by ring]
    exact r3_d0 (a + h + 1) 0 (h + 2)
  have t := r3_chain (h + 2) (a + h + 2) 2
  rw [show (a + h + 2) + (h + 2) = a + 2 * h + 4 from by ring,
      show 2 + 2 * (h + 2) = 2 * h + 6 from by ring] at t; exact t

theorem nonhalt : ¬halts fm c₀ := by
  refine progress_nonhalt (fm := fm)
    (P := fun q ↦ ∃ a h, q = (⟨a+h+1, 2*h, 0, 0, 0⟩ : Q)) ?_ ⟨0, 0, rfl⟩
  intro q ⟨a, h, hq⟩; subst hq
  refine ⟨⟨a+2*h+4, 2*h+6, 0, 0, 0⟩, ⟨a+h, h+3, ?_⟩, main_step a h⟩
  show (a+2*h+4, 2*h+6, 0, 0, 0) = ((a+h)+(h+3)+1, 2*(h+3), 0, 0, 0)
  congr 1; ring

end Sz22_2003_unofficial_410
