import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #1744: [8/15, 33/14, 715/2, 7/11, 2/13]

Vector representation:
```
 3 -1 -1  0  0  0
-1  1  0 -1  1  0
-1  0  1  0  1  1
 0  0  0  1 -1  0
 1  0  0  0  0 -1
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_1744

def Q := ℕ × ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a, b+1, c+1, d, e, f⟩ => some ⟨a+3, b, c, d, e, f⟩
  | ⟨a+1, b, c, d+1, e, f⟩ => some ⟨a, b+1, c, d, e+1, f⟩
  | ⟨a+1, b, c, d, e, f⟩ => some ⟨a, b, c+1, d, e+1, f+1⟩
  | ⟨a, b, c, d, e+1, f⟩ => some ⟨a, b, c, d+1, e, f⟩
  | ⟨a, b, c, d, e, f+1⟩ => some ⟨a+1, b, c, d, e, f⟩
  | _ => none

theorem r3_chain : ∀ k a c e f, ⟨a + k, 0, c, 0, e, f⟩ [fm]⊢*
    ⟨a, 0, c + k, 0, e + k, f + k⟩ := by
  intro k; induction' k with k ih <;> intro a c e f
  · exists 0
  · rw [show a + (k + 1) = (a + k) + 1 from by ring]
    step fm
    apply stepStar_trans (ih a (c + 1) (e + 1) (f + 1))
    ring_nf; finish

theorem r4_chain : ∀ k c d f, ⟨0, 0, c, d, k, f⟩ [fm]⊢* ⟨0, 0, c, d + k, 0, f⟩ := by
  intro k; induction' k with k ih <;> intro c d f
  · exists 0
  · rw [show d + (k + 1) = (d + 1) + k from by ring]
    step fm
    apply stepStar_trans (ih c (d + 1) f)
    ring_nf; finish

theorem r2r1_chain : ∀ k a c d e, ⟨a + 1, 0, c + k, d + k, e, f⟩ [fm]⊢*
    ⟨a + 1 + 2 * k, 0, c, d, e + k, f⟩ := by
  intro k; induction' k with k ih <;> intro a c d e
  · exists 0
  · rw [show c + (k + 1) = (c + k) + 1 from by ring,
        show d + (k + 1) = (d + k) + 1 from by ring]
    step fm
    step fm
    rw [show a + 1 + 2 * (k + 1) = (a + 2) + 1 + 2 * k from by ring]
    apply stepStar_trans (ih (a + 2) c d (e + 1))
    ring_nf; finish

theorem r2_chain : ∀ k a b d e, ⟨a + k, b, 0, d + k, e, f⟩ [fm]⊢*
    ⟨a, b + k, 0, d, e + k, f⟩ := by
  intro k; induction' k with k ih <;> intro a b d e
  · exists 0
  · rw [show a + (k + 1) = (a + k) + 1 from by ring,
        show d + (k + 1) = (d + k) + 1 from by ring,
        show b + (k + 1) = b + 1 + k from by ring,
        show e + (k + 1) = e + 1 + k from by ring]
    exact stepStar_trans (step_stepStar (by simp [fm])) (ih a (b + 1) d (e + 1))

theorem r3r1_step (a b e f : ℕ) :
    (⟨a + 1, b + 1, 0, 0, e, f⟩ : Q) [fm]⊢* ⟨a + 3, b, 0, 0, e + 1, f + 1⟩ :=
  stepStar_trans (step_stepStar (by simp [fm] : (⟨a + 1, b + 1, 0, 0, e, f⟩ : Q) [fm]⊢
    ⟨a, b + 1, 1, 0, e + 1, f + 1⟩))
    (step_stepStar (by simp [fm] : (⟨a, b + 1, 1, 0, e + 1, f + 1⟩ : Q) [fm]⊢
    ⟨a + 3, b, 0, 0, e + 1, f + 1⟩))

theorem r3r1_chain : ∀ k a e f, ⟨a + 1, b + k, 0, 0, e, f⟩ [fm]⊢*
    ⟨a + 1 + 2 * k, b, 0, 0, e + k, f + k⟩ := by
  intro k; induction' k with k ih <;> intro a e f
  · exists 0
  · rw [show b + (k + 1) = (b + k) + 1 from by ring,
        show a + 1 + 2 * (k + 1) = (a + 2) + 1 + 2 * k from by ring,
        show e + (k + 1) = e + 1 + k from by ring,
        show f + (k + 1) = f + 1 + k from by ring]
    exact stepStar_trans (r3r1_step a (b + k) e f) (ih (a + 2) (e + 1) (f + 1))

theorem main_trans (F n : ℕ) :
    (⟨F + 2 * n + 3, 0, 0, 0, F + n + 1, F⟩ : Q) [fm]⊢⁺
    (⟨3 * F + 5 * n + 8, 0, 0, 0, 3 * F + 4 * n + 5, 3 * F + 3 * n + 3⟩ : Q) := by
  apply step_stepStar_stepPlus
    (show (⟨F + 2 * n + 3, 0, 0, 0, F + n + 1, F⟩ : Q) [fm]⊢
      ⟨F + 2 * n + 2, 0, 1, 0, F + n + 2, F + 1⟩ by simp [fm])
  rw [show F + 2 * n + 2 = 0 + (F + 2 * n + 2) from by ring]
  apply stepStar_trans (r3_chain (F + 2 * n + 2) 0 1 (F + n + 2) (F + 1))
  rw [show 1 + (F + 2 * n + 2) = F + 2 * n + 3 from by ring,
      show F + n + 2 + (F + 2 * n + 2) = 2 * F + 3 * n + 4 from by ring,
      show F + 1 + (F + 2 * n + 2) = 2 * F + 2 * n + 3 from by ring]
  apply stepStar_trans (r4_chain (2 * F + 3 * n + 4) (F + 2 * n + 3) 0 (2 * F + 2 * n + 3))
  rw [show 0 + (2 * F + 3 * n + 4) = 2 * F + 3 * n + 4 from by ring,
      show 2 * F + 2 * n + 3 = (2 * F + 2 * n + 2) + 1 from by ring]
  step fm
  rw [show F + 2 * n + 3 = 0 + (F + 2 * n + 3) from by ring,
      show 2 * F + 3 * n + 4 = (F + n + 1) + (F + 2 * n + 3) from by ring]
  apply stepStar_trans (r2r1_chain (F + 2 * n + 3) 0 0 (F + n + 1) 0
    (f := 2 * F + 2 * n + 2))
  simp only [Nat.zero_add]
  rw [show 1 + 2 * (F + 2 * n + 3) = (F + 3 * n + 6) + (F + n + 1) from by ring]
  rw [show (⟨(F + 3 * n + 6) + (F + n + 1), 0, 0, F + n + 1, F + 2 * n + 3, 2 * F + 2 * n + 2⟩ : Q) =
    ⟨(F + 3 * n + 6) + (F + n + 1), 0, 0, 0 + (F + n + 1), F + 2 * n + 3, 2 * F + 2 * n + 2⟩
    from by simp]
  apply stepStar_trans (r2_chain (F + n + 1) (F + 3 * n + 6) 0 0 (F + 2 * n + 3)
    (f := 2 * F + 2 * n + 2))
  simp only [Nat.zero_add]
  rw [show F + 2 * n + 3 + (F + n + 1) = 2 * F + 3 * n + 4 from by ring,
      show F + 3 * n + 6 = (F + 3 * n + 5) + 1 from by ring]
  rw [show (⟨(F + 3 * n + 5) + 1, F + n + 1, 0, 0, 2 * F + 3 * n + 4, 2 * F + 2 * n + 2⟩ : Q) =
    ⟨(F + 3 * n + 5) + 1, 0 + (F + n + 1), 0, 0, 2 * F + 3 * n + 4, 2 * F + 2 * n + 2⟩
    from by simp]
  apply stepStar_trans (r3r1_chain (F + n + 1) (F + 3 * n + 5) (2 * F + 3 * n + 4)
    (2 * F + 2 * n + 2) (b := 0))
  ring_nf; finish

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := (⟨3, 0, 0, 0, 1, 0⟩ : Q))
  · execute fm 5
  apply progress_nonhalt_simple (fm := fm) (A := ℕ × ℕ)
    (fun ⟨F, n⟩ ↦ ⟨F + 2 * n + 3, 0, 0, 0, F + n + 1, F⟩) ⟨0, 0⟩
  intro ⟨F, n⟩
  refine ⟨⟨3 * F + 3 * n + 3, n + 1⟩, ?_⟩
  show (⟨F + 2 * n + 3, 0, 0, 0, F + n + 1, F⟩ : Q) [fm]⊢⁺
    ⟨3 * F + 3 * n + 3 + 2 * (n + 1) + 3, 0, 0, 0,
     3 * F + 3 * n + 3 + (n + 1) + 1, 3 * F + 3 * n + 3⟩
  rw [show 3 * F + 3 * n + 3 + 2 * (n + 1) + 3 = 3 * F + 5 * n + 8 from by ring,
      show 3 * F + 3 * n + 3 + (n + 1) + 1 = 3 * F + 4 * n + 5 from by ring]
  exact main_trans F n

end Sz22_2003_unofficial_1744
