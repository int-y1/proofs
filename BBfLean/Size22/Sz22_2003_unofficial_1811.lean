import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #1811: [9/10, 55/21, 2/3, 7/11, 495/2]

Vector representation:
```
-1  2 -1  0  0
 0 -1  1 -1  1
 1 -1  0  0  0
 0  0  0  1 -1
-1  2  1  0  1
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_1811

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a+1, b, c+1, d, e⟩ => some ⟨a, b+2, c, d, e⟩
  | ⟨a, b+1, c, d+1, e⟩ => some ⟨a, b, c+1, d, e+1⟩
  | ⟨a, b+1, c, d, e⟩ => some ⟨a+1, b, c, d, e⟩
  | ⟨a, b, c, d, e+1⟩ => some ⟨a, b, c, d+1, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b+2, c+1, d, e+1⟩
  | _ => none

theorem r1r2_chain : ∀ k b e, ∀ a d,
    ⟨a + k, b, 1, d + k, e⟩ [fm]⊢* ⟨a, b + k, 1, d, e + k⟩ := by
  intro k; induction' k with k ih <;> intro b e a d
  · exists 0
  · show ⟨(a + k) + 1, b, 1, (d + k) + 1, e⟩ [fm]⊢* ⟨a, b + (k + 1), 1, d, e + (k + 1)⟩
    apply stepStar_trans
      (step_stepStar (show (⟨(a + k) + 1, b, 0 + 1, (d + k) + 1, e⟩ : Q) [fm]⊢
          ⟨a + k, b + 2, 0, (d + k) + 1, e⟩ from by simp [fm]))
    apply stepStar_trans
      (step_stepStar (show (⟨a + k, (b + 1) + 1, 0, (d + k) + 1, e⟩ : Q) [fm]⊢
          ⟨a + k, b + 1, 1, d + k, e + 1⟩ from by simp [fm]))
    apply stepStar_trans (ih (b + 1) (e + 1) a d)
    ring_nf; finish

theorem r3_chain : ∀ k a e, ∀ b,
    ⟨a, b + k, 0, 0, e⟩ [fm]⊢* ⟨a + k, b, 0, 0, e⟩ := by
  intro k; induction' k with k ih <;> intro a e b
  · exists 0
  · show ⟨a, (b + k) + 1, 0, 0, e⟩ [fm]⊢* ⟨a + (k + 1), b, 0, 0, e⟩
    apply stepStar_trans
      (step_stepStar (show (⟨a, (b + k) + 1, 0, 0, e⟩ : Q) [fm]⊢
          ⟨a + 1, b + k, 0, 0, e⟩ from by simp [fm]))
    apply stepStar_trans (ih (a + 1) e b)
    ring_nf; finish

theorem r4_chain : ∀ k a e, ∀ d,
    ⟨a, 0, 0, d, e + k⟩ [fm]⊢* ⟨a, 0, 0, d + k, e⟩ := by
  intro k; induction' k with k ih <;> intro a e d
  · exists 0
  · show ⟨a, 0, 0, d, (e + k) + 1⟩ [fm]⊢* ⟨a, 0, 0, d + (k + 1), e⟩
    apply stepStar_trans
      (step_stepStar (show (⟨a, 0, 0, d, (e + k) + 1⟩ : Q) [fm]⊢
          ⟨a, 0, 0, d + 1, e + k⟩ from by simp [fm]))
    apply stepStar_trans (ih a e (d + 1))
    ring_nf; finish

theorem main_trans : ∀ n,
    ⟨2 * n + 3, 0, 0, n + 1, 0⟩ [fm]⊢⁺ ⟨2 * n + 5, 0, 0, n + 2, 0⟩ := by
  intro n
  rw [show 2 * n + 3 = (2 * n + 2) + 1 from by ring]
  step fm
  apply stepStar_trans (show ⟨2 * n + 2, 2, 1, n + 1, 1⟩ [fm]⊢*
      ⟨n + 1, n + 3, 1, 0, n + 2⟩ from by
    have h := r1r2_chain (n + 1) 2 1 (n + 1) 0
    rw [Nat.zero_add] at h
    convert h using 2; ring_nf)
  rw [show (n + 3 : ℕ) = (n + 2) + 1 from by ring,
      show (n + 1 : ℕ) = n + 0 + 1 from by ring]
  step fm
  apply stepStar_trans (show ⟨n, n + 5, 0, 0, n + 2⟩ [fm]⊢*
      ⟨2 * n + 5, 0, 0, 0, n + 2⟩ from by
    have h := r3_chain (n + 5) n (n + 2) 0
    rw [Nat.zero_add] at h
    convert h using 2; ring_nf)
  have h := r4_chain (n + 2) (2 * n + 5) 0 0
  rw [Nat.zero_add] at h
  exact h

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨3, 0, 0, 1, 0⟩) (by execute fm 7)
  apply progress_nonhalt_simple (fm := fm) (A := ℕ)
    (fun n ↦ ⟨2 * n + 3, 0, 0, n + 1, 0⟩) 0
  intro n; exists n + 1; exact main_trans n
