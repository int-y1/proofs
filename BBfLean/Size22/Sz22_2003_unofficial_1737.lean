import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #1737: [8/15, 33/14, 55/2, 7/11, 4/5]

Vector representation:
```
 3 -1 -1  0  0
-1  1  0 -1  1
-1  0  1  0  1
 0  0  0  1 -1
 2  0 -1  0  0
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_1737

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a, b+1, c+1, d, e⟩ => some ⟨a+3, b, c, d, e⟩
  | ⟨a+1, b, c, d+1, e⟩ => some ⟨a, b+1, c, d, e+1⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b, c+1, d, e+1⟩
  | ⟨a, b, c, d, e+1⟩ => some ⟨a, b, c, d+1, e⟩
  | ⟨a, b, c+1, d, e⟩ => some ⟨a+2, b, c, d, e⟩
  | _ => none

theorem r3_chain : ∀ k a c e, ⟨a + k, 0, c, 0, e⟩ [fm]⊢* ⟨a, 0, c + k, 0, e + k⟩ := by
  intro k; induction' k with k ih <;> intro a c e
  · exists 0
  · rw [show a + (k + 1) = a + k + 1 from by ring]
    step fm
    apply stepStar_trans (ih a (c + 1) (e + 1))
    ring_nf; finish

theorem r4_chain : ∀ k c d e, ⟨0, 0, c, d, e + k⟩ [fm]⊢* ⟨0, 0, c, d + k, e⟩ := by
  intro k; induction' k with k ih <;> intro c d e
  · exists 0
  · rw [show e + (k + 1) = e + k + 1 from by ring]
    step fm
    apply stepStar_trans (ih c (d + 1) e)
    ring_nf; finish

theorem r2r1_chain : ∀ k a d e,
    ⟨a + 1, 0, k, d + k, e⟩ [fm]⊢* ⟨a + 2 * k + 1, 0, 0, d, e + k⟩ := by
  intro k; induction' k with k ih <;> intro a d e
  · exists 0
  · rw [show d + (k + 1) = d + k + 1 from by ring]
    step fm; step fm
    rw [show a + 3 = (a + 2) + 1 from by ring]
    apply stepStar_trans (ih (a + 2) d (e + 1))
    ring_nf; finish

theorem r2_chain : ∀ k a b d e,
    ⟨a + k, b, 0, d + k, e⟩ [fm]⊢* ⟨a, b + k, 0, d, e + k⟩ := by
  intro k; induction' k with k ih <;> intro a b d e
  · exists 0
  · rw [show a + (k + 1) = a + k + 1 from by ring,
        show d + (k + 1) = d + k + 1 from by ring]
    step fm
    apply stepStar_trans (ih a (b + 1) d (e + 1))
    ring_nf; finish

theorem r3r1_chain : ∀ k a b e,
    ⟨a + 1, b + k + 1, 0, 0, e⟩ [fm]⊢* ⟨a + 2 * k + 3, b, 0, 0, e + k + 1⟩ := by
  intro k; induction' k with k ih <;> intro a b e
  · step fm; step fm; ring_nf; finish
  · rw [show b + (k + 1) + 1 = b + k + 1 + 1 from by ring]
    step fm; step fm
    rw [show a + 3 = (a + 2) + 1 from by ring]
    apply stepStar_trans (ih (a + 2) b (e + 1))
    ring_nf; finish

theorem phases_12 (n : ℕ) : ⟨n + 1, 0, 0, 0, n⟩ [fm]⊢⁺ ⟨2, 0, n, 2 * n + 1, 0⟩ := by
  apply stepStar_stepPlus_stepPlus
  · rw [show n + 1 = 0 + (n + 1) from by ring]
    exact r3_chain (n + 1) 0 0 n
  rw [show 0 + (n + 1) = n + 1 from by ring,
      show n + (n + 1) = 0 + (2 * n + 1) from by ring]
  apply stepStar_step_stepPlus (r4_chain (2 * n + 1) (n + 1) 0 0)
  rw [show 0 + (2 * n + 1) = 2 * n + 1 from by ring]
  simp [fm]

theorem phase_3a (n : ℕ) : ⟨2, 0, n, 2 * n + 1, 0⟩ [fm]⊢* ⟨2 * n + 2, 0, 0, n + 1, n⟩ := by
  have h := r2r1_chain n 1 (n + 1) 0
  simp only [show 1 + 2 * n + 1 = 2 * n + 2 from by ring,
             show (n + 1) + n = 2 * n + 1 from by ring,
             show 0 + n = n from by ring,
             show 1 + 1 = 2 from by ring] at h
  exact h

theorem phase_3b (n : ℕ) : ⟨2 * n + 2, 0, 0, n + 1, n⟩ [fm]⊢* ⟨n + 1, n + 1, 0, 0, 2 * n + 1⟩ := by
  have h := r2_chain (n + 1) (n + 1) 0 0 n
  simp only [show (n + 1) + (n + 1) = 2 * n + 2 from by ring,
             show 0 + (n + 1) = n + 1 from by ring,
             show n + (n + 1) = 2 * n + 1 from by ring] at h
  exact h

theorem phase_3c (n : ℕ) : ⟨n + 1, n + 1, 0, 0, 2 * n + 1⟩ [fm]⊢* ⟨3 * n + 3, 0, 0, 0, 3 * n + 2⟩ := by
  have h := r3r1_chain n n 0 (2 * n + 1)
  simp only [show n + 2 * n + 3 = 3 * n + 3 from by ring,
             show 2 * n + 1 + n + 1 = 3 * n + 2 from by ring,
             show 0 + n + 1 = n + 1 from by ring] at h
  exact h

theorem main_trans (n : ℕ) : ⟨n + 1, 0, 0, 0, n⟩ [fm]⊢⁺ ⟨3 * n + 3, 0, 0, 0, 3 * n + 2⟩ :=
  stepPlus_stepStar_stepPlus (phases_12 n)
    (stepStar_trans (phase_3a n) (stepStar_trans (phase_3b n) (phase_3c n)))

theorem nonhalt : ¬halts fm c₀ := by
  apply progress_nonhalt_simple (fm := fm) (A := ℕ)
    (fun n ↦ ⟨n + 1, 0, 0, 0, n⟩) 0
  intro n; exact ⟨3 * n + 2, main_trans n⟩
