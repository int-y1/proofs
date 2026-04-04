import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #1766: [9/10, 22/21, 49/2, 5/121, 10/7]

Vector representation:
```
-1  2 -1  0  0
 1 -1  0 -1  1
-1  0  0  2  0
 0  0  1  0 -2
 1  0  1 -1  0
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_1766

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a+1, b, c+1, d, e⟩ => some ⟨a, b+2, c, d, e⟩
  | ⟨a, b+1, c, d+1, e⟩ => some ⟨a+1, b, c, d, e+1⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b, c, d+2, e⟩
  | ⟨a, b, c, d, e+2⟩ => some ⟨a, b, c+1, d, e⟩
  | ⟨a, b, c, d+1, e⟩ => some ⟨a+1, b, c+1, d, e⟩
  | _ => none

theorem a_to_d : ∀ k d e, ⟨k, 0, 0, d, e⟩ [fm]⊢* ⟨0, 0, 0, d + 2 * k, e⟩ := by
  intro k; induction' k with k ih <;> intro d e
  · exists 0
  · step fm
    apply stepStar_trans (ih (d + 2) e)
    ring_nf; finish

theorem e_to_c : ∀ k c d, ⟨0, 0, c, d, 2 * k⟩ [fm]⊢* ⟨0, 0, c + k, d, 0⟩ := by
  intro k; induction' k with k ih <;> intro c d
  · exists 0
  · rw [show 2 * (k + 1) = 2 * k + 2 from by ring]
    step fm
    apply stepStar_trans (ih (c + 1) d)
    ring_nf; finish

theorem spiral : ∀ k b e, ⟨1, b, k, k, e⟩ [fm]⊢* ⟨1, b + k, 0, 0, e + k⟩ := by
  intro k; induction' k with k ih <;> intro b e
  · exists 0
  · step fm
    step fm
    apply stepStar_trans (ih (b + 1) (e + 1))
    ring_nf; finish

theorem drain : ∀ k a b e, ⟨a + 1, b + 2 * k, 0, 0, e⟩ [fm]⊢* ⟨a + k + 1, b, 0, 0, e + 2 * k⟩ := by
  intro k; induction' k with k ih <;> intro a b e
  · exists 0
  · rw [show b + 2 * (k + 1) = b + 2 * k + 2 from by ring,
        show a + 1 = (a + 1) from rfl]
    step fm
    step fm
    step fm
    rw [show a + 1 + 1 = (a + 1) + 1 from by ring]
    apply stepStar_trans (ih (a + 1) b (e + 2))
    ring_nf; finish

theorem r5_step : ⟨0, 0, c, d + 1, 0⟩ [fm]⊢* ⟨1, 0, c + 1, d, 0⟩ := by
  step fm; finish

theorem half1 : ∀ n, ⟨n + 1, 0, 0, 0, 4 * n⟩ [fm]⊢* ⟨1, 2 * n + 1, 0, 0, 2 * n + 1⟩ := by
  intro n
  apply stepStar_trans (a_to_d (n + 1) 0 (4 * n))
  rw [show 0 + 2 * (n + 1) = 2 * (n + 1) from by ring,
      show 4 * n = 2 * (2 * n) from by ring]
  apply stepStar_trans (e_to_c (2 * n) 0 (2 * (n + 1)))
  rw [show 0 + 2 * n = 2 * n from by ring,
      show 2 * (n + 1) = (2 * n + 1) + 1 from by ring]
  apply stepStar_trans r5_step
  apply stepStar_trans (spiral (2 * n + 1) 0 0)
  ring_nf; finish

theorem half2 : ∀ n, ⟨n + 1, 0, 0, 1, 4 * n + 2⟩ [fm]⊢* ⟨1, 2 * n + 2, 0, 0, 2 * n + 2⟩ := by
  intro n
  apply stepStar_trans (a_to_d (n + 1) 1 (4 * n + 2))
  rw [show 1 + 2 * (n + 1) = 2 * n + 3 from by ring,
      show 4 * n + 2 = 2 * (2 * n + 1) from by ring]
  apply stepStar_trans (e_to_c (2 * n + 1) 0 (2 * n + 3))
  rw [show 0 + (2 * n + 1) = 2 * n + 1 from by ring,
      show 2 * n + 3 = (2 * n + 2) + 1 from by ring]
  apply stepStar_trans r5_step
  apply stepStar_trans (spiral (2 * n + 2) 0 0)
  ring_nf; finish

theorem odd_drain : ∀ n, ⟨1, 2 * n + 1, 0, 0, 2 * n + 1⟩ [fm]⊢* ⟨n + 1, 1, 0, 0, 4 * n + 1⟩ := by
  intro n
  rw [show (1 : ℕ) = 0 + 1 from by ring,
      show 2 * n + 1 = 1 + 2 * n from by ring]
  apply stepStar_trans (drain n 0 1 (1 + 2 * n))
  rw [show 0 + n + 1 = n + 1 from by ring,
      show 1 + 2 * n + 2 * n = 4 * n + 1 from by ring]
  finish

theorem r3r2_step : ⟨n + 1, 1, 0, 0, 4 * n + 1⟩ [fm]⊢⁺ ⟨n + 1, 0, 0, 1, 4 * n + 2⟩ := by
  step fm; step fm; finish

theorem even_drain : ∀ n, ⟨1, 2 * n + 2, 0, 0, 2 * n + 2⟩ [fm]⊢* ⟨n + 2, 0, 0, 0, 4 * n + 4⟩ := by
  intro n
  rw [show (1 : ℕ) = 0 + 1 from by ring,
      show 2 * n + 2 = 0 + 2 * (n + 1) from by ring]
  apply stepStar_trans (drain (n + 1) 0 0 (0 + 2 * (n + 1)))
  rw [show 0 + (n + 1) + 1 = n + 2 from by ring,
      show 0 + 2 * (n + 1) + 2 * (n + 1) = 4 * n + 4 from by ring]
  finish

theorem main_trans : ∀ n, ⟨n + 1, 0, 0, 0, 4 * n⟩ [fm]⊢⁺ ⟨n + 2, 0, 0, 0, 4 * (n + 1)⟩ := by
  intro n
  apply stepStar_stepPlus_stepPlus (half1 n)
  apply stepStar_stepPlus_stepPlus (odd_drain n)
  apply stepPlus_stepStar_stepPlus (r3r2_step)
  apply stepStar_trans (half2 n)
  apply stepStar_trans (even_drain n)
  show ⟨n + 2, 0, 0, 0, 4 * n + 4⟩ [fm]⊢* ⟨n + 2, 0, 0, 0, 4 * (n + 1)⟩
  rw [show 4 * n + 4 = 4 * (n + 1) from by ring]
  finish

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨2, 0, 0, 0, 4⟩) (by execute fm 16)
  apply progress_nonhalt_simple (fm := fm) (A := ℕ)
    (fun n ↦ ⟨n + 2, 0, 0, 0, 4 * (n + 1)⟩) 0
  intro n; exists n + 1
  exact main_trans (n + 1)
