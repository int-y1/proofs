import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #998: [4/15, 33/14, 845/2, 7/11, 33/13]

Vector representation:
```
 2 -1 -1  0  0  0
-1  1  0 -1  1  0
-1  0  1  0  0  2
 0  0  0  1 -1  0
 0  1  0  0  1 -1
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_998

def Q := ℕ × ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a, b+1, c+1, d, e, f⟩ => some ⟨a+2, b, c, d, e, f⟩
  | ⟨a+1, b, c, d+1, e, f⟩ => some ⟨a, b+1, c, d, e+1, f⟩
  | ⟨a+1, b, c, d, e, f⟩ => some ⟨a, b, c+1, d, e, f+2⟩
  | ⟨a, b, c, d, e+1, f⟩ => some ⟨a, b, c, d+1, e, f⟩
  | ⟨a, b, c, d, e, f+1⟩ => some ⟨a, b+1, c, d, e+1, f⟩
  | _ => none

theorem r3_chain : ∀ k, ∀ c e f, ⟨k, 0, c, 0, e, f⟩ [fm]⊢* ⟨0, 0, c + k, 0, e, f + 2 * k⟩ := by
  intro k; induction' k with k ih <;> intro c e f
  · exists 0
  · rw [show (k : ℕ) + 1 = k + 1 from rfl]
    step fm
    apply stepStar_trans (ih (c + 1) e (f + 2))
    ring_nf; finish

theorem r4_chain : ∀ k, ∀ c d f, ⟨0, 0, c, d, k, f⟩ [fm]⊢* ⟨0, 0, c, d + k, 0, f⟩ := by
  intro k; induction' k with k ih <;> intro c d f
  · exists 0
  · rw [show (k : ℕ) + 1 = k + 1 from rfl]
    step fm
    apply stepStar_trans (ih c (d + 1) f)
    ring_nf; finish

theorem r2r1_chain : ∀ k, ∀ a c d e f,
    ⟨a + 1, 0, c + k, d + k, e, f⟩ [fm]⊢* ⟨a + 1 + k, 0, c, d, e + k, f⟩ := by
  intro k; induction' k with k ih <;> intro a c d e f
  · ring_nf; finish
  · rw [show c + (k + 1) = (c + k) + 1 from by ring,
        show d + (k + 1) = (d + k) + 1 from by ring,
        show (k : ℕ) + 1 = k + 1 from rfl]
    step fm; step fm
    apply stepStar_trans (ih (a + 1) c d (e + 1) f)
    ring_nf; finish

theorem main_trans (n : ℕ) :
    ⟨n + 1, 0, 0, 0, n, n * n⟩ [fm]⊢⁺ ⟨n + 2, 0, 0, 0, n + 1, (n + 1) * (n + 1)⟩ := by
  have h1 : ⟨n + 1, 0, 0, 0, n, n * n⟩ [fm]⊢* ⟨0, 0, n + 1, 0, n, n * n + 2 * (n + 1)⟩ := by
    have := r3_chain (n + 1) 0 n (n * n)
    convert this using 2; ring_nf
  have h2 : ⟨0, 0, n + 1, 0, n, n * n + 2 * (n + 1)⟩ [fm]⊢* ⟨0, 0, n + 1, n, 0, n * n + 2 * (n + 1)⟩ := by
    have := r4_chain n (n + 1) 0 (n * n + 2 * (n + 1))
    convert this using 2; ring_nf
  have h3 : ⟨0, 0, n + 1, n, 0, n * n + 2 * (n + 1)⟩ [fm]⊢⁺
      ⟨2, 0, n, n, 1, n * n + 2 * n + 1⟩ := by
    rw [show n * n + 2 * (n + 1) = (n * n + 2 * n + 1) + 1 from by ring]
    step fm; step fm; finish
  have h4 : ⟨2, 0, n, n, 1, n * n + 2 * n + 1⟩ [fm]⊢*
      ⟨n + 2, 0, 0, 0, n + 1, n * n + 2 * n + 1⟩ := by
    have := r2r1_chain n 1 0 0 1 (n * n + 2 * n + 1)
    convert this using 2; ring_nf
  have h5 : n * n + 2 * n + 1 = (n + 1) * (n + 1) := by ring
  exact stepStar_stepPlus_stepPlus h1
    (stepStar_stepPlus_stepPlus h2
      (stepPlus_stepStar_stepPlus h3
        (h5 ▸ h4)))

theorem nonhalt : ¬halts fm c₀ := by
  apply progress_nonhalt_simple (fm := fm) (A := ℕ)
    (fun n ↦ ⟨n + 1, 0, 0, 0, n, n * n⟩) 0
  intro n
  exact ⟨n + 1, main_trans n⟩
