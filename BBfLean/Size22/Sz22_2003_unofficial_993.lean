import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #993: [4/15, 33/14, 65/2, 7/11, 99/13]

Vector representation:
```
 2 -1 -1  0  0  0
-1  1  0 -1  1  0
-1  0  1  0  0  1
 0  0  0  1 -1  0
 0  2  0  0  1 -1
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_993

def Q := ℕ × ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a, b+1, c+1, d, e, f⟩ => some ⟨a+2, b, c, d, e, f⟩
  | ⟨a+1, b, c, d+1, e, f⟩ => some ⟨a, b+1, c, d, e+1, f⟩
  | ⟨a+1, b, c, d, e, f⟩ => some ⟨a, b, c+1, d, e, f+1⟩
  | ⟨a, b, c, d, e+1, f⟩ => some ⟨a, b, c, d+1, e, f⟩
  | ⟨a, b, c, d, e, f+1⟩ => some ⟨a, b+2, c, d, e+1, f⟩
  | _ => none

theorem r4_chain : ∀ k, ∀ c d f, ⟨0, 0, c, d, k, f⟩ [fm]⊢* ⟨0, 0, c, d + k, 0, f⟩ := by
  intro k; induction' k with k ih <;> intro c d f
  · exists 0
  · rw [show (k : ℕ) + 1 = k + 1 from rfl]
    step fm
    apply stepStar_trans (ih c (d + 1) f)
    ring_nf; finish

theorem r3_chain : ∀ k, ∀ c e f, ⟨k, 0, c, 0, e, f⟩ [fm]⊢* ⟨0, 0, c + k, 0, e, f + k⟩ := by
  intro k; induction' k with k ih <;> intro c e f
  · exists 0
  · rw [show (k : ℕ) + 1 = k + 1 from rfl]
    step fm
    apply stepStar_trans (ih (c + 1) e (f + 1))
    ring_nf; finish

theorem r2r1_chain : ∀ k, ∀ a c e f,
    ⟨a + 1, 0, c + k, k, e, f⟩ [fm]⊢* ⟨a + 1 + k, 0, c, 0, e + k, f⟩ := by
  intro k; induction' k with k ih <;> intro a c e f
  · ring_nf; finish
  · rw [show c + (k + 1) = (c + k) + 1 from by ring,
        show (k : ℕ) + 1 = k + 1 from rfl]
    step fm; step fm
    apply stepStar_trans (ih (a + 1) c (e + 1) f)
    ring_nf; finish

theorem main_trans (n g : ℕ) :
    ⟨0, 0, 2 * n + 3, 0, n + 1, g + 4⟩ [fm]⊢⁺ ⟨0, 0, 2 * (n + 1) + 3, 0, (n + 1) + 1, (g + n + 4) + 4⟩ := by
  have h1 : ⟨0, 0, 2 * n + 3, 0, n + 1, g + 4⟩ [fm]⊢* ⟨0, 0, 2 * n + 3, n + 1, 0, g + 4⟩ := by
    have := r4_chain (n + 1) (2 * n + 3) 0 (g + 4)
    rw [show 0 + (n + 1) = n + 1 from by ring] at this; exact this
  have h2 : ⟨0, 0, 2 * n + 3, n + 1, 0, g + 4⟩ [fm]⊢⁺ ⟨0, 2, 2 * n + 3, n + 1, 1, g + 3⟩ := by
    rw [show g + 4 = (g + 3) + 1 from by ring]
    step fm; finish
  have h3 : ⟨0, 2, 2 * n + 3, n + 1, 1, g + 3⟩ [fm]⊢* ⟨4, 0, 2 * n + 1, n + 1, 1, g + 3⟩ := by
    rw [show (2 : ℕ) = 1 + 1 from by ring, show 2 * n + 3 = (2 * n + 1) + 1 + 1 from by ring]
    step fm; step fm; ring_nf; finish
  have h4 : ⟨4, 0, 2 * n + 1, n + 1, 1, g + 3⟩ [fm]⊢* ⟨n + 5, 0, n, 0, n + 2, g + 3⟩ := by
    have := r2r1_chain (n + 1) 3 n 1 (g + 3)
    rw [show n + (n + 1) = 2 * n + 1 from by ring,
        show 3 + 1 = 4 from by ring,
        show 3 + 1 + (n + 1) = n + 5 from by ring,
        show 1 + (n + 1) = n + 2 from by ring] at this
    exact this
  have h5 : ⟨n + 5, 0, n, 0, n + 2, g + 3⟩ [fm]⊢* ⟨0, 0, n + (n + 5), 0, n + 2, g + 3 + (n + 5)⟩ := by
    exact r3_chain (n + 5) n (n + 2) (g + 3)
  have heq1 : n + (n + 5) = 2 * (n + 1) + 3 := by ring
  have heq2 : g + 3 + (n + 5) = (g + n + 4) + 4 := by ring
  have heq3 : n + 2 = (n + 1) + 1 := by ring
  exact stepStar_stepPlus_stepPlus h1
    (stepPlus_stepStar_stepPlus h2
      (stepStar_trans h3
        (stepStar_trans h4
          (heq1 ▸ heq2 ▸ heq3 ▸ h5))))

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨0, 0, 3, 0, 1, 4⟩) (by execute fm 8)
  apply progress_nonhalt_simple (fm := fm) (A := ℕ × ℕ)
    (fun ⟨n, g⟩ ↦ ⟨0, 0, 2 * n + 3, 0, n + 1, g + 4⟩) ⟨0, 0⟩
  intro ⟨n, g⟩
  refine ⟨⟨n + 1, g + n + 4⟩, ?_⟩
  exact main_trans n g
