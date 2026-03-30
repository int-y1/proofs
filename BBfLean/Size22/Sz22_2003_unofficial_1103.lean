import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #1103: [5/6, 4/35, 539/2, 1/5, 3/11, 5/7]

Vector representation:
```
-1 -1  1  0  0
 2  0 -1 -1  0
-1  0  0  2  1
 0  0 -1  0  0
 0  1  0  0 -1
 0  0  1 -1  0
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_1103

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a+1, b+1, c, d, e⟩ => some ⟨a, b, c+1, d, e⟩
  | ⟨a, b, c+1, d+1, e⟩ => some ⟨a+2, b, c, d, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b, c, d+2, e+1⟩
  | ⟨a, b, c+1, d, e⟩ => some ⟨a, b, c, d, e⟩
  | ⟨a, b, c, d, e+1⟩ => some ⟨a, b+1, c, d, e⟩
  | ⟨a, b, c, d+1, e⟩ => some ⟨a, b, c+1, d, e⟩
  | _ => none

-- R3 chain: (a+k, 0, 0, d, e) →* (a, 0, 0, d+2k, e+k)
theorem r3_chain : ∀ k d e, ⟨a + k, 0, 0, d, e⟩ [fm]⊢* ⟨a, 0, 0, d + 2 * k, e + k⟩ := by
  intro k; induction' k with k ih <;> intro d e
  · exists 0
  · rw [show a + (k + 1) = (a + k) + 1 from by ring]
    step fm
    apply stepStar_trans (ih (d + 2) (e + 1))
    ring_nf; finish

-- R5 chain: (0, b, 0, d, e+k) →* (0, b+k, 0, d, e)
theorem r5_chain : ∀ k b e, ⟨0, b, 0, d, e + k⟩ [fm]⊢* ⟨0, b + k, 0, d, e⟩ := by
  intro k; induction' k with k ih <;> intro b e
  · exists 0
  · rw [show e + (k + 1) = (e + k) + 1 from by ring]
    step fm
    apply stepStar_trans (ih (b + 1) e)
    ring_nf; finish

-- 3-step round (R1, R1, R2) repeated k times:
-- (2, b+2k, c, d+k, 0) →* (2, b, c+k, d, 0)
theorem r1r1r2_chain : ∀ k b c d, ⟨2, b + 2 * k, c, d + k, 0⟩ [fm]⊢* ⟨2, b, c + k, d, 0⟩ := by
  intro k; induction' k with k ih <;> intro b c d
  · exists 0
  · rw [show b + 2 * (k + 1) = (b + 2 * k) + 2 from by ring,
        show d + (k + 1) = (d + k) + 1 from by ring]
    step fm; step fm; step fm
    apply stepStar_trans (ih b (c + 1) d)
    ring_nf; finish

-- R2 chain: (a, 0, c+k, d+k, 0) →* (a+2k, 0, c, d, 0)
theorem r2_chain : ∀ k a c d, ⟨a, 0, c + k, d + k, 0⟩ [fm]⊢* ⟨a + 2 * k, 0, c, d, 0⟩ := by
  intro k; induction' k with k ih <;> intro a c d
  · exists 0
  · rw [show c + (k + 1) = (c + k) + 1 from by ring,
        show d + (k + 1) = (d + k) + 1 from by ring]
    step fm
    apply stepStar_trans (ih (a + 2) c d)
    ring_nf; finish

-- Main transition: (2n+5, 0, 0, n^2+2n, 0) →⁺ (2n+7, 0, 0, n^2+4n+3, 0)
theorem main_trans (n : ℕ) :
    ⟨2 * n + 5, 0, 0, n * n + 2 * n, 0⟩ [fm]⊢⁺
    ⟨2 * n + 7, 0, 0, n * n + 4 * n + 3, 0⟩ := by
  have h1 : ⟨2 * n + 5, 0, 0, n * n + 2 * n, 0⟩ [fm]⊢*
      ⟨0, 0, 0, n * n + 6 * n + 10, 2 * n + 5⟩ := by
    rw [show 2 * n + 5 = 0 + (2 * n + 5) from by ring]
    apply stepStar_trans (r3_chain (2 * n + 5) (n * n + 2 * n) 0)
    ring_nf; finish
  have h2 : ⟨0, 0, 0, n * n + 6 * n + 10, 2 * n + 5⟩ [fm]⊢*
      ⟨0, 2 * n + 5, 0, n * n + 6 * n + 10, 0⟩ := by
    rw [show 2 * n + 5 = 0 + (2 * n + 5) from by ring]
    apply stepStar_trans (r5_chain (2 * n + 5) 0 0)
    ring_nf; finish
  have h3 : ⟨0, 2 * n + 5, 0, n * n + 6 * n + 10, 0⟩ [fm]⊢⁺
      ⟨2, 2 * n + 5, 0, n * n + 6 * n + 8, 0⟩ := by
    rw [show n * n + 6 * n + 10 = (n * n + 6 * n + 9) + 1 from by ring]
    step fm
    rw [show n * n + 6 * n + 9 = (n * n + 6 * n + 8) + 1 from by ring]
    step fm
    finish
  have h4 : ⟨2, 2 * n + 5, 0, n * n + 6 * n + 8, 0⟩ [fm]⊢*
      ⟨2, 1, n + 2, n * n + 5 * n + 6, 0⟩ := by
    rw [show 2 * n + 5 = 1 + 2 * (n + 2) from by ring,
        show n * n + 6 * n + 8 = (n * n + 5 * n + 6) + (n + 2) from by ring]
    apply stepStar_trans (r1r1r2_chain (n + 2) 1 0 (n * n + 5 * n + 6))
    ring_nf; finish
  have h5 : ⟨2, 1, n + 2, n * n + 5 * n + 6, 0⟩ [fm]⊢⁺
      ⟨1, 0, n + 3, n * n + 5 * n + 6, 0⟩ := by
    rw [show (2 : ℕ) = 1 + 1 from by ring,
        show (1 : ℕ) = 0 + 1 from by ring,
        show n + 3 = (n + 2) + 1 from by ring]
    step fm; finish
  have h6 : ⟨1, 0, n + 3, n * n + 5 * n + 6, 0⟩ [fm]⊢*
      ⟨2 * n + 7, 0, 0, n * n + 4 * n + 3, 0⟩ := by
    rw [show n + 3 = 0 + (n + 3) from by ring,
        show n * n + 5 * n + 6 = (n * n + 4 * n + 3) + (n + 3) from by ring]
    apply stepStar_trans (r2_chain (n + 3) 1 0 (n * n + 4 * n + 3))
    ring_nf; finish
  exact stepStar_stepPlus_stepPlus h1
    (stepStar_stepPlus_stepPlus h2
      (stepPlus_stepStar_stepPlus h3
        (stepStar_trans h4
          (stepStar_trans (stepPlus_stepStar h5) h6))))

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨5, 0, 0, 0, 0⟩)
  · execute fm 20
  apply progress_nonhalt_simple (fm := fm) (A := ℕ)
    (fun n ↦ ⟨2 * n + 5, 0, 0, n * n + 2 * n, 0⟩) 0
  intro n; exists n + 1
  rw [show 2 * (n + 1) + 5 = 2 * n + 7 from by ring,
      show (n + 1) * (n + 1) + 2 * (n + 1) = n * n + 4 * n + 3 from by ring]
  exact main_trans n

end Sz22_2003_unofficial_1103
