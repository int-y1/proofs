import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #1297: [63/10, 121/2, 2/33, 5/7, 20/11]

Vector representation:
```
-1  2 -1  1  0
-1  0  0  0  2
 1 -1  0  0 -1
 0  0  1 -1  0
 2  0  1  0 -1
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_1297

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a+1, b, c+1, d, e⟩ => some ⟨a, b+2, c, d+1, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b, c, d, e+2⟩
  | ⟨a, b+1, c, d, e+1⟩ => some ⟨a+1, b, c, d, e⟩
  | ⟨a, b, c, d+1, e⟩ => some ⟨a, b, c+1, d, e⟩
  | ⟨a, b, c, d, e+1⟩ => some ⟨a+2, b, c+1, d, e⟩
  | _ => none

-- R4 chain: (0, 0, c, d+k, e) →* (0, 0, c+k, d, e)
theorem r4_chain : ∀ k c d e, ⟨0, 0, c, d + k, e⟩ [fm]⊢* ⟨0, 0, c + k, d, e⟩ := by
  intro k; induction' k with k ih <;> intro c d e
  · exists 0
  · rw [show d + (k + 1) = (d + k) + 1 from by ring]
    step fm
    apply stepStar_trans (ih (c + 1) d e)
    ring_nf; finish

-- R1 chain: (a+k, b, c+k, d, e) →* (a, b+2*k, c, d+k, e)
theorem r1_chain : ∀ k a b c d e, ⟨a + k, b, c + k, d, e⟩ [fm]⊢* ⟨a, b + 2 * k, c, d + k, e⟩ := by
  intro k; induction' k with k ih <;> intro a b c d e
  · exists 0
  · rw [show a + (k + 1) = (a + k) + 1 from by ring,
        show c + (k + 1) = (c + k) + 1 from by ring]
    step fm
    apply stepStar_trans (ih a (b + 2) c (d + 1) e)
    ring_nf; finish

-- (R3-R1) chain: (0, b+1, c+k, d, e+1+k) →* (0, b+1+k, c, d+k, e+1)
theorem r3r1_chain : ∀ k b c d e, ⟨0, b + 1, c + k, d, e + 1 + k⟩ [fm]⊢* ⟨0, b + 1 + k, c, d + k, e + 1⟩ := by
  intro k; induction' k with k ih <;> intro b c d e
  · exists 0
  · rw [show c + (k + 1) = (c + k) + 1 from by ring,
        show e + 1 + (k + 1) = (e + 1 + k) + 1 from by ring]
    step fm; step fm
    apply stepStar_trans (ih (b + 1) c (d + 1) e)
    ring_nf; finish

-- (R3-R2) drain: (0, b+1+k, 0, d, e+1) →* (0, b+1, 0, d, e+1+k)
theorem r3r2_drain : ∀ k b d e, ⟨0, b + 1 + k, 0, d, e + 1⟩ [fm]⊢* ⟨0, b + 1, 0, d, e + 1 + k⟩ := by
  intro k; induction' k with k ih <;> intro b d e
  · exists 0
  · rw [show b + 1 + (k + 1) = (b + 1 + k) + 1 from by ring]
    step fm
    rw [show e + 1 = (e + 1 + 0) from by ring]
    step fm
    apply stepStar_trans (ih b d (e + 1))
    ring_nf; finish

-- Main transition: (0, 0, 0, m+1, 3*m+5) ⊢⁺ (0, 0, 0, m+2, 3*m+8)
theorem main_trans (m : ℕ) : ⟨0, 0, 0, m + 1, 3 * m + 5⟩ [fm]⊢⁺ ⟨0, 0, 0, m + 2, 3 * m + 8⟩ := by
  have phase1 : ⟨0, 0, 0, m + 1, 3 * m + 5⟩ [fm]⊢* ⟨0, 0, m + 1, 0, 3 * m + 5⟩ := by
    have := r4_chain (m + 1) 0 0 (3 * m + 5)
    simp at this; exact this
  have phase2 : ⟨0, 0, m + 1, 0, 3 * m + 5⟩ [fm]⊢⁺ ⟨2, 0, m + 2, 0, 3 * m + 4⟩ := by
    rw [show 3 * m + 5 = (3 * m + 4) + 1 from by ring]
    step fm; finish
  have phase3a : ⟨2, 0, m + 2, 0, 3 * m + 4⟩ [fm]⊢* ⟨0, 4, m, 2, 3 * m + 4⟩ := by
    have := r1_chain 2 0 0 m 0 (3 * m + 4)
    simp at this; exact this
  have phase3b : ⟨0, 4, m, 2, 3 * m + 4⟩ [fm]⊢* ⟨0, m + 4, 0, m + 2, 2 * m + 4⟩ := by
    have h := r3r1_chain m 3 0 2 (2 * m + 3)
    rw [show 3 + 1 = (4 : ℕ) from by ring,
        show 0 + m = m from by ring,
        show 2 * m + 3 + 1 + m = 3 * m + 4 from by ring,
        show 3 + 1 + m = m + 4 from by ring,
        show 2 + m = m + 2 from by ring,
        show 2 * m + 3 + 1 = 2 * m + 4 from by ring] at h
    exact h
  have phase4 : ⟨0, m + 4, 0, m + 2, 2 * m + 4⟩ [fm]⊢* ⟨0, 1, 0, m + 2, 3 * m + 7⟩ := by
    rw [show m + 4 = 0 + 1 + (m + 3) from by ring,
        show 2 * m + 4 = (2 * m + 3) + 1 from by ring]
    apply stepStar_trans (r3r2_drain (m + 3) 0 (m + 2) (2 * m + 3))
    ring_nf; finish
  have phase5 : ⟨0, 1, 0, m + 2, 3 * m + 7⟩ [fm]⊢⁺ ⟨0, 0, 0, m + 2, 3 * m + 8⟩ := by
    rw [show 3 * m + 7 = (3 * m + 6) + 1 from by ring]
    step fm; step fm
    rw [show 3 * m + 6 + 2 = 3 * m + 8 from by ring]
    finish
  exact stepStar_stepPlus_stepPlus phase1
    (stepPlus_trans phase2
      (stepStar_stepPlus_stepPlus phase3a
        (stepStar_stepPlus_stepPlus phase3b
          (stepStar_stepPlus_stepPlus phase4 phase5))))

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨0, 0, 0, 1, 5⟩)
  · execute fm 8
  apply progress_nonhalt_simple (fm := fm) (A := ℕ)
    (fun n ↦ ⟨0, 0, 0, n + 1, 3 * n + 5⟩) 0
  intro n; exists n + 1
  exact main_trans n
