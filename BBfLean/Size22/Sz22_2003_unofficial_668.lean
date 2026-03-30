import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #668: [35/6, 28/55, 121/2, 3/7, 35/11]

Vector representation:
```
-1 -1  1  1  0
 2  0 -1  1 -1
-1  0  0  0  2
 0  1  0 -1  0
 0  0  1  1 -1
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_668

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a+1, b+1, c, d, e⟩ => some ⟨a, b, c+1, d+1, e⟩
  | ⟨a, b, c+1, d, e+1⟩ => some ⟨a+2, b, c, d+1, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b, c, d, e+2⟩
  | ⟨a, b, c, d+1, e⟩ => some ⟨a, b+1, c, d, e⟩
  | ⟨a, b, c, d, e+1⟩ => some ⟨a, b, c+1, d+1, e⟩
  | _ => none

-- R3 repeated: (a+k, 0, 0, d, e) →* (a, 0, 0, d, e+2*k).
theorem a_to_e : ∀ k, ⟨a + k, 0, 0, d, e⟩ [fm]⊢* ⟨a, 0, 0, d, e + 2 * k⟩ := by
  intro k; induction' k with k ih generalizing a d e
  · exists 0
  · rw [show a + (k + 1) = (a + k) + 1 from by ring]
    step fm
    apply stepStar_trans (ih (e := e + 2))
    ring_nf; finish

-- R4 repeated: (0, b, 0, d+k, e) →* (0, b+k, 0, d, e).
theorem d_to_b : ∀ k, ⟨0, b, 0, d + k, e⟩ [fm]⊢* ⟨0, b + k, 0, d, e⟩ := by
  intro k; induction' k with k ih generalizing b d e
  · exists 0
  · rw [show d + (k + 1) = (d + k) + 1 from by ring]
    step fm
    apply stepStar_trans (ih (b := b + 1))
    ring_nf; finish

-- R2 repeated: (a, 0, c+k, d, k) →* (a+2*k, 0, c, d+k, 0).
theorem r2_chain : ∀ k, ⟨a, 0, c + k, d, k⟩ [fm]⊢* ⟨a + 2 * k, 0, c, d + k, 0⟩ := by
  intro k; induction' k with k ih generalizing a c d
  · exists 0
  · rw [show c + (k + 1) = (c + k) + 1 from by ring]
    step fm
    apply stepStar_trans (ih (a := a + 2) (d := d + 1))
    ring_nf; finish

-- 3-step cycle (R2, R1, R1) repeated k times.
-- (0, 2k, c+1, d, c+2k+1) →* (0, 0, c+k+1, d+3k, c+k+1).
theorem r2r1r1_chain : ∀ k c d, ⟨0, 2 * k, c + 1, d, c + 2 * k + 1⟩ [fm]⊢*
    ⟨0, 0, c + k + 1, d + 3 * k, c + k + 1⟩ := by
  intro k; induction' k with k ih <;> intro c d
  · exists 0
  · rw [show c + 2 * (k + 1) + 1 = (c + 2 * k + 2) + 1 from by ring,
        show 2 * (k + 1) = (2 * k + 1) + 1 from by ring]
    step fm
    show ⟨2, (2 * k + 1) + 1, c, d + 1, c + 2 * k + 2⟩ [fm]⊢* _
    rw [show (2 : ℕ) = 1 + 1 from by ring,
        show c + 2 * k + 2 = c + 2 * k + 2 from rfl]
    step fm
    show ⟨1, 2 * k + 1, c + 1, d + 2, c + 2 * k + 2⟩ [fm]⊢* _
    rw [show (1 : ℕ) = 0 + 1 from by ring,
        show 2 * k + 1 = (2 * k) + 1 from by ring]
    step fm
    show ⟨0, 2 * k, c + 2, d + 3, c + 2 * k + 2⟩ [fm]⊢* _
    rw [show c + 2 = (c + 1) + 1 from by ring,
        show c + 2 * k + 2 = (c + 1) + 2 * k + 1 from by ring]
    apply stepStar_trans (ih (c + 1) (d + 3))
    ring_nf; finish

-- Main transition: (n+2, 0, 0, 2n+2, 0) ⊢⁺ (2n+4, 0, 0, 4n+6, 0).
theorem main_trans : ⟨n + 2, 0, 0, 2 * n + 2, 0⟩ [fm]⊢⁺ ⟨2 * n + 4, 0, 0, 4 * n + 6, 0⟩ := by
  have phase1 : ⟨n + 2, 0, 0, 2 * n + 2, 0⟩ [fm]⊢* ⟨0, 0, 0, 2 * n + 2, 2 * n + 4⟩ := by
    rw [show n + 2 = 0 + (n + 2) from by ring]
    apply stepStar_trans (a_to_e (n + 2) (a := 0) (d := 2 * n + 2) (e := 0))
    ring_nf; finish
  have phase2 : ⟨0, 0, 0, 2 * n + 2, 2 * n + 4⟩ [fm]⊢* ⟨0, 2 * n + 2, 0, 0, 2 * n + 4⟩ := by
    rw [show 2 * n + 2 = 0 + (2 * n + 2) from by ring]
    apply stepStar_trans (d_to_b (2 * n + 2) (b := 0) (d := 0) (e := 2 * n + 4))
    ring_nf; finish
  have phase3a : ⟨0, 2 * n + 2, 0, 0, 2 * n + 4⟩ [fm]⊢ ⟨0, 2 * n + 2, 1, 1, 2 * n + 3⟩ := by
    show (fm : FM) ⟨0, 2 * n + 2, 0, 0, (2 * n + 3) + 1⟩ = some _
    simp [fm]
  have phase3b : ⟨0, 2 * n + 2, 1, 1, 2 * n + 3⟩ [fm]⊢ ⟨2, 2 * n + 2, 0, 2, 2 * n + 2⟩ := by
    show (fm : FM) ⟨0, 2 * n + 2, 0 + 1, 1, (2 * n + 2) + 1⟩ = some ⟨0 + 2, 2 * n + 2, 0, 1 + 1, 2 * n + 2⟩
    simp [fm]
  have phase3c : ⟨2, 2 * n + 2, 0, 2, 2 * n + 2⟩ [fm]⊢ ⟨1, 2 * n + 1, 1, 3, 2 * n + 2⟩ := by
    show (fm : FM) ⟨1 + 1, (2 * n + 1) + 1, 0, 2, 2 * n + 2⟩ = some ⟨1, 2 * n + 1, 0 + 1, 2 + 1, 2 * n + 2⟩
    simp [fm]
  have phase3d : ⟨1, 2 * n + 1, 1, 3, 2 * n + 2⟩ [fm]⊢ ⟨0, 2 * n, 2, 4, 2 * n + 2⟩ := by
    show (fm : FM) ⟨0 + 1, (2 * n) + 1, 1, 3, 2 * n + 2⟩ = some ⟨0, 2 * n, 1 + 1, 3 + 1, 2 * n + 2⟩
    simp [fm]
  have phase4 : ⟨0, 2 * n, 2, 4, 2 * n + 2⟩ [fm]⊢* ⟨0, 0, n + 2, 3 * n + 4, n + 2⟩ := by
    rw [show (2 : ℕ) = 1 + 1 from by ring,
        show 2 * n + 2 = 1 + 2 * n + 1 from by ring]
    apply stepStar_trans (r2r1r1_chain n 1 4)
    ring_nf; finish
  have phase5 : ⟨0, 0, n + 2, 3 * n + 4, n + 2⟩ [fm]⊢* ⟨2 * n + 4, 0, 0, 4 * n + 6, 0⟩ := by
    have := r2_chain (n + 2) (a := 0) (c := 0) (d := 3 * n + 4)
    simp only [Nat.zero_add] at this
    apply stepStar_trans this
    ring_nf; finish
  apply stepStar_stepPlus_stepPlus (stepStar_trans phase1 phase2)
  apply step_stepStar_stepPlus phase3a
  apply stepStar_trans (step_stepStar phase3b)
  apply stepStar_trans (step_stepStar phase3c)
  apply stepStar_trans (step_stepStar phase3d)
  apply stepStar_trans phase4
  exact phase5

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨2, 0, 0, 2, 0⟩) (by execute fm 3)
  apply progress_nonhalt_simple (fm := fm) (A := ℕ)
    (fun n ↦ ⟨n + 2, 0, 0, 2 * n + 2, 0⟩) 0
  intro n; exists 2 * n + 2
  show ⟨n + 2, 0, 0, 2 * n + 2, 0⟩ [fm]⊢⁺ ⟨(2 * n + 2) + 2, 0, 0, 2 * (2 * n + 2) + 2, 0⟩
  rw [show (2 * n + 2) + 2 = 2 * n + 4 from by ring,
      show 2 * (2 * n + 2) + 2 = 4 * n + 6 from by ring]
  exact main_trans
