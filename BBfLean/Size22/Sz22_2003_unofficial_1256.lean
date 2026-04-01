import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #1256: [5/6, 77/2, 572/35, 3/13, 65/11]

Vector representation:
```
-1 -1  1  0  0  0
-1  0  0  1  1  0
 2  0 -1 -1  1  1
 0  1  0  0  0 -1
 0  0  1  0 -1  1
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_1256

def Q := ℕ × ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a+1, b+1, c, d, e, f⟩ => some ⟨a, b, c+1, d, e, f⟩
  | ⟨a+1, b, c, d, e, f⟩ => some ⟨a, b, c, d+1, e+1, f⟩
  | ⟨a, b, c+1, d+1, e, f⟩ => some ⟨a+2, b, c, d, e+1, f+1⟩
  | ⟨a, b, c, d, e, f+1⟩ => some ⟨a, b+1, c, d, e, f⟩
  | ⟨a, b, c, d, e+1, f⟩ => some ⟨a, b, c+1, d, e, f+1⟩
  | _ => none

-- R4 repeated: drain f to b
theorem f_to_b : ∀ k b d e f, ⟨(0 : ℕ), b, 0, d, e, f + k⟩ [fm]⊢* ⟨0, b + k, 0, d, e, f⟩ := by
  intro k; induction' k with k ih <;> intro b d e f
  · exists 0
  · rw [show f + (k + 1) = (f + k) + 1 from by ring]
    step fm
    apply stepStar_trans (ih (b + 1) d e f)
    ring_nf; finish

-- R1R1R3 chain: each round does R1,R1,R3
theorem r1r1r3_chain : ∀ k b c d e f,
    ⟨(2 : ℕ), b + 2 * k, c, d + k, e, f⟩ [fm]⊢* ⟨2, b, c + k, d, e + k, f + k⟩ := by
  intro k; induction' k with k ih <;> intro b c d e f
  · exists 0
  · rw [show b + 2 * (k + 1) = (b + 2 * k) + 2 from by ring,
        show d + (k + 1) = (d + k) + 1 from by ring]
    step fm; step fm
    rw [show c + 2 = (c + 1) + 1 from by ring]
    step fm
    apply stepStar_trans (ih b (c + 1) d (e + 1) (f + 1))
    ring_nf; finish

-- R3R2R2 chain: each round does R3,R2,R2
theorem r3r2r2_chain : ∀ k c d e f,
    ⟨(0 : ℕ), 0, c + k, d + 1, e, f⟩ [fm]⊢* ⟨0, 0, c, d + 1 + k, e + 3 * k, f + k⟩ := by
  intro k; induction' k with k ih <;> intro c d e f
  · exists 0
  · rw [show c + (k + 1) = (c + k) + 1 from by ring]
    step fm; step fm; step fm
    rw [show d + 2 = (d + 1) + 1 from by ring]
    apply stepStar_trans (ih c (d + 1) (e + 3) (f + 1))
    ring_nf; finish

-- Main transition: (0, 0, 0, n+1, 2n²+1, 2n) →⁺ (0, 0, 0, n+2, 2n²+4n+3, 2n+2)
theorem main_trans (n : ℕ) :
    ⟨(0 : ℕ), 0, 0, n + 1, 2 * n * n + 1, 2 * n⟩ [fm]⊢⁺
    ⟨(0 : ℕ), 0, 0, n + 2, 2 * n * n + 4 * n + 3, 2 * n + 2⟩ := by
  -- Phase 1: R4 x (2n): drain f to b
  have phase1 : ⟨(0 : ℕ), 0, 0, n + 1, 2 * n * n + 1, 2 * n⟩ [fm]⊢*
      ⟨0, 2 * n, 0, n + 1, 2 * n * n + 1, 0⟩ := by
    have h := f_to_b (2 * n) 0 (n + 1) (2 * n * n + 1) 0
    simp only [Nat.zero_add] at h; exact h
  apply stepStar_stepPlus_stepPlus phase1
  -- State: (0, 2n, 0, n+1, 2n²+1, 0)
  -- Phase 2: R5
  apply step_stepStar_stepPlus
    (by simp [fm] : (⟨0, 2 * n, 0, n + 1, 2 * n * n + 1, 0⟩ : Q) [fm]⊢
      ⟨0, 2 * n, 1, n + 1, 2 * n * n, 1⟩)
  -- State: (0, 2n, 1, n+1, 2n², 1)
  -- Phase 3: R3
  rw [show (1 : ℕ) = 0 + 1 from by ring]
  apply stepStar_trans
    (step_stepStar (by simp [fm] : (⟨0, 2 * n, 0 + 1, n + 1, 2 * n * n, 1⟩ : Q) [fm]⊢
      ⟨2, 2 * n, 0, n, 2 * n * n + 1, 2⟩))
  -- State: (2, 2n, 0, n, 2n²+1, 2)
  -- Phase 4: R1R1R3 chain x n
  have phase4 : ⟨(2 : ℕ), 2 * n, 0, n, 2 * n * n + 1, 2⟩ [fm]⊢*
      ⟨2, 0, n, 0, 2 * n * n + n + 1, n + 2⟩ := by
    have h := r1r1r3_chain n 0 0 0 (2 * n * n + 1) 2
    simp only [Nat.zero_add] at h
    rw [show 2 * n * n + 1 + n = 2 * n * n + n + 1 from by ring,
        show 2 + n = n + 2 from by ring] at h
    exact h
  apply stepStar_trans phase4
  -- State: (2, 0, n, 0, 2n²+n+1, n+2)
  -- Phase 5: R2, R2
  step fm; step fm
  -- State: (0, 0, n, 2, 2n²+n+3, n+2)
  -- Phase 6: R3R2R2 chain x n
  have phase6 : ⟨(0 : ℕ), 0, n, 2, 2 * n * n + n + 3, n + 2⟩ [fm]⊢*
      ⟨0, 0, 0, n + 2, 2 * n * n + 4 * n + 3, 2 * n + 2⟩ := by
    have h := r3r2r2_chain n 0 1 (2 * n * n + n + 3) (n + 2)
    simp only [Nat.zero_add] at h
    rw [show 1 + 1 + n = n + 2 from by ring,
        show 2 * n * n + n + 3 + 3 * n = 2 * n * n + 4 * n + 3 from by ring,
        show n + 2 + n = 2 * n + 2 from by ring] at h
    exact h
  show ⟨(0 : ℕ), 0, n, 2, 2 * n * n + n + 3, n + 2⟩ [fm]⊢*
       ⟨0, 0, 0, n + 2, 2 * n * n + 4 * n + 3, 2 * n + 2⟩
  exact phase6

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨0, 0, 0, 1, 1, 0⟩) (by execute fm 1)
  apply progress_nonhalt_simple (fm := fm) (A := ℕ)
    (fun n ↦ ⟨0, 0, 0, n + 1, 2 * n * n + 1, 2 * n⟩) 0
  intro n; exists n + 1
  show ⟨(0 : ℕ), 0, 0, n + 1, 2 * n * n + 1, 2 * n⟩ [fm]⊢⁺
       ⟨(0 : ℕ), 0, 0, n + 1 + 1, 2 * (n + 1) * (n + 1) + 1, 2 * (n + 1)⟩
  have h := main_trans n
  rw [show 2 * n * n + 4 * n + 3 = 2 * (n + 1) * (n + 1) + 1 from by ring,
      show 2 * n + 2 = 2 * (n + 1) from by ring,
      show n + 2 = n + 1 + 1 from by ring] at h
  exact h

end Sz22_2003_unofficial_1256
