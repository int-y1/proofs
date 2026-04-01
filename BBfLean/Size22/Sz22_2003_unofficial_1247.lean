import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #1247: [5/6, 77/2, 52/35, 3/13, 15/11]

Vector representation:
```
-1 -1  1  0  0  0
-1  0  0  1  1  0
 2  0 -1 -1  0  1
 0  1  0  0  0 -1
 0  1  1  0 -1  0
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_1247

def Q := ℕ × ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a+1, b+1, c, d, e, f⟩ => some ⟨a, b, c+1, d, e, f⟩
  | ⟨a+1, b, c, d, e, f⟩ => some ⟨a, b, c, d+1, e+1, f⟩
  | ⟨a, b, c+1, d+1, e, f⟩ => some ⟨a+2, b, c, d, e, f+1⟩
  | ⟨a, b, c, d, e, f+1⟩ => some ⟨a, b+1, c, d, e, f⟩
  | ⟨a, b, c, d, e+1, f⟩ => some ⟨a, b+1, c+1, d, e, f⟩
  | _ => none

-- R4 repeated: drain f into b
theorem f_to_b : ∀ k b d e f, ⟨(0 : ℕ), b, 0, d, e, f + k⟩ [fm]⊢* ⟨(0 : ℕ), b + k, 0, d, e, f⟩ := by
  intro k; induction' k with k ih
  · intro b d e f; exists 0
  · intro b d e f
    rw [Nat.add_succ f k]
    step fm
    apply stepStar_trans (ih (b + 1) d e f)
    ring_nf; finish

-- R3+R1+R1 chain: n rounds
theorem r3r1r1_chain : ∀ k, ∀ b c d e f, ⟨(0 : ℕ), b + 2 * k, c + 1, d + k, e, f⟩ [fm]⊢* ⟨(0 : ℕ), b, c + 1 + k, d, e, f + k⟩ := by
  intro k; induction' k with k ih
  · intro b c d e f; exists 0
  · intro b c d e f
    rw [show b + 2 * (k + 1) = (b + 2) + 2 * k from by ring,
        show d + (k + 1) = (d + 1) + k from by ring]
    apply stepStar_trans (ih (b + 2) c (d + 1) e f)
    rw [show c + 1 + k = (c + k) + 1 from by ring,
        show d + 1 = d + 1 from rfl]
    step fm
    step fm
    step fm
    rw [show c + k + 2 = c + 1 + (k + 1) from by ring,
        show f + k + 1 = f + (k + 1) from by ring]
    finish

-- R3+R2+R2 chain: k rounds
theorem r3r2r2_chain : ∀ k, ∀ c d e f, ⟨(0 : ℕ), 0, c + k, d + 1, e, f⟩ [fm]⊢* ⟨(0 : ℕ), 0, c, d + 1 + k, e + 2 * k, f + k⟩ := by
  intro k; induction' k with k ih
  · intro c d e f; exists 0
  · intro c d e f
    rw [show c + (k + 1) = c + k + 1 from by ring,
        show d + 1 = d + 1 from rfl]
    step fm
    step fm
    step fm
    rw [show d + 1 + 1 = (d + 1) + 1 from by ring]
    apply stepStar_trans (ih c (d + 1) (e + 2) (f + 1))
    ring_nf; finish

-- Main transition: C(n) →⁺ C(n+1)
-- C(n) = (0, 0, 0, n+1, n²+n+1, 2n)
theorem main_trans (n : ℕ) :
    ⟨(0 : ℕ), 0, 0, n + 1, n * n + n + 1, 2 * n⟩ [fm]⊢⁺
    ⟨(0 : ℕ), 0, 0, n + 2, n * n + 3 * n + 3, 2 * n + 2⟩ := by
  -- Phase 1: R4 x 2n: drain f into b
  rw [show (2 * n : ℕ) = 0 + (2 * n) from by ring]
  apply stepStar_stepPlus_stepPlus (f_to_b (2 * n) 0 (n + 1) (n * n + n + 1) 0)
  rw [show (0 : ℕ) + 2 * n = 2 * n from by ring]
  -- State: (0, 2n, 0, n+1, n²+n+1, 0)
  -- Phase 2: R5 once
  rw [show n * n + n + 1 = (n * n + n) + 1 from by ring]
  apply step_stepStar_stepPlus (by simp [fm] : (⟨0, 2 * n, 0, n + 1, (n * n + n) + 1, 0⟩ : Q) [fm]⊢ ⟨0, 2 * n + 1, 1, n + 1, n * n + n, 0⟩)
  -- State: (0, 2n+1, 1, n+1, n²+n, 0)
  -- Phase 3: R3+R1+R1 x n rounds
  rw [show 2 * n + 1 = 1 + 2 * n from by ring,
      show n + 1 = 1 + n from by ring]
  apply stepStar_trans (r3r1r1_chain n 1 0 1 (n * n + n) 0)
  rw [show (0 : ℕ) + 1 + n = n + 1 from by ring,
      show (0 : ℕ) + n = n from by ring]
  -- State: (0, 1, n+1, 1, n²+n, n)
  -- Phase 4: R3
  apply stepStar_trans (step_stepStar (by simp [fm] : (⟨0, 1, n + 1, 1, n * n + n, n⟩ : Q) [fm]⊢ ⟨2, 1, n, 0, n * n + n, n + 1⟩))
  -- Phase 5: R1
  apply stepStar_trans (step_stepStar (by simp [fm] : (⟨2, 1, n, 0, n * n + n, n + 1⟩ : Q) [fm]⊢ ⟨1, 0, n + 1, 0, n * n + n, n + 1⟩))
  -- Phase 6: R2
  apply stepStar_trans (step_stepStar (by simp [fm] : (⟨1, 0, n + 1, 0, n * n + n, n + 1⟩ : Q) [fm]⊢ ⟨0, 0, n + 1, 1, n * n + n + 1, n + 1⟩))
  -- State: (0, 0, n+1, 1, n²+n+1, n+1)
  -- Phase 7: R3+R2+R2 x (n+1) rounds
  have h7 := r3r2r2_chain (n + 1) 0 0 (n * n + n + 1) (n + 1)
  simp only [Nat.zero_add] at h7
  apply stepStar_trans h7
  ring_nf; finish

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨0, 0, 0, 2, 3, 2⟩) (by execute fm 8)
  apply progress_nonhalt_simple (fm := fm) (A := ℕ)
    (fun n ↦ ⟨0, 0, 0, n + 2, (n + 1) * (n + 1) + (n + 1) + 1, 2 * (n + 1)⟩) 0
  intro n; exists n + 1
  rw [show (n + 1) + 2 = n + 2 + 1 from by ring]
  rw [show (n + 2) * (n + 2) + (n + 2) + 1 = (n + 1) * (n + 1) + 3 * (n + 1) + 3 from by ring,
      show 2 * (n + 2) = 2 * (n + 1) + 2 from by ring]
  show ⟨(0 : ℕ), 0, 0, (n + 1) + 1, (n + 1) * (n + 1) + (n + 1) + 1, 2 * (n + 1)⟩ [fm]⊢⁺
       ⟨(0 : ℕ), 0, 0, (n + 1) + 2, (n + 1) * (n + 1) + 3 * (n + 1) + 3, 2 * (n + 1) + 2⟩
  exact main_trans (n + 1)

end Sz22_2003_unofficial_1247
