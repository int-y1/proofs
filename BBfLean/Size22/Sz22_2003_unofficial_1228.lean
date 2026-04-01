import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #1228: [5/6, 572/35, 77/2, 3/13, 65/11]

Vector representation:
```
-1 -1  1  0  0  0
 2  0 -1 -1  1  1
-1  0  0  1  1  0
 0  1  0  0  0 -1
 0  0  1  0 -1  1
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_1228

def Q := ℕ × ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a+1, b+1, c, d, e, f⟩ => some ⟨a, b, c+1, d, e, f⟩
  | ⟨a, b, c+1, d+1, e, f⟩ => some ⟨a+2, b, c, d, e+1, f+1⟩
  | ⟨a+1, b, c, d, e, f⟩ => some ⟨a, b, c, d+1, e+1, f⟩
  | ⟨a, b, c, d, e, f+1⟩ => some ⟨a, b+1, c, d, e, f⟩
  | ⟨a, b, c, d, e+1, f⟩ => some ⟨a, b, c+1, d, e, f+1⟩
  | _ => none

-- R3 chain: drain a, adding to d and e
theorem r3_chain : ∀ k, ∀ d e f,
    ⟨k, (0 : ℕ), 0, d, e, f⟩ [fm]⊢* ⟨(0 : ℕ), (0 : ℕ), 0, d + k, e + k, f⟩ := by
  intro k; induction' k with k ih
  · intro d e f; exists 0
  · intro d e f
    step fm
    apply stepStar_trans (ih (d + 1) (e + 1) f)
    ring_nf; finish

-- R4 chain: drain f to b
theorem f_to_b : ∀ k, ∀ b d e,
    ⟨(0 : ℕ), b, 0, d, e, k⟩ [fm]⊢* ⟨(0 : ℕ), b + k, 0, d, e, 0⟩ := by
  intro k; induction' k with k ih
  · intro b d e; exists 0
  · intro b d e
    step fm
    apply stepStar_trans (ih (b + 1) d e)
    ring_nf; finish

-- R2-R1-R1 chain: k rounds
theorem r2r1r1_chain : ∀ k, ∀ c d e f,
    ⟨(0 : ℕ), 2 * k, c + 1, d + k, e, f⟩ [fm]⊢*
    ⟨(0 : ℕ), (0 : ℕ), c + k + 1, d, e + k, f + k⟩ := by
  intro k; induction' k with k ih
  · intro c d e f; simp; exists 0
  · intro c d e f
    rw [show 2 * (k + 1) = 2 * k + 2 from by ring,
        show d + (k + 1) = d + k + 1 from by ring]
    step fm; step fm; step fm
    rw [show c + 2 = (c + 1) + 1 from by ring]
    apply stepStar_trans (ih (c + 1) d (e + 1) (f + 1))
    ring_nf; finish

-- R3-R2 chain: k rounds
theorem r3r2_chain : ∀ k, ∀ a c e f,
    ⟨a + 2, (0 : ℕ), c + k, 0, e, f⟩ [fm]⊢*
    ⟨a + 2 + k, (0 : ℕ), c, 0, e + 2 * k, f + k⟩ := by
  intro k; induction' k with k ih
  · intro a c e f; simp; exists 0
  · intro a c e f
    rw [show c + (k + 1) = (c + k) + 1 from by ring]
    step fm
    rw [show (c + k) + 1 = c + k + 1 from by ring]
    step fm
    rw [show a + 3 = (a + 1) + 2 from by ring]
    apply stepStar_trans (ih (a + 1) c (e + 2) (f + 1))
    ring_nf; finish

-- Canonical state: (n+2, 0, 0, 0, (n+1)*(2*n+1), 2*n+2)
theorem main_transition (n : ℕ) :
    ⟨n + 2, (0 : ℕ), 0, 0, (n + 1) * (2 * n + 1), 2 * n + 2⟩ [fm]⊢⁺
    ⟨n + 3, (0 : ℕ), 0, 0, (n + 2) * (2 * n + 3), 2 * n + 4⟩ := by
  -- Phase 1: R3 x(n+2): drain a
  apply stepStar_stepPlus_stepPlus (r3_chain (n + 2) 0 ((n + 1) * (2 * n + 1)) (2 * n + 2))
  rw [show (0 : ℕ) + (n + 2) = n + 2 from by ring,
      show (n + 1) * (2 * n + 1) + (n + 2) = 2 * n * n + 4 * n + 3 from by ring]
  -- State: (0, 0, 0, n+2, 2n^2+4n+3, 2n+2)
  -- Phase 2: R4 x(2n+2): move f to b
  apply stepStar_stepPlus_stepPlus (f_to_b (2 * n + 2) 0 (n + 2) (2 * n * n + 4 * n + 3))
  rw [show (0 : ℕ) + (2 * n + 2) = 2 * n + 2 from by ring]
  -- State: (0, 2n+2, 0, n+2, 2n^2+4n+3, 0)
  -- Phase 3: R5
  rw [show 2 * n * n + 4 * n + 3 = (2 * n * n + 4 * n + 2) + 1 from by ring]
  apply step_stepStar_stepPlus
    (by simp [fm] : (⟨0, 2 * n + 2, 0, n + 2, (2 * n * n + 4 * n + 2) + 1, 0⟩ : Q) [fm]⊢
      ⟨0, 2 * n + 2, 1, n + 2, 2 * n * n + 4 * n + 2, 1⟩)
  -- State: (0, 2n+2, 1, n+2, 2n^2+4n+2, 1)
  -- Phase 4: R2-R1-R1 x(n+1)
  rw [show 2 * n + 2 = 2 * (n + 1) from by ring,
      show (1 : ℕ) = 0 + 1 from by ring,
      show n + 2 = 1 + (n + 1) from by ring]
  apply stepStar_trans (r2r1r1_chain (n + 1) 0 1 (2 * n * n + 4 * n + 2) 1)
  rw [show 0 + (n + 1) + 1 = n + 2 from by ring,
      show (2 * n * n + 4 * n + 2) + (n + 1) = 2 * n * n + 5 * n + 3 from by ring,
      show 1 + (n + 1) = n + 2 from by ring]
  -- State: (0, 0, n+2, 1, 2n^2+5n+3, n+2)
  -- Phase 5: R2
  rw [show n + 2 = (n + 1) + 1 from by ring,
      show (1 : ℕ) = 0 + 1 from by ring]
  apply stepStar_trans (step_stepStar
    (by simp [fm] : (⟨0, 0, (n + 1) + 1, 0 + 1, 2 * n * n + 5 * n + 3, n + 2⟩ : Q) [fm]⊢
      ⟨2, 0, n + 1, 0, 2 * n * n + 5 * n + 4, n + 3⟩))
  -- State: (2, 0, n+1, 0, 2n^2+5n+4, n+3)
  -- Phase 6: R3-R2 x(n+1)
  rw [show (2 : ℕ) = 0 + 2 from by ring,
      show n + 1 = 0 + (n + 1) from by ring]
  apply stepStar_trans (r3r2_chain (n + 1) 0 0 (2 * n * n + 5 * n + 4) (n + 3))
  rw [show 0 + 2 + (n + 1) = n + 3 from by ring,
      show (2 * n * n + 5 * n + 4) + 2 * (n + 1) = (n + 2) * (2 * n + 3) from by ring,
      show (n + 3) + (n + 1) = 2 * n + 4 from by ring]
  ring_nf; finish

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨2, 0, 0, 0, 1, 2⟩) (by execute fm 3)
  apply progress_nonhalt_simple (fm := fm) (A := ℕ)
    (fun n ↦ ⟨n + 2, 0, 0, 0, (n + 1) * (2 * n + 1), 2 * n + 2⟩) 0
  intro n; exists n + 1
  rw [show (n + 1) + 2 = n + 3 from by ring,
      show (n + 1 + 1) * (2 * (n + 1) + 1) = (n + 2) * (2 * n + 3) from by ring,
      show 2 * (n + 1) + 2 = 2 * n + 4 from by ring]
  exact main_transition n

end Sz22_2003_unofficial_1228
