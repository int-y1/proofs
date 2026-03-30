import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #670: [35/6, 28/55, 121/2, 3/7, 6/11]

Vector representation:
```
-1 -1  1  1  0
 2  0 -1  1 -1
-1  0  0  0  2
 0  1  0 -1  0
 1  1  0  0 -1
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_670

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a+1, b+1, c, d, e⟩ => some ⟨a, b, c+1, d+1, e⟩
  | ⟨a, b, c+1, d, e+1⟩ => some ⟨a+2, b, c, d+1, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b, c, d, e+2⟩
  | ⟨a, b, c, d+1, e⟩ => some ⟨a, b+1, c, d, e⟩
  | ⟨a, b, c, d, e+1⟩ => some ⟨a+1, b+1, c, d, e⟩
  | _ => none

-- R3 chain: drain a to e.
theorem r3_chain : ∀ k, ⟨a + k, 0, 0, d, e⟩ [fm]⊢* ⟨a, 0, 0, d, e + 2 * k⟩ := by
  intro k; induction' k with k ih generalizing a d e
  · exists 0
  · rw [show a + (k + 1) = (a + k) + 1 from by ring]
    step fm
    apply stepStar_trans (ih (a := a) (e := e + 2))
    ring_nf; finish

-- R4 chain: drain d to b.
theorem r4_chain : ∀ k, ⟨0, b, 0, d + k, e⟩ [fm]⊢* ⟨0, b + k, 0, d, e⟩ := by
  intro k; induction' k with k ih generalizing b d e
  · exists 0
  · rw [show d + (k + 1) = (d + k) + 1 from by ring]
    step fm
    apply stepStar_trans (ih (b := b + 1))
    ring_nf; finish

-- R5 + R1 + R2 opening: 3 steps.
theorem r5_r1_r2 : ⟨0, b, 0, 0, b + 2⟩ [fm]⊢* ⟨2, b, 0, 2, b⟩ := by
  step fm; step fm; step fm; finish

-- 3-step round chain (R1, R1, R2 interleaved).
theorem round3 : ∀ k, ⟨2, b + 2 * k, c, d, e + k⟩ [fm]⊢* ⟨2, b, c + k, d + 3 * k, e⟩ := by
  intro k; induction' k with k ih generalizing b c d e
  · exists 0
  · rw [show b + 2 * (k + 1) = (b + 2 * k) + 2 from by ring,
        show e + (k + 1) = (e + k) + 1 from by ring]
    step fm; step fm; step fm
    apply stepStar_trans (ih (c := c + 1) (d := d + 3))
    ring_nf; finish

-- R2 drain: with b = 0, drain c and e together.
theorem r2_drain : ∀ k, ⟨a, 0, k, d, k⟩ [fm]⊢* ⟨a + 2 * k, 0, 0, d + k, 0⟩ := by
  intro k; induction' k with k ih generalizing a d
  · exists 0
  · rw [show (k + 1 : ℕ) = k + 1 from rfl]
    step fm
    apply stepStar_trans (ih (a := a + 2) (d := d + 1))
    ring_nf; finish

-- Phases 1+2: (a, 0, 0, d, 0) →* (0, d, 0, 0, 2*a)
theorem phase12 (a d : ℕ) : ⟨a, 0, 0, d, 0⟩ [fm]⊢* ⟨0, d, 0, 0, 2 * a⟩ := by
  apply stepStar_trans
  · rw [show a = 0 + a from by ring]
    exact r3_chain a (a := 0) (d := d) (e := 0)
  rw [show 0 + 2 * a = 2 * a from by ring,
      show d = 0 + d from by ring]
  exact r4_chain d (b := 0) (d := 0) (e := 2 * a)

-- Phases 3+4+5 combined for the specific case.
theorem phase345 (n : ℕ) :
    ⟨0, 2 * n + 2, 0, 0, 2 * n + 4⟩ [fm]⊢⁺ ⟨2 * n + 4, 0, 0, 4 * n + 6, 0⟩ := by
  -- Phase 3: R5 + R1 + R2 (3 steps)
  -- (0, 2n+2, 0, 0, 2n+4) →* (2, 2n+2, 0, 2, 2n+2)
  apply stepStar_stepPlus_stepPlus
  · show ⟨0, 2 * n + 2, 0, 0, (2 * n + 2) + 2⟩ [fm]⊢* ⟨2, 2 * n + 2, 0, 2, 2 * n + 2⟩
    exact r5_r1_r2 (b := 2 * n + 2)
  -- Phase 4: 3-step round chain (n+1 rounds)
  -- (2, 2n+2, 0, 2, 2n+2) →* (2, 0, n+1, 3n+5, n+1)
  apply stepStar_stepPlus_stepPlus
  · have h := round3 (n + 1) (b := 0) (c := 0) (d := 2) (e := n + 1)
    rw [show 0 + 2 * (n + 1) = 2 * n + 2 from by ring,
        show (n + 1) + (n + 1) = 2 * n + 2 from by ring] at h
    exact h
  -- Phase 5: R2 drain
  -- (2, 0, n+1, 3n+5, n+1) →⁺ (2n+4, 0, 0, 4n+6, 0)
  rw [show 0 + (n + 1) = n + 1 from by ring,
      show 2 + 3 * (n + 1) = 3 * n + 5 from by ring]
  apply step_stepStar_stepPlus
    (by simp [fm] : (⟨2, 0, n + 1, 3 * n + 5, n + 1⟩ : Q) [fm]⊢ ⟨4, 0, n, 3 * n + 6, n⟩)
  apply stepStar_trans (r2_drain n (a := 4) (d := 3 * n + 6))
  rw [show 4 + 2 * n = 2 * n + 4 from by ring,
      show 3 * n + 6 + n = 4 * n + 6 from by ring]
  finish

-- Main transition.
theorem main_trans (n : ℕ) :
    ⟨n + 2, 0, 0, 2 * n + 2, 0⟩ [fm]⊢⁺ ⟨2 * n + 4, 0, 0, 4 * n + 6, 0⟩ :=
  stepStar_stepPlus_stepPlus (phase12 (n + 2) (2 * n + 2)) (phase345 n)

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨2, 0, 0, 2, 0⟩) (by execute fm 4)
  apply progress_nonhalt_simple (fm := fm) (A := ℕ)
    (fun n ↦ ⟨n + 2, 0, 0, 2 * n + 2, 0⟩) 0
  intro n; exists 2 * n + 2
  rw [show (2 * n + 2) + 2 = 2 * n + 4 from by ring,
      show 2 * (2 * n + 2) + 2 = 4 * n + 6 from by ring]
  exact main_trans n
