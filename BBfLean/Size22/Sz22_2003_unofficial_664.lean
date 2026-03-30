import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #664: [35/6, 28/55, 121/2, 3/7, 10/11]

Vector representation:
```
-1 -1  1  1  0
 2  0 -1  1 -1
-1  0  0  0  2
 0  1  0 -1  0
 1  0  1  0 -1
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_664

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a+1, b+1, c, d, e⟩ => some ⟨a, b, c+1, d+1, e⟩
  | ⟨a, b, c+1, d, e+1⟩ => some ⟨a+2, b, c, d+1, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b, c, d, e+2⟩
  | ⟨a, b, c, d+1, e⟩ => some ⟨a, b+1, c, d, e⟩
  | ⟨a, b, c, d, e+1⟩ => some ⟨a+1, b, c+1, d, e⟩
  | _ => none

theorem r3_chain : ∀ k, ∀ a d e, ⟨a + k, 0, 0, d, e⟩ [fm]⊢* ⟨a, 0, 0, d, e + 2 * k⟩ := by
  intro k; induction' k with k ih <;> intro a d e
  · exists 0
  · rw [show a + (k + 1) = (a + k) + 1 from by ring]
    step fm
    apply stepStar_trans (ih a d (e + 2))
    ring_nf; finish

theorem r4_chain : ∀ k, ∀ b d e, ⟨0, b, 0, d + k, e⟩ [fm]⊢* ⟨0, b + k, 0, d, e⟩ := by
  intro k; induction' k with k ih <;> intro b d e
  · exists 0
  · rw [show d + (k + 1) = (d + k) + 1 from by ring]
    step fm
    apply stepStar_trans (ih (b + 1) d e)
    ring_nf; finish

theorem three_step : ∀ b c d e, ⟨0, b + 2, c + 1, d, e + 1⟩ [fm]⊢* ⟨0, b, c + 2, d + 3, e⟩ := by
  intro b c d e
  step fm; step fm; step fm; ring_nf; finish

theorem three_step_chain : ∀ k, ∀ c d e,
    ⟨0, 2 * k, c + 1, d, e + k⟩ [fm]⊢* ⟨0, 0, c + 1 + k, d + 3 * k, e⟩ := by
  intro k; induction' k with k ih <;> intro c d e
  · ring_nf; finish
  · rw [show 2 * (k + 1) = (2 * k) + 2 from by ring,
        show e + (k + 1) = (e + k) + 1 from by ring]
    apply stepStar_trans (three_step (2 * k) c d (e + k))
    rw [show c + 2 = (c + 1) + 1 from by ring]
    apply stepStar_trans (ih (c + 1) (d + 3) e)
    ring_nf; finish

theorem r2_chain : ∀ k, ∀ a d e, ⟨a, 0, k, d, e + k⟩ [fm]⊢* ⟨a + 2 * k, 0, 0, d + k, e⟩ := by
  intro k; induction' k with k ih <;> intro a d e
  · ring_nf; finish
  · rw [show e + (k + 1) = (e + k) + 1 from by ring,
        show k + 1 = k + 1 from rfl]
    step fm
    apply stepStar_trans (ih (a + 2) (d + 1) e)
    ring_nf; finish

theorem main_trans (n : ℕ) :
    ⟨2 ^ n + 2, 0, 0, 2 ^ (n + 1) - 1, 3 * n⟩ [fm]⊢⁺
    ⟨2 ^ (n + 1) + 2, 0, 0, 2 ^ (n + 2) - 1, 3 * (n + 1)⟩ := by
  have h2n : 2 ^ n ≥ 1 := Nat.one_le_pow _ _ (by omega)
  have h2n1 : 2 ^ (n + 1) ≥ 2 := by
    have : 2 ^ (n + 1) = 2 * 2 ^ n := by ring
    omega
  -- Phase 1: R3 chain drains a
  have phase1 : ⟨2 ^ n + 2, 0, 0, 2 ^ (n + 1) - 1, 3 * n⟩ [fm]⊢*
      ⟨0, 0, 0, 2 ^ (n + 1) - 1, 3 * n + 2 * (2 ^ n + 2)⟩ := by
    have h := r3_chain (2 ^ n + 2) 0 (2 ^ (n + 1) - 1) (3 * n)
    simp at h; exact h
  -- Phase 2: R4 chain drains d to b
  have phase2 : ⟨0, 0, 0, 2 ^ (n + 1) - 1, 3 * n + 2 * (2 ^ n + 2)⟩ [fm]⊢*
      ⟨0, 2 ^ (n + 1) - 1, 0, 0, 3 * n + 2 * (2 ^ n + 2)⟩ := by
    rw [show 2 ^ (n + 1) - 1 = 0 + (2 ^ (n + 1) - 1) from by ring]
    exact r4_chain _ 0 _ _
  -- Phase 3: R5 + R1 (2 steps)
  have phase3 : ⟨0, 2 ^ (n + 1) - 1, 0, 0, 3 * n + 2 * (2 ^ n + 2)⟩ [fm]⊢⁺
      ⟨0, 2 ^ (n + 1) - 2, 2, 1, 3 * n + 2 ^ (n + 1) + 3⟩ := by
    rw [show 2 ^ (n + 1) - 1 = (2 ^ (n + 1) - 2) + 1 from by omega,
        show 3 * n + 2 * (2 ^ n + 2) = (3 * n + 2 ^ (n + 1) + 3) + 1 from by
          rw [show 2 ^ (n + 1) = 2 * 2 ^ n from by ring]; omega]
    step fm; step fm; finish
  -- Phase 4: three_step_chain with k = 2^n - 1
  have phase4 : ⟨0, 2 ^ (n + 1) - 2, 2, 1, 3 * n + 2 ^ (n + 1) + 3⟩ [fm]⊢*
      ⟨0, 0, 2 ^ n + 1, 3 * 2 ^ n - 2, 3 * n + 2 ^ n + 4⟩ := by
    rw [show 2 ^ (n + 1) - 2 = 2 * (2 ^ n - 1) from by
          rw [show 2 ^ (n + 1) = 2 * 2 ^ n from by ring]; omega,
        show (2 : ℕ) = 1 + 1 from by ring,
        show 3 * n + 2 ^ (n + 1) + 3 = (3 * n + 2 ^ n + 4) + (2 ^ n - 1) from by
          rw [show 2 ^ (n + 1) = 2 * 2 ^ n from by ring]; omega]
    have h := three_step_chain (2 ^ n - 1) 1 1 (3 * n + 2 ^ n + 4)
    rw [show 1 + 1 + (2 ^ n - 1) = 2 ^ n + 1 from by omega,
        show 1 + 3 * (2 ^ n - 1) = 3 * 2 ^ n - 2 from by omega] at h
    exact h
  -- Phase 5: R2 chain drains c
  have phase5 : ⟨0, 0, 2 ^ n + 1, 3 * 2 ^ n - 2, 3 * n + 2 ^ n + 4⟩ [fm]⊢*
      ⟨2 ^ (n + 1) + 2, 0, 0, 2 ^ (n + 2) - 1, 3 * (n + 1)⟩ := by
    rw [show 3 * n + 2 ^ n + 4 = 3 * (n + 1) + (2 ^ n + 1) from by ring]
    have h := r2_chain (2 ^ n + 1) 0 (3 * 2 ^ n - 2) (3 * (n + 1))
    rw [show 0 + 2 * (2 ^ n + 1) = 2 ^ (n + 1) + 2 from by
          rw [show 2 ^ (n + 1) = 2 * 2 ^ n from by ring]; ring,
        show 3 * 2 ^ n - 2 + (2 ^ n + 1) = 2 ^ (n + 2) - 1 from by
          rw [show 2 ^ (n + 2) = 4 * 2 ^ n from by ring]; omega] at h
    exact h
  exact stepStar_stepPlus_stepPlus phase1
    (stepStar_stepPlus_stepPlus phase2
      (stepPlus_stepStar_stepPlus phase3
        (stepStar_trans phase4 phase5)))

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨3, 0, 0, 1, 0⟩) (by execute fm 3)
  apply progress_nonhalt_simple (fm := fm) (A := ℕ)
    (fun n ↦ ⟨2 ^ n + 2, 0, 0, 2 ^ (n + 1) - 1, 3 * n⟩) 0
  intro n; exact ⟨n + 1, main_trans n⟩
