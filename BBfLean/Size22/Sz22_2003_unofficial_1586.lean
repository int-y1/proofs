import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #1586: [7/90, 22/3, 9/77, 5/11, 21/2]

Vector representation:
```
-1 -2 -1  1  0
 1 -1  0  0  1
 0  2  0 -1 -1
 0  0  1  0 -1
-1  1  0  1  0
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_1586

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a+1, b+2, c+1, d, e⟩ => some ⟨a, b, c, d+1, e⟩
  | ⟨a, b+1, c, d, e⟩ => some ⟨a+1, b, c, d, e+1⟩
  | ⟨a, b, c, d+1, e+1⟩ => some ⟨a, b+2, c, d, e⟩
  | ⟨a, b, c, d, e+1⟩ => some ⟨a, b, c+1, d, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b+1, c, d+1, e⟩
  | _ => none

-- Phase 1: R5,R2,R3,R1 cycle. Each round: (a+1, 0, c+1, d, 0) -> (a, 0, c, d+1, 0).
theorem phase1 : ∀ k, ∀ a c d, ⟨a + k, 0, c + k, d, 0⟩ [fm]⊢* ⟨a, 0, c, d + k, 0⟩ := by
  intro k; induction' k with k ih <;> intro a c d
  · exists 0
  · rw [show a + (k + 1) = (a + k) + 1 from by ring,
        show c + (k + 1) = (c + k) + 1 from by ring]
    apply stepStar_trans
      (step_stepStar (show (⟨(a + k) + 1, 0, (c + k) + 1, d, 0⟩ : Q) [fm]⊢
        ⟨a + k, 1, (c + k) + 1, d + 1, 0⟩ from by simp [fm]))
    apply stepStar_trans
      (step_stepStar (show (⟨a + k, 1, (c + k) + 1, d + 1, 0⟩ : Q) [fm]⊢
        ⟨a + k + 1, 0, (c + k) + 1, d + 1, 1⟩ from by simp [fm]))
    apply stepStar_trans
      (step_stepStar (show (⟨a + k + 1, 0, (c + k) + 1, d + 1, 1⟩ : Q) [fm]⊢
        ⟨a + k + 1, 2, (c + k) + 1, d, 0⟩ from by simp [fm]))
    apply stepStar_trans
      (step_stepStar (show (⟨a + k + 1, 2, (c + k) + 1, d, 0⟩ : Q) [fm]⊢
        ⟨a + k, 0, c + k, d + 1, 0⟩ from by simp [fm]))
    apply stepStar_trans (ih a c (d + 1)); ring_nf; finish

-- Phase 2b: R3,R2,R2 chain. Each round drains d by 1, increases a by 2 and e by 1.
theorem phase2b : ∀ k, ∀ a d e, ⟨a, 0, 0, d + k, e + 1⟩ [fm]⊢* ⟨a + 2 * k, 0, 0, d, e + k + 1⟩ := by
  intro k; induction' k with k ih <;> intro a d e
  · exists 0
  · rw [show d + (k + 1) = (d + k) + 1 from by ring]
    step fm; step fm; step fm
    apply stepStar_trans (ih (a + 2) d (e + 1)); ring_nf; finish

-- Phase 3: R4 chain transfers e to c.
theorem phase3 : ∀ k, ∀ a c e, ⟨a, 0, c, 0, e + k⟩ [fm]⊢* ⟨a, 0, c + k, 0, e⟩ := by
  intro k; induction' k with k ih <;> intro a c e
  · exists 0
  · rw [show e + (k + 1) = (e + k) + 1 from by ring]
    step fm
    apply stepStar_trans (ih a (c + 1) e); ring_nf; finish

-- Sub-lemma: phase 1 result to final state.
theorem phase1_to_end (n : ℕ) :
    ⟨n ^ 2 + n + 1, 0, 0, 2 * n + 2, 0⟩ [fm]⊢⁺
    ⟨n ^ 2 + 5 * n + 7, 0, 2 * n + 4, 0, 0⟩ := by
  -- Phase 2a: R5, R2 (2 steps).
  rw [show n ^ 2 + n + 1 = (n ^ 2 + n) + 1 from by ring]
  apply step_stepStar_stepPlus
    (show (⟨(n ^ 2 + n) + 1, 0, 0, 2 * n + 2, 0⟩ : Q) [fm]⊢
      ⟨n ^ 2 + n, 1, 0, 2 * n + 3, 0⟩ from by simp [fm])
  apply stepStar_trans
    (step_stepStar (show (⟨n ^ 2 + n, 1, 0, 2 * n + 3, 0⟩ : Q) [fm]⊢
      ⟨n ^ 2 + n + 1, 0, 0, 2 * n + 3, 1⟩ from by simp [fm]))
  -- Phase 2b: R3,R2,R2 chain (2n+3 iterations).
  rw [show 2 * n + 3 = 0 + (2 * n + 3) from by ring,
      show (1 : ℕ) = 0 + 1 from by ring]
  apply stepStar_trans (phase2b (2 * n + 3) (n ^ 2 + n + 1) 0 0)
  -- Phase 3: R4 chain (2n+4 iterations).
  rw [show n ^ 2 + n + 1 + 2 * (2 * n + 3) = n ^ 2 + 5 * n + 7 from by ring,
      show 0 + (2 * n + 3) + 1 = 0 + (2 * n + 4) from by ring]
  apply stepStar_trans (phase3 (2 * n + 4) (n ^ 2 + 5 * n + 7) 0 0)
  ring_nf; finish

-- Main transition: (n^2+3n+3, 0, 2n+2, 0, 0) ⊢⁺ (n^2+5n+7, 0, 2n+4, 0, 0).
theorem main_trans (n : ℕ) :
    ⟨n ^ 2 + 3 * n + 3, 0, 2 * n + 2, 0, 0⟩ [fm]⊢⁺
    ⟨n ^ 2 + 5 * n + 7, 0, 2 * n + 4, 0, 0⟩ := by
  -- Phase 1: drain c and a together (2n+2 iterations).
  rw [show n ^ 2 + 3 * n + 3 = (n ^ 2 + n + 1) + (2 * n + 2) from by ring]
  have h1 := phase1 (2 * n + 2) (n ^ 2 + n + 1) 0 0
  rw [show 0 + (2 * n + 2) = 2 * n + 2 from by ring] at h1
  exact stepStar_stepPlus_stepPlus h1 (phase1_to_end n)

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨3, 0, 2, 0, 0⟩) (by execute fm 7)
  rw [show (⟨3, 0, 2, 0, 0⟩ : Q) = ⟨0 ^ 2 + 3 * 0 + 3, 0, 2 * 0 + 2, 0, 0⟩ from by norm_num]
  apply progress_nonhalt_simple (fm := fm) (A := ℕ)
    (fun n ↦ ⟨n ^ 2 + 3 * n + 3, 0, 2 * n + 2, 0, 0⟩) 0
  intro n; exact ⟨n + 1, by
    rw [show (n + 1) ^ 2 + 3 * (n + 1) + 3 = n ^ 2 + 5 * n + 7 from by ring,
        show 2 * (n + 1) + 2 = 2 * n + 4 from by ring]
    exact main_trans n⟩

end Sz22_2003_unofficial_1586
