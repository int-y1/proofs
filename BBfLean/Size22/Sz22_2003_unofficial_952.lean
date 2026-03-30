import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #952: [4/15, 33/14, 275/2, 7/11, 9/5]

Vector representation:
```
 2 -1 -1  0  0
-1  1  0 -1  1
-1  0  2  0  1
 0  0  0  1 -1
 0  2 -1  0  0
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_952

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a, b+1, c+1, d, e⟩ => some ⟨a+2, b, c, d, e⟩
  | ⟨a+1, b, c, d+1, e⟩ => some ⟨a, b+1, c, d, e+1⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b, c+2, d, e+1⟩
  | ⟨a, b, c, d, e+1⟩ => some ⟨a, b, c, d+1, e⟩
  | ⟨a, b, c+1, d, e⟩ => some ⟨a, b+2, c, d, e⟩
  | _ => none

theorem r4_drain : ∀ k, ∀ c d,
    ⟨0, 0, c, d, k⟩ [fm]⊢* ⟨0, 0, c, d + k, 0⟩ := by
  intro k; induction' k with k ih <;> intro c d
  · ring_nf; finish
  · rw [show (k : ℕ) + 1 = k + 1 from rfl]
    step fm; apply stepStar_trans (ih c (d + 1)); ring_nf; finish

theorem r3_drain : ∀ k, ∀ c e,
    ⟨k, 0, c, 0, e⟩ [fm]⊢* ⟨0, 0, c + 2 * k, 0, e + k⟩ := by
  intro k; induction' k with k ih <;> intro c e
  · ring_nf; finish
  · step fm; apply stepStar_trans (ih (c + 2) (e + 1)); ring_nf; finish

theorem r2r1_chain : ∀ k, ∀ a c d e,
    ⟨a + 1, 0, c + k, d + k, e⟩ [fm]⊢* ⟨a + k + 1, 0, c, d, e + k⟩ := by
  intro k; induction' k with k ih <;> intro a c d e
  · ring_nf; finish
  · rw [show c + (k + 1) = (c + k) + 1 from by ring,
        show d + (k + 1) = (d + k) + 1 from by ring,
        show (k : ℕ) + 1 = k + 1 from rfl]
    step fm; step fm
    apply stepStar_trans (ih (a + 1) c d (e + 1)); ring_nf; finish

theorem main_trans (s d : ℕ) :
    ⟨0, 0, d + 1 + (s + 3), d + 1, 0⟩ [fm]⊢⁺ ⟨0, 0, 2 * (d + 1) + 4 + (s + 4), 2 * (d + 1) + 4, 0⟩ := by
  -- Phase A: R5 opening (1 step)
  rw [show d + 1 + (s + 3) = (d + (s + 3)) + 1 from by ring]
  apply step_stepStar_stepPlus
  · show fm ⟨0, 0, (d + (s + 3)) + 1, d + 1, 0⟩ = some ⟨0, 2, d + (s + 3), d + 1, 0⟩
    unfold fm; simp only
  -- Phase B: R1, R1 (2 steps)
  rw [show d + (s + 3) = (d + (s + 2)) + 1 from by ring]
  step fm
  rw [show d + (s + 2) = (d + (s + 1)) + 1 from by ring,
      show (1 : ℕ) = 0 + 1 from rfl]
  step fm
  -- State: (4, 0, d + (s + 1), d + 1, 0) = (3 + 1, 0, s + (d + 1), 0 + (d + 1), 0)
  -- Phase C: R2-R1 chain (d+1 rounds)
  have hC := r2r1_chain (d + 1) 3 s 0 0
  simp only [show 3 + 1 = 4 from rfl,
      show s + (d + 1) = d + (s + 1) from by ring,
      show 0 + (d + 1) = d + 1 from by ring,
      show 3 + (d + 1) + 1 = d + 5 from by ring] at hC
  apply stepStar_trans hC
  -- State: (d + 5, 0, s, 0, d + 1)
  -- Phase D: R3 drain
  have hD := r3_drain (d + 5) s (d + 1)
  simp only [show s + 2 * (d + 5) = 2 * d + s + 10 from by ring,
      show d + 1 + (d + 5) = 2 * d + 6 from by ring] at hD
  apply stepStar_trans hD
  -- State: (0, 0, 2*d + s + 10, 0, 2*d + 6)
  -- Phase E: R4 drain
  have hE := r4_drain (2 * d + 6) (2 * d + s + 10) 0
  simp only [show 0 + (2 * d + 6) = 2 * d + 6 from by ring] at hE
  apply stepStar_trans hE
  -- Final state: (0, 0, 2*d + s + 10, 2*d + 6, 0)
  ring_nf; finish

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨0, 0, 19, 16, 0⟩) (by execute fm 59)
  apply progress_nonhalt_simple (fm := fm) (A := ℕ × ℕ)
    (fun ⟨s, d⟩ ↦ ⟨0, 0, d + 1 + (s + 3), d + 1, 0⟩) ⟨0, 15⟩
  intro ⟨s, d⟩
  refine ⟨⟨s + 1, 2 * d + 5⟩, ?_⟩
  show ⟨0, 0, d + 1 + (s + 3), d + 1, 0⟩ [fm]⊢⁺
    ⟨0, 0, (2 * d + 5) + 1 + ((s + 1) + 3), (2 * d + 5) + 1, 0⟩
  rw [show (2 * d + 5) + 1 + ((s + 1) + 3) = 2 * (d + 1) + 4 + (s + 4) from by ring,
      show (2 * d + 5) + 1 = 2 * (d + 1) + 4 from by ring]
  exact main_trans s d
