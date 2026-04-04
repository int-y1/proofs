import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #1943: [9/70, 4/33, 55/2, 7/11, 4/5]

Vector representation:
```
-1  2 -1 -1  0
 2 -1  0  0 -1
-1  0  1  0  1
 0  0  0  1 -1
 2  0 -1  0  0
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_1943

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a+1, b, c+1, d+1, e⟩ => some ⟨a, b+2, c, d, e⟩
  | ⟨a, b+1, c, d, e+1⟩ => some ⟨a+2, b, c, d, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b, c+1, d, e+1⟩
  | ⟨a, b, c, d, e+1⟩ => some ⟨a, b, c, d+1, e⟩
  | ⟨a, b, c+1, d, e⟩ => some ⟨a+2, b, c, d, e⟩
  | _ => none

-- R3 chain with b=0, d=0: (a+k, 0, c, 0, e) →* (a, 0, c+k, 0, e+k)
theorem r3_chain : ∀ k, ∀ a c e, ⟨a + k, 0, c, 0, e⟩ [fm]⊢* ⟨a, 0, c + k, 0, e + k⟩ := by
  intro k; induction' k with k ih <;> intro a c e
  · exists 0
  · rw [show a + (k + 1) = (a + 1) + k from by ring]
    apply stepStar_trans (ih (a + 1) c e)
    apply step_stepStar
    show fm ⟨a + 1, 0, c + k, 0, e + k⟩ = some ⟨a, 0, c + k + 1, 0, e + k + 1⟩
    simp [fm]

-- R4 step: (0, 0, c, d, e+1) → (0, 0, c, d+1, e)
theorem r4_step : ⟨0, 0, c, d, e + 1⟩ [fm]⊢ ⟨0, 0, c, d + 1, e⟩ := by
  simp [fm]

-- R4 chain: (0, 0, c, d, e+k) →* (0, 0, c, d+k, e)
theorem r4_chain : ∀ k, ∀ c d e, ⟨0, 0, c, d, e + k⟩ [fm]⊢* ⟨0, 0, c, d + k, e⟩ := by
  intro k; induction' k with k ih <;> intro c d e
  · exists 0
  · rw [show d + (k + 1) = (d + 1) + k from by ring,
        show e + (k + 1) = e + k + 1 from by ring]
    apply stepStar_trans
    · apply step_stepStar (r4_step (c := c) (d := d) (e := e + k))
    exact ih c (d + 1) e

-- R5+R1+R1 one round: (0, b, c+3, d+2, 0) →* (0, b+4, c, d, 0)
theorem r5r1r1_round : ⟨0, b, c + 3, d + 2, 0⟩ [fm]⊢* ⟨0, b + 4, c, d, 0⟩ := by
  step fm; step fm; step fm; finish

-- R5+R1+R1 chain: m rounds.
theorem r5r1r1_chain : ∀ k, ∀ b c d, ⟨0, b, c + 3 * k, d + 2 * k, 0⟩ [fm]⊢* ⟨0, b + 4 * k, c, d, 0⟩ := by
  intro k; induction' k with k ih <;> intro b c d
  · exists 0
  · rw [show c + 3 * (k + 1) = (c + 3) + 3 * k from by ring,
        show d + 2 * (k + 1) = (d + 2) + 2 * k from by ring]
    apply stepStar_trans (ih b (c + 3) (d + 2))
    apply stepStar_trans (r5r1r1_round (b := b + 4 * k) (c := c) (d := d))
    ring_nf; finish

-- Bridge (F >= 1): (0, b, c+2, 1, 0) →⁺ (1, b+2, c, 0, 0)
theorem bridge_f_pos : ⟨0, b, c + 2, 1, 0⟩ [fm]⊢⁺ ⟨1, b + 2, c, 0, 0⟩ := by
  step fm; step fm; finish

-- Bridge (F = 0): (0, b, 1, 1, 0) →⁺ (2, b+1, 0, 0, 0)
theorem bridge_f_zero : ⟨0, b, 1, 1, 0⟩ [fm]⊢⁺ ⟨2, b + 1, 0, 0, 0⟩ := by
  step fm; step fm; step fm; step fm; finish

-- R3+R2 drain step: (a+1, b+1, c, 0, 0) →* (a+2, b, c+1, 0, 0)
theorem r3r2_step : ⟨a + 1, b + 1, c, 0, 0⟩ [fm]⊢* ⟨a + 2, b, c + 1, 0, 0⟩ := by
  step fm; step fm; finish

-- R3+R2 drain: (a+1, b+k, c, 0, 0) →* (a+k+1, b, c+k, 0, 0)
theorem r3r2_drain : ∀ k, ∀ a b c, ⟨a + 1, b + k, c, 0, 0⟩ [fm]⊢* ⟨a + k + 1, b, c + k, 0, 0⟩ := by
  intro k; induction' k with k ih <;> intro a b c
  · exists 0
  · rw [show b + (k + 1) = (b + k) + 1 from by ring]
    apply stepStar_trans (r3r2_step (a := a) (b := b + k) (c := c))
    rw [show a + 2 = (a + 1) + 1 from by ring]
    apply stepStar_trans (ih (a + 1) b (c + 1))
    ring_nf; finish

-- Main transition for F = 0: (2m+1, 0, m, 0, 0) →⁺ (4m+3, 0, 4m+1, 0, 0)
theorem main_trans_f_zero (m : ℕ) :
    ⟨2 * m + 1, 0, m, 0, 0⟩ [fm]⊢⁺ ⟨4 * m + 3, 0, 4 * m + 1, 0, 0⟩ := by
  rw [show 2 * m + 1 = 0 + (2 * m + 1) from by ring]
  apply stepStar_stepPlus_stepPlus (r3_chain (2 * m + 1) 0 m 0)
  rw [show m + (2 * m + 1) = 3 * m + 1 from by ring,
      show (0 : ℕ) + (2 * m + 1) = 0 + (2 * m + 1) from by ring]
  apply stepStar_stepPlus_stepPlus (r4_chain (2 * m + 1) (3 * m + 1) 0 0)
  rw [show (0 : ℕ) + (2 * m + 1) = 2 * m + 1 from by ring,
      show 3 * m + 1 = 1 + 3 * m from by ring,
      show 2 * m + 1 = 1 + 2 * m from by ring]
  apply stepStar_stepPlus_stepPlus (r5r1r1_chain m 0 1 1)
  rw [show (0 : ℕ) + 4 * m = 4 * m from by ring]
  apply stepPlus_stepStar_stepPlus (bridge_f_zero (b := 4 * m))
  rw [show (2 : ℕ) = 1 + 1 from by ring,
      show 4 * m + 1 = 0 + (4 * m + 1) from by ring]
  apply stepStar_trans (r3r2_drain (4 * m + 1) 1 0 0)
  ring_nf; finish

-- Main transition for F >= 1: (2m+1, 0, m+F+1, 0, 0) →⁺ (4m+3, 0, 4m+F+2, 0, 0)
theorem main_trans_f_pos (m F : ℕ) :
    ⟨2 * m + 1, 0, m + F + 1, 0, 0⟩ [fm]⊢⁺ ⟨4 * m + 3, 0, 4 * m + F + 2, 0, 0⟩ := by
  rw [show 2 * m + 1 = 0 + (2 * m + 1) from by ring]
  apply stepStar_stepPlus_stepPlus (r3_chain (2 * m + 1) 0 (m + F + 1) 0)
  rw [show m + F + 1 + (2 * m + 1) = 3 * m + F + 2 from by ring,
      show (0 : ℕ) + (2 * m + 1) = 0 + (2 * m + 1) from by ring]
  apply stepStar_stepPlus_stepPlus (r4_chain (2 * m + 1) (3 * m + F + 2) 0 0)
  rw [show (0 : ℕ) + (2 * m + 1) = 2 * m + 1 from by ring,
      show 3 * m + F + 2 = (F + 2) + 3 * m from by ring,
      show 2 * m + 1 = 1 + 2 * m from by ring]
  apply stepStar_stepPlus_stepPlus (r5r1r1_chain m 0 (F + 2) 1)
  rw [show (0 : ℕ) + 4 * m = 4 * m from by ring]
  apply stepPlus_stepStar_stepPlus (bridge_f_pos (b := 4 * m) (c := F))
  rw [show (1 : ℕ) = 0 + 1 from by ring,
      show 4 * m + 2 = 0 + (4 * m + 2) from by ring]
  apply stepStar_trans (r3r2_drain (4 * m + 2) 0 0 F)
  ring_nf; finish

-- Combined main transition
theorem main_trans (m F : ℕ) :
    ⟨2 * m + 1, 0, m + F, 0, 0⟩ [fm]⊢⁺ ⟨4 * m + 3, 0, 4 * m + F + 1, 0, 0⟩ := by
  rcases F with _ | F
  · exact main_trans_f_zero m
  · show ⟨2 * m + 1, 0, m + F + 1, 0, 0⟩ [fm]⊢⁺ ⟨4 * m + 3, 0, 4 * m + (F + 1) + 1, 0, 0⟩
    rw [show 4 * m + (F + 1) + 1 = 4 * m + F + 2 from by ring]
    exact main_trans_f_pos m F

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨3, 0, 1, 0, 0⟩) (by execute fm 8)
  apply progress_nonhalt_simple (fm := fm) (A := ℕ × ℕ)
    (fun ⟨m, F⟩ ↦ ⟨2 * m + 1, 0, m + F, 0, 0⟩) ⟨1, 0⟩
  intro ⟨m, F⟩
  refine ⟨⟨2 * m + 1, 2 * m + F⟩, ?_⟩
  show ⟨2 * m + 1, 0, m + F, 0, 0⟩ [fm]⊢⁺ ⟨2 * (2 * m + 1) + 1, 0, (2 * m + 1) + (2 * m + F), 0, 0⟩
  rw [show 2 * (2 * m + 1) + 1 = 4 * m + 3 from by ring,
      show (2 * m + 1) + (2 * m + F) = 4 * m + F + 1 from by ring]
  exact main_trans m F

end Sz22_2003_unofficial_1943
