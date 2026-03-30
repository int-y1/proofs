import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #808: [35/6, 6655/2, 4/77, 3/5, 7/11]

Vector representation:
```
-1 -1  1  1  0
-1  0  1  0  3
 2  0  0 -1 -1
 0  1 -1  0  0
 0  0  0  1 -1
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_808

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a+1, b+1, c, d, e⟩ => some ⟨a, b, c+1, d+1, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b, c+1, d, e+3⟩
  | ⟨a, b, c, d+1, e+1⟩ => some ⟨a+2, b, c, d, e⟩
  | ⟨a, b, c+1, d, e⟩ => some ⟨a, b+1, c, d, e⟩
  | ⟨a, b, c, d, e+1⟩ => some ⟨a, b, c, d+1, e⟩
  | _ => none

-- R4 chain: (0, b, c+k, 0, e) →* (0, b+k, c, 0, e).
theorem c_to_b : ∀ k, ⟨0, b, c + k, 0, e⟩ [fm]⊢* ⟨0, b + k, c, 0, e⟩ := by
  intro k; induction' k with k ih generalizing b c
  · exists 0
  · rw [show c + (k + 1) = (c + k) + 1 from by ring]
    step fm
    apply stepStar_trans (ih (b := b + 1))
    ring_nf; finish

-- R5+R3: (0, b, 0, 0, e+2) →* (2, b, 0, 0, e).
theorem r5_r3 : ⟨0, b, 0, 0, e + 2⟩ [fm]⊢* ⟨2, b, 0, 0, e⟩ := by
  step fm; step fm; finish

-- One R1R1R3 round: (2, b+2, c, d, e+1) →* (2, b, c+2, d+1, e).
theorem r1r1r3_one : ⟨2, b + 2, c, d, e + 1⟩ [fm]⊢* ⟨2, b, c + 2, d + 1, e⟩ := by
  step fm
  step fm
  rw [show d + 2 = (d + 1) + 1 from by ring]
  step fm
  finish

-- R1R1R3 chain by composing rounds: (2, b+2*k, c, d, e+k) →* (2, b, c+2*k, d+k, e).
theorem r1r1r3_chain : ∀ k, ∀ b c d e,
    ⟨2, b + 2 * k, c, d, e + k⟩ [fm]⊢* ⟨2, b, c + 2 * k, d + k, e⟩ := by
  intro k; induction' k with k ih <;> intro b c d e
  · simp; exists 0
  · rw [show b + 2 * (k + 1) = (b + 2) + 2 * k from by ring,
        show e + (k + 1) = (e + 1) + k from by ring]
    apply stepStar_trans (ih (b + 2) c d (e + 1))
    exact r1r1r3_one

-- One R2R2R3 round: (2, 0, c, d+1, e) →* (2, 0, c+2, d, e+5).
theorem r2r2r3_one : ⟨2, 0, c, d + 1, e⟩ [fm]⊢* ⟨2, 0, c + 2, d, e + 5⟩ := by
  step fm; step fm; step fm; ring_nf; finish

-- R2R2R3 chain: (2, 0, c, k, e) →* (2, 0, c+2*k, 0, e+5*k).
theorem r2r2r3_chain : ∀ k, ∀ c e,
    ⟨2, 0, c, k, e⟩ [fm]⊢* ⟨2, 0, c + 2 * k, 0, e + 5 * k⟩ := by
  intro k; induction' k with k ih <;> intro c e
  · simp; exists 0
  · rw [show (k : ℕ) + 1 = k + 1 from rfl]
    apply stepStar_trans (r2r2r3_one (c := c) (d := k) (e := e))
    apply stepStar_trans (ih (c + 2) (e + 5))
    ring_nf; finish

-- Final 2 R2: (2, 0, c, 0, e) →⁺ (0, 0, c+2, 0, e+6).
theorem final_r2r2 : ⟨2, 0, c, 0, e⟩ [fm]⊢⁺ ⟨0, 0, c + 2, 0, e + 6⟩ := by
  step fm; step fm; finish

-- Phases 1-4: (0, 0, 2*n+4, 0, 4*n+9) →* (2, 0, 4*n+8, 0, 8*n+15).
theorem phases1to4 (n : ℕ) :
    ⟨0, 0, 2 * n + 4, 0, 4 * n + 9⟩ [fm]⊢* ⟨2, 0, 4 * n + 8, 0, 8 * n + 15⟩ := by
  rw [show 2 * n + 4 = 0 + (2 * n + 4) from by ring]
  apply stepStar_trans (c_to_b (2 * n + 4) (b := 0) (c := 0) (e := 4 * n + 9))
  rw [show 0 + (2 * n + 4) = 2 * n + 4 from by ring,
      show 4 * n + 9 = (4 * n + 7) + 2 from by ring]
  apply stepStar_trans (r5_r3 (b := 2 * n + 4) (e := 4 * n + 7))
  rw [show 2 * n + 4 = 0 + 2 * (n + 2) from by ring,
      show 4 * n + 7 = (3 * n + 5) + (n + 2) from by ring]
  apply stepStar_trans (r1r1r3_chain (n + 2) 0 0 0 (3 * n + 5))
  rw [show 0 + 2 * (n + 2) = 2 * n + 4 from by ring,
      show 0 + (n + 2) = n + 2 from by ring]
  apply stepStar_trans (r2r2r3_chain (n + 2) (2 * n + 4) (3 * n + 5))
  rw [show 2 * n + 4 + 2 * (n + 2) = 4 * n + 8 from by ring,
      show 3 * n + 5 + 5 * (n + 2) = 8 * n + 15 from by ring]
  finish

-- Main transition: (0, 0, 2*n+4, 0, 4*n+9) →⁺ (0, 0, 4*n+10, 0, 8*n+21).
theorem main_transition (n : ℕ) :
    ⟨0, 0, 2 * n + 4, 0, 4 * n + 9⟩ [fm]⊢⁺ ⟨0, 0, 4 * n + 10, 0, 8 * n + 21⟩ := by
  rw [show 4 * n + 10 = (4 * n + 8) + 2 from by ring,
      show 8 * n + 21 = (8 * n + 15) + 6 from by ring]
  exact stepStar_stepPlus_stepPlus (phases1to4 n) final_r2r2

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨0, 0, 4, 0, 9⟩)
  · execute fm 9
  apply progress_nonhalt_simple (fm := fm) (A := ℕ)
    (fun n ↦ ⟨0, 0, 2 * n + 4, 0, 4 * n + 9⟩) 0
  intro n
  refine ⟨2 * n + 3, ?_⟩
  rw [show 2 * (2 * n + 3) + 4 = 4 * n + 10 from by ring,
      show 4 * (2 * n + 3) + 9 = 8 * n + 21 from by ring]
  exact main_transition n
