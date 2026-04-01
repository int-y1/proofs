import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #1349: [63/10, 35/33, 4/3, 11/7, 21/2]

Vector representation:
```
-1  2 -1  1  0
 0 -1  1  1 -1
 2 -1  0  0  0
 0  0  0 -1  1
-1  1  0  1  0
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_1349

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a+1, b, c+1, d, e⟩ => some ⟨a, b+2, c, d+1, e⟩
  | ⟨a, b+1, c, d, e+1⟩ => some ⟨a, b, c+1, d+1, e⟩
  | ⟨a, b+1, c, d, e⟩ => some ⟨a+2, b, c, d, e⟩
  | ⟨a, b, c, d+1, e⟩ => some ⟨a, b, c, d, e+1⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b+1, c, d+1, e⟩
  | _ => none

-- R4 chain: transfer d to e
theorem d_to_e : ∀ k d, ⟨a, 0, 0, d + k, 0⟩ [fm]⊢* ⟨a, 0, 0, d, k⟩ := by
  intro k; induction' k with k ih <;> intro d
  · exists 0
  · rw [show d + (k + 1) = (d + 1) + k from by ring]
    apply stepStar_trans (ih (d + 1))
    step fm
    ring_nf; finish

-- R3 chain: transfer b to a (each b gives +2 to a)
theorem b_to_a : ∀ k, ∀ a b, ⟨a, b + k, 0, d, 0⟩ [fm]⊢* ⟨a + 2 * k, b, 0, d, 0⟩ := by
  intro k; induction' k with k ih <;> intro a b
  · exists 0
  · rw [show b + (k + 1) = (b + k) + 1 from by ring]
    step fm
    apply stepStar_trans (ih (a + 2) b)
    ring_nf; finish

-- R1-R2 interleaved chain: each round does R1 then R2, net effect a-=1, b+=1, d+=2, e-=1
theorem r1r2_chain : ∀ k, ∀ a b d, ⟨a + k, b, 1, d, k⟩ [fm]⊢* ⟨a, b + k, 1, d + 2 * k, 0⟩ := by
  intro k; induction' k with k ih <;> intro a b d
  · exists 0
  · rw [show a + (k + 1) = (a + k) + 1 from by ring]
    step fm
    apply stepStar_trans
    · show ⟨a + k, b + 2, 0, d + 1, k + 1⟩ [fm]⊢* ⟨a + k, b + 1, 1, d + 2, k⟩
      apply step_stepStar
      show fm ⟨a + k, b + 2, 0, d + 1, k + 1⟩ = some ⟨a + k, b + 1, 1, d + 2, k⟩
      simp [fm]
    apply stepStar_trans (ih a (b + 1) (d + 2))
    ring_nf; finish

-- Main transition: (e+2, 0, 0, 0, e+1) ⊢⁺ (2e+4, 0, 0, 0, 2e+3) for all e
theorem main_trans (e : ℕ) :
    ⟨e + 2, 0, 0, 0, e + 1⟩ [fm]⊢⁺ ⟨2 * e + 4, 0, 0, 0, 2 * e + 3⟩ := by
  step fm  -- R5: (e+1, 1, 0, 1, e+1)
  step fm  -- R2: (e+1, 0, 1, 2, e)
  rw [show e + 1 = 1 + e from by ring]
  apply stepStar_trans (r1r2_chain e 1 0 2)
  -- now at (1, e, 1, 2+2*e, 0)
  rw [show 0 + e = e from by ring, show 2 + 2 * e = 2 * e + 2 from by ring]
  step fm  -- R1: (0, e+2, 0, 2*e+3, 0)
  rw [show e + 2 = 0 + (e + 2) from by ring]
  apply stepStar_trans (b_to_a (d := 2 * e + 3) (e + 2) 0 0)
  rw [show 0 + 2 * (e + 2) = 2 * e + 4 from by ring]
  rw [show (2 * e + 3 : ℕ) = 0 + (2 * e + 3) from by ring]
  apply stepStar_trans (d_to_e (a := 2 * e + 4) (2 * e + 3) 0)
  ring_nf; finish

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨2, 0, 0, 0, 1⟩) (by execute fm 3)
  apply progress_nonhalt_simple (fm := fm) (A := ℕ)
    (fun e ↦ ⟨e + 2, 0, 0, 0, e + 1⟩) 0
  intro e; exact ⟨2 * e + 2, main_trans e⟩
