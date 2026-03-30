import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #878: [4/15, 1/42, 33/2, 7/3, 5/11, 3/7]

Vector representation:
```
 2 -1 -1  0  0
-1 -1  0 -1  0
-1  1  0  0  1
 0 -1  0  1  0
 0  0  1  0 -1
 0  1  0 -1  0
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_878

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a, b+1, c+1, d, e⟩ => some ⟨a+2, b, c, d, e⟩
  | ⟨a+1, b+1, c, d+1, e⟩ => some ⟨a, b, c, d, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b+1, c, d, e+1⟩
  | ⟨a, b+1, c, d, e⟩ => some ⟨a, b, c, d+1, e⟩
  | ⟨a, b, c, d, e+1⟩ => some ⟨a, b, c+1, d, e⟩
  | ⟨a, b, c, d+1, e⟩ => some ⟨a, b+1, c, d, e⟩
  | _ => none

-- R5 chain: move e to c
theorem e_to_c : ∀ k c d e, ⟨(0:ℕ), 0, c, d, e + k⟩ [fm]⊢* ⟨0, 0, c + k, d, e⟩ := by
  intro k; induction k with
  | zero => intro c d e; exists 0
  | succ k ih =>
    intro c d e
    rw [show e + (k + 1) = e + k + 1 from by ring]
    step fm
    apply stepStar_trans (ih (c + 1) d e)
    rw [show c + 1 + k = c + (k + 1) from by ring]; finish

-- R3 chain: drain a to b and e
theorem a_drain : ∀ k a b e, ⟨a + k, b, 0, 0, e⟩ [fm]⊢* ⟨a, b + k, 0, 0, e + k⟩ := by
  intro k; induction k with
  | zero => intro a b e; exists 0
  | succ k ih =>
    intro a b e
    rw [show a + (k + 1) = a + k + 1 from by ring]
    step fm
    apply stepStar_trans (ih a (b + 1) (e + 1))
    rw [show b + 1 + k = b + (k + 1) from by ring,
        show e + 1 + k = e + (k + 1) from by ring]; finish

-- R4 chain: drain b to d
theorem b_drain : ∀ k b d e, ⟨(0:ℕ), b + k, 0, d, e⟩ [fm]⊢* ⟨0, b, 0, d + k, e⟩ := by
  intro k; induction k with
  | zero => intro b d e; exists 0
  | succ k ih =>
    intro b d e
    rw [show b + (k + 1) = b + k + 1 from by ring]
    step fm
    apply stepStar_trans (ih b (d + 1) e)
    rw [show d + 1 + k = d + (k + 1) from by ring]; finish

-- R3+R1 interleaved chain
theorem r3r1_chain : ∀ k a c d e, ⟨a + 1, 0, c + k, d, e⟩ [fm]⊢* ⟨a + 1 + k, 0, c, d, e + k⟩ := by
  intro k; induction k with
  | zero => intro a c d e; exists 0
  | succ k ih =>
    intro a c d e
    rw [show c + (k + 1) = c + k + 1 from by ring]
    step fm
    step fm
    rw [show a + 2 = (a + 1) + 1 from by ring]
    apply stepStar_trans (ih (a + 1) c d (e + 1))
    rw [show a + 1 + 1 + k = a + 1 + (k + 1) from by ring,
        show e + 1 + k = e + (k + 1) from by ring]; finish

-- R3+R2 drain chain
theorem r3r2_chain : ∀ k a e, ⟨a + 1 + 2 * k, 0, 0, k, e⟩ [fm]⊢* ⟨a + 1, 0, 0, 0, e + k⟩ := by
  intro k; induction k with
  | zero => intro a e; exists 0
  | succ k ih =>
    intro a e
    rw [show a + 1 + 2 * (k + 1) = a + 1 + 2 * k + 2 from by ring,
        show (k + 1 : ℕ) = k + 1 from rfl]
    step fm
    step fm
    apply stepStar_trans (ih a (e + 1))
    rw [show e + 1 + k = e + (k + 1) from by ring]; finish

-- Phase 1: (1, 0, 0, 0, e) →⁺ (e+2, 0, 0, 0, e)
theorem phase1 (e : ℕ) : ⟨1, 0, 0, 0, e⟩ [fm]⊢⁺ ⟨e + 2, 0, 0, 0, e⟩ := by
  -- R3
  step fm
  -- R4
  step fm
  -- R5 chain
  rw [show e + 1 = 0 + (e + 1) from by ring]
  apply stepStar_trans (e_to_c (e + 1) 0 1 0)
  rw [show 0 + (e + 1) = e + 1 from by ring,
      show (1 : ℕ) = 0 + 1 from by ring]
  -- R6
  step fm
  -- R1
  step fm
  -- R3+R1 chain
  rw [show (2 : ℕ) = 1 + 1 from by ring,
      show (e : ℕ) = 0 + e from by ring]
  apply stepStar_trans (r3r1_chain e 1 0 0 0)
  rw [show 1 + 1 + e = e + 2 from by ring,
      show 0 + e = e from by ring]; finish

-- Phase 2: (e+2, 0, 0, 0, e) →* (1, 0, 0, 0, 3*e+2)
theorem phase2 (e : ℕ) : ⟨e + 2, 0, 0, 0, e⟩ [fm]⊢* ⟨1, 0, 0, 0, 3 * e + 2⟩ := by
  -- R3 drain
  rw [show e + 2 = 0 + (e + 2) from by ring]
  apply stepStar_trans (a_drain (e + 2) 0 0 e)
  rw [show 0 + (e + 2) = e + 2 from by ring,
      show e + (e + 2) = 2 * e + 2 from by ring]
  -- R4 drain
  rw [show e + 2 = 0 + (e + 2) from by ring]
  apply stepStar_trans (b_drain (e + 2) 0 0 (2 * e + 2))
  rw [show 0 + (e + 2) = e + 2 from by ring]
  -- R5 chain
  rw [show 2 * e + 2 = 0 + (2 * e + 2) from by ring]
  apply stepStar_trans (e_to_c (2 * e + 2) 0 (e + 2) 0)
  rw [show 0 + (2 * e + 2) = 2 * e + 2 from by ring]
  -- R6
  rw [show e + 2 = (e + 1) + 1 from by ring]
  step fm
  -- R1
  rw [show 2 * e + 2 = (2 * e + 1) + 1 from by ring]
  step fm
  -- R3+R1 chain
  rw [show (2 : ℕ) = 1 + 1 from by ring,
      show 2 * e + 1 = 0 + (2 * e + 1) from by ring]
  apply stepStar_trans (r3r1_chain (2 * e + 1) 1 0 (e + 1) 0)
  rw [show 1 + 1 + (2 * e + 1) = 0 + 1 + 2 * (e + 1) from by ring,
      show 0 + (2 * e + 1) = 2 * e + 1 from by ring]
  -- R3+R2 chain
  apply stepStar_trans (r3r2_chain (e + 1) 0 (2 * e + 1))
  rw [show 2 * e + 1 + (e + 1) = 3 * e + 2 from by ring]; finish

-- Main transition
theorem main_trans (e : ℕ) : ⟨1, 0, 0, 0, e⟩ [fm]⊢⁺ ⟨1, 0, 0, 0, 3 * e + 2⟩ :=
  stepPlus_stepStar_stepPlus (phase1 e) (phase2 e)

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨1, 0, 0, 0, 0⟩) (by exists 0)
  apply progress_nonhalt_simple (fm := fm) (A := ℕ)
    (fun e ↦ ⟨1, 0, 0, 0, e⟩) 0
  intro e; exact ⟨3 * e + 2, main_trans e⟩
