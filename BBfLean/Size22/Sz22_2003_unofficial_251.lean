import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #251: [14/15, 1/154, 36/7, 11/3, 35/2]

Vector representation:
```
 1 -1 -1  1  0
-1  0  0 -1 -1
 2  2  0 -1  0
 0 -1  0  0  1
-1  0  1  1  0
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_251

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a, b+1, c+1, d, e⟩ => some ⟨a+1, b, c, d+1, e⟩
  | ⟨a+1, b, c, d+1, e+1⟩ => some ⟨a, b, c, d, e⟩
  | ⟨a, b, c, d+1, e⟩ => some ⟨a+2, b+2, c, d, e⟩
  | ⟨a, b+1, c, d, e⟩ => some ⟨a, b, c, d, e+1⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b, c+1, d+1, e⟩
  | _ => none

-- R4 loop: drain b into e (c=0, d=0).
theorem r4_loop : ∀ b a e,
    ⟨a, b + 1, 0, 0, e⟩ [fm]⊢* ⟨a, 0, 0, 0, e + b + 1⟩ := by
  intro b; induction b with
  | zero => intro a e; step fm; finish
  | succ b ih =>
    intro a e; step fm
    apply stepStar_trans (ih a (e + 1))
    rw [show e + 1 + b + 1 = e + (b + 1) + 1 from by ring]; finish

-- R5/R2 loop: alternating R5 and R2, plus a final R5.
-- (A + 2*e + 1, 0, c, 0, e) →* (A, 0, c + e + 1, 1, 0)
theorem r5r2_loop : ∀ e A c,
    ⟨A + 2 * e + 1, 0, c, 0, e⟩ [fm]⊢* ⟨A, 0, c + e + 1, 1, 0⟩ := by
  intro e; induction e with
  | zero => intro A c; step fm; rw [show c + 0 + 1 = c + 1 from by ring]; finish
  | succ e ih =>
    intro A c
    rw [show A + 2 * (e + 1) + 1 = (A + 2 * e + 1) + 1 + 1 from by ring]
    step fm; step fm
    apply stepStar_trans (ih A (c + 1))
    rw [show c + 1 + e + 1 = c + (e + 1) + 1 from by ring]; finish

-- R3 drain: (A, B, 0, D+1, 0) →* (A + 2*(D+1), B + 2*(D+1), 0, 0, 0)
theorem r3_drain : ∀ D A B,
    ⟨A, B, 0, D + 1, 0⟩ [fm]⊢* ⟨A + 2 * (D + 1), B + 2 * (D + 1), 0, 0, 0⟩ := by
  intro D; induction D with
  | zero => intro A B; step fm; finish
  | succ D ih =>
    intro A B; step fm
    apply stepStar_trans (ih (A + 2) (B + 2))
    rw [show A + 2 + 2 * (D + 1) = A + 2 * (D + 2) from by ring,
        show B + 2 + 2 * (D + 1) = B + 2 * (D + 2) from by ring]; finish

-- Phase C: from (A, 0, c, D+1, 0) to (A + 3*c + 2*(D+1), c + 2*(D+1), 0, 0, 0).
-- By strong induction on c with cases 0, 1, c+2.
theorem phase_c : ∀ c A D,
    ⟨A, 0, c, D + 1, 0⟩ [fm]⊢* ⟨A + 3 * c + 2 * (D + 1), c + 2 * (D + 1), 0, 0, 0⟩ := by
  intro c; induction' c using Nat.strongRecOn with c ih; intro A D
  rcases c with _ | _ | c
  · -- c = 0: just R3 drain
    apply r3_drain D A 0
  · -- c = 1: R3 → R1 → R3 drain
    rw [show (0 + 1 : ℕ) = 0 + 1 from by ring]
    step fm; step fm
    -- Now at (A+3, 1, 0, D+1, 0)
    apply stepStar_trans (r3_drain D (A + 3) 1)
    rw [show A + 3 + 2 * (D + 1) = A + 3 * 1 + 2 * (D + 1) from by ring,
        show 1 + 2 * (D + 1) = 1 + 2 * (D + 1) from by ring]; finish
  · -- c + 2: R3, R1, R1, then recurse with c
    rw [show c + 2 = c + 1 + 1 from by ring]
    step fm
    rw [show c + 1 + 1 = (c + 1) + 1 from by ring]
    step fm; step fm
    -- Now at (A+4, 0, c, D+2, 0) = (A+4, 0, c, (D+1)+1, 0)
    apply stepStar_trans (ih c (by omega) (A + 4) (D + 1))
    rw [show A + 4 + 3 * c + 2 * (D + 1 + 1) = A + 3 * (c + 2) + 2 * (D + 1) from by ring,
        show c + 2 * (D + 1 + 1) = c + 2 + 2 * (D + 1) from by ring]; finish

-- Main transition: (a + 2*b + 5, b + 2, 0, 0, 0) ⊢⁺ (a + 3*b + 11, b + 5, 0, 0, 0)
theorem main_step (a b : ℕ) :
    ⟨a + 2 * b + 5, b + 2, 0, 0, 0⟩ [fm]⊢⁺ ⟨a + 3 * b + 11, b + 5, 0, 0, 0⟩ := by
  -- Phase 1: R4 loop, drain b+2 into e
  rw [show b + 2 = (b + 1) + 1 from by ring]
  apply step_stepStar_stepPlus
  · show fm ⟨a + 2 * b + 5, (b + 1) + 1, 0, 0, 0⟩ = some ⟨a + 2 * b + 5, b + 1, 0, 0, 1⟩
    rfl
  apply stepStar_trans (r4_loop b (a + 2 * b + 5) 1)
  -- Now at (a + 2*b + 5, 0, 0, 0, b + 2)
  rw [show 1 + b + 1 = b + 2 from by ring]
  -- Phase 2: R5/R2 loop
  rw [show a + 2 * b + 5 = a + 2 * (b + 2) + 1 from by ring]
  apply stepStar_trans (r5r2_loop (b + 2) a 0)
  -- Now at (a, 0, b + 3, 1, 0) = (a, 0, b+3, 0+1, 0)
  rw [show 0 + (b + 2) + 1 = b + 3 from by ring]
  -- Phase 3: Phase C
  apply stepStar_trans (phase_c (b + 3) a 0)
  rw [show a + 3 * (b + 3) + 2 * (0 + 1) = a + 3 * b + 11 from by ring,
      show b + 3 + 2 * (0 + 1) = b + 5 from by ring]; finish

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨1 + 2 * 1 + 5, 1 + 2, 0, 0, 0⟩)
  · unfold c₀; execute fm 19
  apply progress_nonhalt_simple (fm := fm) (A := ℕ × ℕ)
    (fun p ↦ ⟨p.1 + 2 * p.2 + 5, p.2 + 2, 0, 0, 0⟩) (1, 1)
  intro ⟨a, b⟩
  refine ⟨(a + b, b + 3), ?_⟩
  show ⟨a + 2 * b + 5, b + 2, 0, 0, 0⟩ [fm]⊢⁺ ⟨(a + b) + 2 * (b + 3) + 5, (b + 3) + 2, 0, 0, 0⟩
  rw [show (a + b) + 2 * (b + 3) + 5 = a + 3 * b + 11 from by ring,
      show (b + 3) + 2 = b + 5 from by ring]
  exact main_step a b

end Sz22_2003_unofficial_251
