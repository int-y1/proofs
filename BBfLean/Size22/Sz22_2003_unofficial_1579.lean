import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #1579: [7/45, 5/77, 2662/5, 3/11, 25/2]

Vector representation:
```
 0 -2 -1  1  0
 0  0  1 -1 -1
 1  0 -1  0  3
 0  1  0  0 -1
-1  0  2  0  0
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_1579

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a, b+2, c+1, d, e⟩ => some ⟨a, b, c, d+1, e⟩
  | ⟨a, b, c, d+1, e+1⟩ => some ⟨a, b, c+1, d, e⟩
  | ⟨a, b, c+1, d, e⟩ => some ⟨a+1, b, c, d, e+3⟩
  | ⟨a, b, c, d, e+1⟩ => some ⟨a, b+1, c, d, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b, c+2, d, e⟩
  | _ => none

-- R3 chain with b=0
theorem r3_chain : ∀ n, ⟨a, 0, n, 0, e⟩ [fm]⊢* ⟨a + n, 0, 0, 0, e + 3 * n⟩ := by
  intro n; induction' n with n ih generalizing a e
  · exists 0
  · step fm
    apply stepStar_trans (ih (a := a + 1) (e := e + 3))
    ring_nf; finish

-- R3 chain with b=1
theorem r3_chain_b1 : ∀ n, ⟨a, 1, n, 0, e⟩ [fm]⊢* ⟨a + n, 1, 0, 0, e + 3 * n⟩ := by
  intro n; induction' n with n ih generalizing a e
  · exists 0
  · step fm
    apply stepStar_trans (ih (a := a + 1) (e := e + 3))
    ring_nf; finish

-- R4 drain
theorem r4_drain : ∀ n, ⟨a, b, 0, 0, n⟩ [fm]⊢* ⟨a, b + n, 0, 0, 0⟩ := by
  intro n; induction' n with n ih generalizing b
  · exists 0
  · step fm
    apply stepStar_trans (ih (b := b + 1))
    ring_nf; finish

-- R5+R1+R1 one round
theorem r5r1r1_one : ⟨a + 1, b + 4, 0, d, 0⟩ [fm]⊢* ⟨a, b, 0, d + 2, 0⟩ := by
  rw [show b + 4 = (b + 2) + 2 from by ring]
  step fm; step fm; step fm; finish

-- R5+R1+R1 loop
theorem r5r1r1_loop : ∀ n b, ⟨a + n, b + 4 * n, 0, d, 0⟩ [fm]⊢* ⟨a, b, 0, d + 2 * n, 0⟩ := by
  intro n; induction' n with n ih generalizing a d
  · intro b; exists 0
  · intro b
    rw [show a + (n + 1) = (a + 1) + n from by ring,
        show b + 4 * (n + 1) = (b + 4) + 4 * n from by ring]
    apply stepStar_trans (ih (a := a + 1) (d := d) (b + 4))
    rw [show d + 2 * n = (d + 2 * n) from rfl]
    apply stepStar_trans (r5r1r1_one (b := b) (a := a) (d := d + 2 * n))
    ring_nf; finish

-- R2x3+R3 interleave loop with b=1. Net per round: a+1, c+2, d-3.
theorem interleave_b1 : ∀ n, ⟨a, 1, c, d + 3 * n, 3⟩ [fm]⊢* ⟨a + n, 1, c + 2 * n, d, 3⟩ := by
  intro n; induction' n with n ih generalizing a c d
  · exists 0
  · rw [show d + 3 * (n + 1) = (d + 3 * n) + 3 from by ring]
    rw [show (d + 3 * n) + 3 = (d + 3 * n + 2) + 1 from by ring,
        show (3 : ℕ) = 2 + 1 from by ring]
    step fm
    rw [show (d + 3 * n + 2) = (d + 3 * n + 1) + 1 from by ring,
        show (2 : ℕ) = 1 + 1 from by ring]
    step fm
    rw [show (d + 3 * n + 1) = (d + 3 * n) + 1 from by ring]
    step fm
    apply stepStar_trans
      (step_stepStar (show (⟨a, 1, c + 3, d + 3 * n, 0⟩ : Q) [fm]⊢ ⟨a + 1, 1, c + 2, d + 3 * n, 3⟩ from by simp [fm]))
    apply stepStar_trans (ih (a := a + 1) (c := c + 2) (d := d))
    ring_nf; finish

-- R2x3+R3 interleave loop with b=0
theorem interleave_b0 : ∀ n, ⟨a, 0, c, d + 3 * n, 3⟩ [fm]⊢* ⟨a + n, 0, c + 2 * n, d, 3⟩ := by
  intro n; induction' n with n ih generalizing a c d
  · exists 0
  · rw [show d + 3 * (n + 1) = (d + 3 * n) + 3 from by ring]
    rw [show (d + 3 * n) + 3 = (d + 3 * n + 2) + 1 from by ring,
        show (3 : ℕ) = 2 + 1 from by ring]
    step fm
    rw [show (d + 3 * n + 2) = (d + 3 * n + 1) + 1 from by ring,
        show (2 : ℕ) = 1 + 1 from by ring]
    step fm
    rw [show (d + 3 * n + 1) = (d + 3 * n) + 1 from by ring]
    step fm
    apply stepStar_trans
      (step_stepStar (show (⟨a, 0, c + 3, d + 3 * n, 0⟩ : Q) [fm]⊢ ⟨a + 1, 0, c + 2, d + 3 * n, 3⟩ from by simp [fm]))
    apply stepStar_trans (ih (a := a + 1) (c := c + 2) (d := d))
    ring_nf; finish

-- Half 1: (a, 0, 4k+3, 0, 0) ->* (a+k+1, 1, 0, 6k+4, 0)
theorem half1_drain (a k : ℕ) :
    ⟨a, 0, 4 * k + 3, 0, 0⟩ [fm]⊢* ⟨a + k + 1, 1, 0, 6 * k + 4, 0⟩ := by
  apply stepStar_trans (r3_chain (4 * k + 3) (a := a) (e := 0))
  rw [show 0 + 3 * (4 * k + 3) = 12 * k + 9 from by ring]
  apply stepStar_trans (r4_drain (12 * k + 9) (a := a + (4 * k + 3)) (b := 0))
  rw [show a + (4 * k + 3) = (a + k + 1) + (3 * k + 2) from by ring,
      show 0 + (12 * k + 9) = 1 + 4 * (3 * k + 2) from by ring]
  apply stepStar_trans (r5r1r1_loop (3 * k + 2) (a := a + k + 1) (d := 0) 1)
  ring_nf; finish

-- Phase A: R5+R3: (a+k+1, 1, 0, 6k+4, 0) ->* (a+k+1, 1, 1, 6k+4, 3)
theorem phaseA (a k : ℕ) :
    ⟨a + k + 1, 1, 0, 6 * k + 4, 0⟩ [fm]⊢* ⟨a + k + 1, 1, 1, 6 * k + 4, 3⟩ := by
  rw [show a + k + 1 = (a + k) + 1 from by ring]
  step fm; step fm; finish

-- Phase B: interleave(2k), R2x3, R3, R2
-- (a+k+1, 1, 1, 6k+4, 3) ->* (a+3k+2, 1, 4k+4, 0, 2)
theorem phaseB (a k : ℕ) :
    ⟨a + k + 1, 1, 1, 6 * k + 4, 3⟩ [fm]⊢* ⟨a + 3 * k + 2, 1, 4 * k + 4, 0, 2⟩ := by
  rw [show 6 * k + 4 = 4 + 3 * (2 * k) from by ring]
  apply stepStar_trans (interleave_b1 (2 * k) (a := a + k + 1) (c := 1) (d := 4))
  rw [show a + k + 1 + 2 * k = a + 3 * k + 1 from by ring,
      show 1 + 2 * (2 * k) = 4 * k + 1 from by ring]
  rw [show (4 : ℕ) = 3 + 1 from by ring, show (3 : ℕ) = 2 + 1 from by ring]
  step fm; step fm; step fm
  rw [show 4 * k + 4 = (4 * k + 3) + 1 from by ring]
  step fm; step fm
  ring_nf; finish

-- Phase C: R3 chain b1, R4 drain
-- (a+3k+2, 1, 4k+4, 0, 2) ->* (a+7k+6, 12k+15, 0, 0, 0)
theorem phaseC (a k : ℕ) :
    ⟨a + 3 * k + 2, 1, 4 * k + 4, 0, 2⟩ [fm]⊢* ⟨a + 7 * k + 6, 12 * k + 15, 0, 0, 0⟩ := by
  apply stepStar_trans (r3_chain_b1 (4 * k + 4) (a := a + 3 * k + 2) (e := 2))
  rw [show a + 3 * k + 2 + (4 * k + 4) = a + 7 * k + 6 from by ring,
      show 2 + 3 * (4 * k + 4) = 12 * k + 14 from by ring]
  apply stepStar_trans (r4_drain (12 * k + 14) (a := a + 7 * k + 6) (b := 1))
  rw [show 1 + (12 * k + 14) = 12 * k + 15 from by ring]; finish

-- Phase D: R5+R1+R1 loop
-- (a+7k+6, 12k+15, 0, 0, 0) ->* (a+4k+3, 3, 0, 6k+6, 0)
theorem phaseD (a k : ℕ) :
    ⟨a + 7 * k + 6, 12 * k + 15, 0, 0, 0⟩ [fm]⊢* ⟨a + 4 * k + 3, 3, 0, 6 * k + 6, 0⟩ := by
  rw [show a + 7 * k + 6 = (a + 4 * k + 3) + (3 * k + 3) from by ring,
      show 12 * k + 15 = 3 + 4 * (3 * k + 3) from by ring]
  apply stepStar_trans (r5r1r1_loop (3 * k + 3) (a := a + 4 * k + 3) (d := 0) 3)
  ring_nf; finish

-- Phase E: R5, R1, R3, R2x3, R3
theorem phaseE (a k : ℕ) :
    ⟨a + 4 * k + 3, 3, 0, 6 * k + 6, 0⟩ [fm]⊢* ⟨a + 4 * k + 4, 1, 2, 6 * k + 4, 3⟩ := by
  rw [show a + 4 * k + 3 = (a + 4 * k + 2) + 1 from by ring]
  step fm; step fm; step fm
  rw [show 6 * k + 7 = (6 * k + 6) + 1 from by ring, show (3 : ℕ) = 2 + 1 from by ring]
  step fm
  rw [show (6 * k + 6) = (6 * k + 5) + 1 from by ring]
  step fm
  rw [show (6 * k + 5) = (6 * k + 4) + 1 from by ring]
  step fm
  rw [show (3 : ℕ) = 2 + 1 from by ring]
  step fm
  ring_nf; finish

-- Phase F: interleave(2k), R2x3, R3, R2
-- (a+4k+4, 1, 2, 6k+4, 3) ->* (a+6k+5, 1, 4k+5, 0, 2)
theorem phaseF (a k : ℕ) :
    ⟨a + 4 * k + 4, 1, 2, 6 * k + 4, 3⟩ [fm]⊢* ⟨a + 6 * k + 5, 1, 4 * k + 5, 0, 2⟩ := by
  rw [show 6 * k + 4 = 4 + 3 * (2 * k) from by ring]
  apply stepStar_trans (interleave_b1 (2 * k) (a := a + 4 * k + 4) (c := 2) (d := 4))
  rw [show a + 4 * k + 4 + 2 * k = a + 6 * k + 4 from by ring,
      show 2 + 2 * (2 * k) = 4 * k + 2 from by ring]
  rw [show (4 : ℕ) = 3 + 1 from by ring, show (3 : ℕ) = 2 + 1 from by ring]
  step fm; step fm; step fm
  rw [show 4 * k + 5 = (4 * k + 4) + 1 from by ring]
  step fm; step fm
  ring_nf; finish

-- Phase G: R3 chain b1, R4 drain
-- (a+6k+5, 1, 4k+5, 0, 2) ->* (a+10k+10, 12k+18, 0, 0, 0)
theorem phaseG (a k : ℕ) :
    ⟨a + 6 * k + 5, 1, 4 * k + 5, 0, 2⟩ [fm]⊢* ⟨a + 10 * k + 10, 12 * k + 18, 0, 0, 0⟩ := by
  apply stepStar_trans (r3_chain_b1 (4 * k + 5) (a := a + 6 * k + 5) (e := 2))
  rw [show a + 6 * k + 5 + (4 * k + 5) = a + 10 * k + 10 from by ring,
      show 2 + 3 * (4 * k + 5) = 12 * k + 17 from by ring]
  apply stepStar_trans (r4_drain (12 * k + 17) (a := a + 10 * k + 10) (b := 1))
  rw [show 1 + (12 * k + 17) = 12 * k + 18 from by ring]; finish

-- Phase H: R5+R1+R1 loop
-- (a+10k+10, 12k+18, 0, 0, 0) ->* (a+7k+6, 2, 0, 6k+8, 0)
theorem phaseH (a k : ℕ) :
    ⟨a + 10 * k + 10, 12 * k + 18, 0, 0, 0⟩ [fm]⊢* ⟨a + 7 * k + 6, 2, 0, 6 * k + 8, 0⟩ := by
  rw [show a + 10 * k + 10 = (a + 7 * k + 6) + (3 * k + 4) from by ring,
      show 12 * k + 18 = 2 + 4 * (3 * k + 4) from by ring]
  apply stepStar_trans (r5r1r1_loop (3 * k + 4) (a := a + 7 * k + 6) (d := 0) 2)
  ring_nf; finish

-- Phase I: R5, R1, R3, R2x3, R3
theorem phaseI (a k : ℕ) :
    ⟨a + 7 * k + 6, 2, 0, 6 * k + 8, 0⟩ [fm]⊢* ⟨a + 7 * k + 7, 0, 2, 6 * k + 6, 3⟩ := by
  rw [show a + 7 * k + 6 = (a + 7 * k + 5) + 1 from by ring]
  step fm; step fm; step fm
  rw [show 6 * k + 9 = (6 * k + 8) + 1 from by ring, show (3 : ℕ) = 2 + 1 from by ring]
  step fm
  rw [show (6 * k + 8) = (6 * k + 7) + 1 from by ring]
  step fm
  rw [show (6 * k + 7) = (6 * k + 6) + 1 from by ring]
  step fm
  rw [show (3 : ℕ) = 2 + 1 from by ring]
  step fm
  ring_nf; finish

-- Phase J: interleave_b0(2k+1), R2x3
-- (a+7k+7, 0, 2, 6k+6, 3) ->* (a+9k+8, 0, 4k+7, 0, 0)
theorem phaseJ (a k : ℕ) :
    ⟨a + 7 * k + 7, 0, 2, 6 * k + 6, 3⟩ [fm]⊢* ⟨a + 9 * k + 8, 0, 4 * k + 7, 0, 0⟩ := by
  rw [show 6 * k + 6 = 3 + 3 * (2 * k + 1) from by ring]
  apply stepStar_trans (interleave_b0 (2 * k + 1) (a := a + 7 * k + 7) (c := 2) (d := 3))
  rw [show a + 7 * k + 7 + (2 * k + 1) = a + 9 * k + 8 from by ring,
      show 2 + 2 * (2 * k + 1) = 4 * k + 4 from by ring,
      show (3 : ℕ) = 2 + 1 from by ring]
  step fm; step fm; step fm
  ring_nf; finish

-- Main transition
theorem main_trans (a k : ℕ) : ⟨a, 0, 4 * k + 3, 0, 0⟩ [fm]⊢⁺ ⟨a + 9 * k + 8, 0, 4 * k + 7, 0, 0⟩ := by
  rw [show 4 * k + 3 = (4 * k + 2) + 1 from by ring]
  apply step_stepStar_stepPlus
    (show (⟨a, 0, (4 * k + 2) + 1, 0, 0⟩ : Q) [fm]⊢ ⟨a + 1, 0, 4 * k + 2, 0, 3⟩ from by simp [fm])
  apply stepStar_trans (r3_chain (4 * k + 2) (a := a + 1) (e := 3))
  rw [show a + 1 + (4 * k + 2) = a + 4 * k + 3 from by ring,
      show 3 + 3 * (4 * k + 2) = 12 * k + 9 from by ring]
  apply stepStar_trans (r4_drain (12 * k + 9) (a := a + 4 * k + 3) (b := 0))
  rw [show 0 + (12 * k + 9) = 12 * k + 9 from by ring,
      show a + 4 * k + 3 = (a + k + 1) + (3 * k + 2) from by ring,
      show 12 * k + 9 = 1 + 4 * (3 * k + 2) from by ring]
  apply stepStar_trans (r5r1r1_loop (3 * k + 2) (a := a + k + 1) (d := 0) 1)
  rw [show 0 + 2 * (3 * k + 2) = 6 * k + 4 from by ring]
  exact stepStar_trans (phaseA a k)
   (stepStar_trans (phaseB a k)
   (stepStar_trans (phaseC a k)
   (stepStar_trans (phaseD a k)
   (stepStar_trans (phaseE a k)
   (stepStar_trans (phaseF a k)
   (stepStar_trans (phaseG a k)
   (stepStar_trans (phaseH a k)
   (stepStar_trans (phaseI a k)
                   (phaseJ a k)))))))))

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨1, 0, 3, 0, 0⟩) (by execute fm 18)
  apply progress_nonhalt_simple (fm := fm) (A := ℕ × ℕ)
    (fun ⟨k, f⟩ ↦ ⟨f, 0, 4 * k + 3, 0, 0⟩) ⟨0, 1⟩
  intro ⟨k, f⟩
  refine ⟨⟨k + 1, f + 9 * k + 8⟩, ?_⟩
  show ⟨f, 0, 4 * k + 3, 0, 0⟩ [fm]⊢⁺ ⟨f + 9 * k + 8, 0, 4 * (k + 1) + 3, 0, 0⟩
  rw [show 4 * (k + 1) + 3 = 4 * k + 7 from by ring]
  exact main_trans f k
