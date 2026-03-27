import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #522: [28/15, 3/242, 55/2, 11/7, 6/5]

Vector representation:
```
 2 -1 -1  1  0
-1  1  0  0 -2
-1  0  1  0  1
 0  0  0 -1  1
 1  1 -1  0  0
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_522

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a, b+1, c+1, d, e⟩ => some ⟨a+2, b, c, d+1, e⟩
  | ⟨a+1, b, c, d, e+2⟩ => some ⟨a, b+1, c, d, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b, c+1, d, e+1⟩
  | ⟨a, b, c, d+1, e⟩ => some ⟨a, b, c, d, e+1⟩
  | ⟨a, b, c+1, d, e⟩ => some ⟨a+1, b+1, c, d, e⟩
  | _ => none

-- Phase 1: k rounds of R3,R3,R2,R1
theorem phase1_round : ⟨a+k+2, 0, c, d, 0⟩ [fm]⊢* ⟨a+2, 0, c+k, d+k, 0⟩ := by
  have h : ∀ k c d, ⟨a+k+2, 0, c, d, 0⟩ [fm]⊢* ⟨a+2, 0, c+k, d+k, 0⟩ := by
    intro k; induction' k with k ih <;> intro c d
    · exists 0
    rw [show a + (k + 1) + 2 = (a + k + 2) + 1 from by ring]
    step fm; step fm; step fm; step fm
    apply stepStar_trans (ih _ _); ring_nf; finish
  exact h k c d

-- R4 drain
theorem r4_drain : ⟨0, 0, c, d+k, e⟩ [fm]⊢* ⟨0, 0, c, d, e+k⟩ := by
  have h : ∀ k d e, ⟨0, 0, c, d+k, e⟩ [fm]⊢* ⟨0, 0, c, d, e+k⟩ := by
    intro k; induction' k with k ih <;> intro d e
    · exists 0
    rw [show d + (k + 1) = (d + k) + 1 from by ring]
    step fm; apply stepStar_trans (ih _ _); ring_nf; finish
  exact h k d e

-- R2,R1 chain
theorem r2r1_chain : ∀ a c d, ⟨a+1, 0, c+k, d, e+2*k⟩ [fm]⊢* ⟨a+k+1, 0, c, d+k, e⟩ := by
  induction' k with k ih <;> intro a c d
  · exists 0
  rw [show c + (k + 1) = (c + k) + 1 from by ring,
      show e + 2 * (k + 1) = (e + 2 * k) + 2 from by ring]
  step fm; step fm
  apply stepStar_trans (ih _ _ _); ring_nf; finish

-- Pure R2 chain
theorem pure_r2 : ∀ a b, ⟨a+k, b, 0, d, e+2*k⟩ [fm]⊢* ⟨a, b+k, 0, d, e⟩ := by
  induction' k with k ih <;> intro a b
  · exists 0
  rw [show a + (k + 1) = (a + k) + 1 from by ring,
      show e + 2 * (k + 1) = (e + 2 * k) + 2 from by ring]
  step fm; apply stepStar_trans (ih _ _); ring_nf; finish

-- Key lemma: (A+2, B, 0, D, 2) to (A+B+2, 0, 0, D+2*B+2, 0)
theorem key_lemma : ∀ A D, ⟨A+2, B, 0, D, 2⟩ [fm]⊢* ⟨A+B+2, 0, 0, D+2*B+2, 0⟩ := by
  induction' B with B ih <;> intro A D
  · execute fm 6
  step fm; step fm; step fm; step fm; step fm
  apply stepStar_trans (ih _ _); ring_nf; finish

-- Phase 2: from (0, 0, n+2, 0, 4*n+5) to (n+3, 0, 0, 3*n+6, 0)
theorem phase2 : ⟨0, 0, n+2, 0, 4*n+5⟩ [fm]⊢* ⟨n+3, 0, 0, 3*n+6, 0⟩ := by
  -- R5, R1
  rw [show n + 2 = (n + 1) + 1 from by ring]
  step fm; step fm
  -- R2,R1 chain: need (3, 0, n, 1, 4n+5) -> (n+3, 0, 0, n+1, 2n+5)
  -- After step fm, Lean leaves terms in non-canonical form. Massage with have + rw.
  have h1 : ⟨3, 0, n, 1, 4*n+5⟩ [fm]⊢* ⟨n+3, 0, 0, n+1, 2*n+5⟩ := by
    have := r2r1_chain (k := n) (e := 2*n+5) 2 0 1
    rw [show 2 + 1 = 3 from by ring,
        show (0 : ℕ) + n = n from by ring,
        show 2 * n + 5 + 2 * n = 4 * n + 5 from by ring,
        show 2 + n + 1 = n + 3 from by ring,
        show 1 + n = n + 1 from by ring] at this
    exact this
  rw [show 4 * n + 4 + 1 = 4 * n + 5 from by ring]
  apply stepStar_trans h1
  -- Pure R2 drain: (n+3, 0, 0, n+1, 2n+5) -> (1, n+2, 0, n+1, 1)
  have h2 : ⟨n+3, 0, 0, n+1, 2*n+5⟩ [fm]⊢* ⟨1, n+2, 0, n+1, 1⟩ := by
    have := pure_r2 (k := n+2) (d := n+1) (e := 1) 1 0
    rw [show 1 + (n + 2) = n + 3 from by ring,
        show 1 + 2 * (n + 2) = 2 * n + 5 from by ring,
        show (0 : ℕ) + (n + 2) = n + 2 from by ring] at this
    exact this
  apply stepStar_trans h2
  -- Bridge: R3, R1
  rw [show n + 2 = (n + 1) + 1 from by ring]
  step fm; step fm
  -- Key lemma: (2, n+1, 0, n+2, 2) -> (n+3, 0, 0, 3n+6, 0)
  have h3 : ⟨2, n+1, 0, n+2, 2⟩ [fm]⊢* ⟨n+3, 0, 0, 3*n+6, 0⟩ := by
    have := key_lemma (B := n+1) 0 (n+2)
    rw [show 0 + 2 = 2 from by ring,
        show 0 + (n + 1) + 2 = n + 3 from by ring,
        show (n + 2) + 2 * (n + 1) + 2 = 3 * n + 6 from by ring] at this
    exact this
  rw [show n + 1 + 1 = n + 2 from by ring]
  exact h3

-- Main transition
theorem main_trans : ⟨n+2, 0, 0, 3*n+3, 0⟩ [fm]⊢⁺ ⟨n+3, 0, 0, 3*n+6, 0⟩ := by
  -- Phase 1: n rounds -> (2, 0, n, 4n+3, 0)
  rw [show n + 2 = 0 + n + 2 from by ring]
  apply stepStar_stepPlus_stepPlus (phase1_round (a := 0) (k := n) (c := 0) (d := 3*n+3))
  rw [show (0 : ℕ) + 2 = 2 from by ring,
      show (0 : ℕ) + n = n from by ring,
      show 3 * n + 3 + n = 4 * n + 3 from by ring]
  -- Phase 1 tail: R3,R3
  step fm; step fm
  rw [show n + 1 + 1 = n + 2 from by ring,
      show 4 * n + 3 = 0 + (4 * n + 3) from by ring]
  -- R4 drain -> (0, 0, n+2, 0, 4n+5)
  apply stepStar_trans (r4_drain (c := n+2) (d := 0) (k := 4*n+3) (e := 2))
  rw [show 2 + (4 * n + 3) = 4 * n + 5 from by ring]
  exact phase2

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨2, 0, 0, 3, 0⟩) (by execute fm 10)
  apply progress_nonhalt_simple (fm := fm) (A := ℕ)
    (fun n ↦ ⟨n+2, 0, 0, 3*n+3, 0⟩) 0
  intro n; exists n+1
  rw [show (n + 1) + 2 = n + 3 from by ring,
      show 3 * (n + 1) + 3 = 3 * n + 6 from by ring]
  exact main_trans
