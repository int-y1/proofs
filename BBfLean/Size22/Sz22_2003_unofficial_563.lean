import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #563: [35/18, 33/2, 4/55, 3/7, 10/11]

Vector representation:
```
-1 -2  1  1  0
-1  1  0  0  1
 2  0 -1  0 -1
 0  1  0 -1  0
 1  0  1  0 -1
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_563

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a+1, b+2, c, d, e⟩ => some ⟨a, b, c+1, d+1, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b+1, c, d, e+1⟩
  | ⟨a, b, c+1, d, e+1⟩ => some ⟨a+2, b, c, d, e⟩
  | ⟨a, b, c, d+1, e⟩ => some ⟨a, b+1, c, d, e⟩
  | ⟨a, b, c, d, e+1⟩ => some ⟨a+1, b, c+1, d, e⟩
  | _ => none

-- R4 repeated: convert d to b (a=0, c=0)
theorem d_to_b : ⟨0, b, 0, d+k, e⟩ [fm]⊢* ⟨0, b+k, 0, d, e⟩ := by
  have many_step : ∀ k b, ⟨0, b, 0, d+k, e⟩ [fm]⊢* ⟨0, b+k, 0, d, e⟩ := by
    intro k; induction' k with k h <;> intro b
    · exists 0
    rw [← Nat.add_assoc]
    step fm
    apply stepStar_trans (h _)
    ring_nf; finish
  exact many_step k b

-- Opening chain: 3-step R1/R3/R1 round
theorem open_round : ⟨1, b+4, c, d, e+1⟩ [fm]⊢* ⟨1, b, c+1, d+2, e⟩ := by
  step fm; step fm; step fm; ring_nf; finish

-- Iterated opening chain: k rounds
theorem open_chain : ⟨1, b+4*k, c, d, e+k⟩ [fm]⊢* ⟨1, b, c+k, d+2*k, e⟩ := by
  have many_step : ∀ k c d e, ⟨1, b+4*k, c, d, e+k⟩ [fm]⊢* ⟨1, b, c+k, d+2*k, e⟩ := by
    intro k; induction' k with k h <;> intro c d e
    · exists 0
    rw [show b + 4 * (k + 1) = (b + 4 * k) + 4 from by ring,
        show e + (k + 1) = (e + k) + 1 from by ring]
    apply stepStar_trans (@open_round (b + 4 * k) c d (e + k))
    apply stepStar_trans (h _ _ _)
    ring_nf; finish
  exact many_step k c d e

-- Closing B=0: (1, 0, c+1, d, e) → (0, 2, c, d+1, e+2)
theorem close_b0 : ⟨1, 0, c+1, d, e⟩ [fm]⊢* ⟨0, 2, c, d+1, e+2⟩ := by
  step fm; step fm; step fm; step fm; step fm; step fm; step fm
  ring_nf; finish

-- Closing B=1: (1, 1, c, d, e) → (0, 2, c, d, e+1)
theorem close_b1 : ⟨1, 1, c, d, e⟩ [fm]⊢* ⟨0, 2, c, d, e+1⟩ := by
  step fm; ring_nf; finish

-- Closing B=2: (1, 2, c, d, e+1) → (0, 2, c, d+1, e+2)
theorem close_b2 : ⟨1, 2, c, d, e+1⟩ [fm]⊢* ⟨0, 2, c, d+1, e+2⟩ := by
  step fm; step fm; step fm; step fm; ring_nf; finish

-- Closing B=3: (1, 3, c, d, e+1) → (0, 2, c, d+2, e+2)
theorem close_b3 : ⟨1, 3, c, d, e+1⟩ [fm]⊢* ⟨0, 2, c, d+2, e+2⟩ := by
  step fm; step fm; step fm; step fm; step fm; step fm; step fm
  ring_nf; finish

-- Inner loop: single round
theorem inner_round : ⟨0, 2, c+1, d, e+1⟩ [fm]⊢* ⟨0, 2, c, d+2, e+2⟩ := by
  step fm; step fm; step fm; step fm; step fm; step fm; step fm; step fm; step fm
  ring_nf; finish

-- Iterated inner loop: k rounds
theorem inner_loop : ⟨0, 2, c+k, d, e+1⟩ [fm]⊢* ⟨0, 2, c, d+2*k, e+k+1⟩ := by
  have many_step : ∀ k c d, ⟨0, 2, c+k, d, e+1⟩ [fm]⊢* ⟨0, 2, c, d+2*k, e+k+1⟩ := by
    intro k; induction' k with k h <;> intro c d
    · exists 0
    rw [show c + (k + 1) = (c + 1) + k from by ring]
    apply stepStar_trans (h _ _)
    apply stepStar_trans inner_round
    ring_nf; finish
  exact many_step k c d

-- Compose: drain + R5 + open + close_b0 + inner
-- From (0, 2, 0, D, E+1) where D=0+D_val, after drain we get (0, 2+D, 0, 0, E+1)
-- Then R5: (1, 2+D, 1, 0, E)
-- We parameterize all 4 cases with explicit numerical forms.

theorem trans_mod0 (m : ℕ) :
    ⟨0, 2, 0, 12*m+2, 4*m+2⟩ [fm]⊢⁺ ⟨0, 2, 0, 12*m+5, 4*m+3⟩ := by
  rw [show (12*m+2 : ℕ) = 0 + (12*m+2) from by ring]
  apply stepStar_stepPlus_stepPlus d_to_b
  rw [show (4*m+2 : ℕ) = (4*m+1) + 1 from by ring]
  step fm
  -- State after R5: (1, 2+(12*m+2), 1, 0, 4*m+1)
  -- Normalize everything at once for open_chain
  rw [show (2 + (12*m+2) : ℕ) = 0 + 4*(3*m+1) from by ring,
      show (4*m+1 : ℕ) = m + (3*m+1) from by ring]
  apply stepStar_trans open_chain
  -- State: (1, 0, 1+(3*m+1), 0+2*(3*m+1), m)
  -- For close_b0 we need c+1 form: rewrite 1+(3*m+1) = c+1 with c = 3*m+1
  -- But 1+(3*m+1) normalizes to (3*m+1)+1 = (3*m+1)+1 ✓ for c+1 matching
  -- However d needs normalization
  rw [show (0 + 2 * (3*m+1) : ℕ) = 6*m+2 from by ring]
  apply stepStar_trans close_b0
  -- c = Nat.add 1 (3*m), d = 6*m+2+1, e = m+2
  simp only [Nat.add_eq]
  rw [show 1 + 3*m = 0 + (3*m+1) from by ring,
      show (6*m+2+1 : ℕ) = 6*m+3 from by ring,
      show (m+2 : ℕ) = (m+1) + 1 from by ring]
  apply stepStar_trans inner_loop
  ring_nf; finish

theorem trans_mod1 (m : ℕ) :
    ⟨0, 2, 0, 12*m+5, 4*m+3⟩ [fm]⊢⁺ ⟨0, 2, 0, 12*m+8, 4*m+4⟩ := by
  rw [show (12*m+5 : ℕ) = 0 + (12*m+5) from by ring]
  apply stepStar_stepPlus_stepPlus d_to_b
  rw [show (4*m+3 : ℕ) = (4*m+2) + 1 from by ring]
  step fm
  rw [show (2 + (12*m+5) : ℕ) = 3 + 4*(3*m+1) from by ring,
      show (4*m+2 : ℕ) = (m+1) + (3*m+1) from by ring]
  apply stepStar_trans open_chain
  rw [show (0 + 2 * (3*m+1) : ℕ) = 6*m+2 from by ring]
  apply stepStar_trans close_b3
  -- c = 1+(3*m+1), d = 6*m+2+2, e = m+2
  rw [show 1 + (3*m+1) = 0 + (3*m+2) from by ring,
      show (6*m+2+2 : ℕ) = 6*m+4 from by ring,
      show (m+2 : ℕ) = (m+1) + 1 from by ring]
  apply stepStar_trans inner_loop
  ring_nf; finish

theorem trans_mod2 (m : ℕ) :
    ⟨0, 2, 0, 12*m+8, 4*m+4⟩ [fm]⊢⁺ ⟨0, 2, 0, 12*m+11, 4*m+5⟩ := by
  rw [show (12*m+8 : ℕ) = 0 + (12*m+8) from by ring]
  apply stepStar_stepPlus_stepPlus d_to_b
  rw [show (4*m+4 : ℕ) = (4*m+3) + 1 from by ring]
  step fm
  rw [show (2 + (12*m+8) : ℕ) = 2 + 4*(3*m+2) from by ring,
      show (4*m+3 : ℕ) = (m+1) + (3*m+2) from by ring]
  apply stepStar_trans open_chain
  rw [show (0 + 2 * (3*m+2) : ℕ) = 6*m+4 from by ring]
  apply stepStar_trans close_b2
  -- c = 1+(3*m+2), d = 6*m+4+1, e = m+2
  rw [show 1 + (3*m+2) = 0 + (3*m+3) from by ring,
      show (6*m+4+1 : ℕ) = 6*m+5 from by ring,
      show (m+2 : ℕ) = (m+1) + 1 from by ring]
  apply stepStar_trans inner_loop
  ring_nf; finish

theorem trans_mod3 (m : ℕ) :
    ⟨0, 2, 0, 12*m+11, 4*m+5⟩ [fm]⊢⁺ ⟨0, 2, 0, 12*m+14, 4*m+6⟩ := by
  rw [show (12*m+11 : ℕ) = 0 + (12*m+11) from by ring]
  apply stepStar_stepPlus_stepPlus d_to_b
  rw [show (4*m+5 : ℕ) = (4*m+4) + 1 from by ring]
  step fm
  rw [show (2 + (12*m+11) : ℕ) = 1 + 4*(3*m+3) from by ring,
      show (4*m+4 : ℕ) = (m+1) + (3*m+3) from by ring]
  apply stepStar_trans open_chain
  rw [show (1 + (3*m+3) : ℕ) = 3*m+4 from by ring,
      show (0 + 2 * (3*m+3) : ℕ) = 6*m+6 from by ring]
  apply stepStar_trans close_b1
  rw [show (3*m+4 : ℕ) = 0 + (3*m+4) from by ring,
      show (m+1+1 : ℕ) = (m+1) + 1 from by ring]
  apply stepStar_trans inner_loop
  ring_nf; finish

theorem main_trans (n : ℕ) :
    ⟨0, 2, 0, 3*n+2, n+2⟩ [fm]⊢⁺ ⟨0, 2, 0, 3*(n+1)+2, (n+1)+2⟩ := by
  rw [show 3*(n+1)+2 = 3*n+5 from by ring, show (n+1)+2 = n+3 from by ring]
  rcases Nat.even_or_odd n with ⟨K, hK⟩ | ⟨K, hK⟩
  · rcases Nat.even_or_odd K with ⟨m, hm⟩ | ⟨m, hm⟩
    · subst hm; subst hK
      have h := trans_mod0 m; ring_nf at h ⊢; exact h
    · subst hm; subst hK
      have h := trans_mod2 m; ring_nf at h ⊢; exact h
  · rcases Nat.even_or_odd K with ⟨m, hm⟩ | ⟨m, hm⟩
    · subst hm; subst hK
      have h := trans_mod1 m; ring_nf at h ⊢; exact h
    · subst hm; subst hK
      have h := trans_mod3 m; ring_nf at h ⊢; exact h

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨0, 2, 0, 2, 2⟩) (by execute fm 12)
  apply progress_nonhalt_simple (fm := fm) (A := ℕ) (fun n ↦ ⟨0, 2, 0, 3*n+2, n+2⟩) 0
  intro n; exact ⟨n+1, main_trans n⟩
