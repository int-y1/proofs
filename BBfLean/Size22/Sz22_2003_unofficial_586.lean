import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #586: [35/6, 11/2, 8/55, 3/7, 70/11]

Vector representation:
```
-1 -1  1  1  0
-1  0  0  0  1
 3  0 -1  0 -1
 0  1  0 -1  0
 1  0  1  1 -1
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_586

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a+1, b+1, c, d, e⟩ => some ⟨a, b, c+1, d+1, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b, c, d, e+1⟩
  | ⟨a, b, c+1, d, e+1⟩ => some ⟨a+3, b, c, d, e⟩
  | ⟨a, b, c, d+1, e⟩ => some ⟨a, b+1, c, d, e⟩
  | ⟨a, b, c, d, e+1⟩ => some ⟨a+1, b, c+1, d+1, e⟩
  | _ => none

-- R4 chain: d to b transfer
theorem d_to_b : ⟨0, b, 0, d+k, e⟩ [fm]⊢* ⟨0, b+k, 0, d, e⟩ := by
  have h : ∀ k b, ⟨0, b, 0, d+k, e⟩ [fm]⊢* ⟨0, b+k, 0, d, e⟩ := by
    intro k; induction' k with k ih <;> intro b
    · exists 0
    rw [show d + (k + 1) = (d + k) + 1 from by ring]
    step fm; apply stepStar_trans (ih _); ring_nf; finish
  exact h k b

-- R3+R2x3 drain: c to e transfer
theorem drain : ⟨0, 0, c+k, d, e+k⟩ [fm]⊢* ⟨0, 0, c, d, e+3*k⟩ := by
  have h : ∀ k, ∀ c e, ⟨0, 0, c+k, d, e+k⟩ [fm]⊢* ⟨0, 0, c, d, e+3*k⟩ := by
    intro k; induction' k with k ih <;> intro c e
    · exists 0
    rw [show c + (k + 1) = (c + k) + 1 from by ring,
        show e + (k + 1) = (e + k) + 1 from by ring]
    step fm; step fm; step fm; step fm
    rw [show e + k + 1 + 1 + 1 = (e + 3) + k from by ring]
    apply stepStar_trans (ih c (e + 3)); ring_nf; finish
  exact h k c e

-- R3+R1x3 interleave chain
theorem interleave : ⟨0, b+3*k, c+1, d, e+k⟩ [fm]⊢* ⟨0, b, c+2*k+1, d+3*k, e⟩ := by
  have h : ∀ k, ∀ c d e, ⟨0, b+3*k, c+1, d, e+k⟩ [fm]⊢* ⟨0, b, c+2*k+1, d+3*k, e⟩ := by
    intro k; induction' k with k ih <;> intro c d e
    · exists 0
    rw [show b + 3 * (k + 1) = (b + 3 * k) + 1 + 1 + 1 from by ring,
        show e + (k + 1) = (e + k) + 1 from by ring]
    step fm; step fm; step fm; step fm
    rw [show c + 3 = (c + 2) + 1 from by ring]
    apply stepStar_trans (ih (c + 2) (d + 3) e); ring_nf; finish
  exact h k c d e

-- Transition for d = 3k+1
theorem trans_r0 :
    ⟨0, 0, 0, 3*k+1, f+3*k+3⟩ [fm]⊢⁺ ⟨0, 0, 0, 3*k+2, f+6*k+6⟩ := by
  -- R4 drain
  rw [show (3*k+1 : ℕ) = 0 + (3*k+1) from by ring]
  apply stepStar_stepPlus_stepPlus (d_to_b (b := 0) (d := 0))
  simp only [Nat.zero_add]
  -- R5+R1
  rw [show f+3*k+3 = (f+3*k+2) + 1 from by ring,
      show (3*k+1 : ℕ) = (3*k) + 1 from by ring]
  step fm; step fm
  -- Interleave k rounds
  rw [show f + 3 * k + 2 = (f + 2 * k + 2) + k from by ring,
      show (3 * k : ℕ) = 0 + 3 * k from by ring]
  refine stepStar_trans (interleave (b := 0) (c := 1) (d := 2) (e := f + 2 * k + 2)) ?_
  -- Drain
  rw [show 1 + 2 * k + 1 = 0 + (2 * k + 2) from by ring,
      show 2 + 3 * k = 3 * k + 2 from by ring,
      show f + 2 * k + 2 = f + (2 * k + 2) from by ring]
  apply stepStar_trans (drain (c := 0) (k := 2 * k + 2) (d := 3 * k + 2) (e := f))
  ring_nf; finish

-- Transition for d = 3k+2
theorem trans_r1 :
    ⟨0, 0, 0, 3*k+2, f+3*k+4⟩ [fm]⊢⁺ ⟨0, 0, 0, 3*k+3, f+6*k+8⟩ := by
  rw [show (3*k+2 : ℕ) = 0 + (3*k+2) from by ring]
  apply stepStar_stepPlus_stepPlus (d_to_b (b := 0) (d := 0))
  simp only [Nat.zero_add]
  rw [show f+3*k+4 = (f+3*k+3) + 1 from by ring,
      show (3*k+2 : ℕ) = (3*k+1) + 1 from by ring]
  step fm; step fm
  -- Interleave k rounds
  rw [show (3*k+1 : ℕ) = 1 + 3*k from by ring,
      show f+3*k+3 = (f+2*k+3) + k from by ring]
  apply stepStar_trans (interleave (b := 1) (c := 1) (d := 2) (e := f+2*k+3))
  -- R3+R1+R2x2
  rw [show 1 + 2 * k + 1 = (2 * k + 1) + 1 from by ring,
      show f + 2 * k + 3 = (f + 2 * k + 2) + 1 from by ring]
  step fm; rw [show 2 + 3 * k = 3 * k + 2 from by ring]
  step fm; step fm; step fm
  -- Drain
  rw [show 2 * k + 2 = 0 + (2 * k + 2) from by ring,
      show f + 2 * k + 2 + 1 + 1 = (f + 2) + (2 * k + 2) from by ring]
  apply stepStar_trans (drain (c := 0) (k := 2*k+2) (d := 3*k+3) (e := f+2))
  ring_nf; finish

-- Transition for d = 3k+3
theorem trans_r2 :
    ⟨0, 0, 0, 3*k+3, f+3*k+5⟩ [fm]⊢⁺ ⟨0, 0, 0, 3*k+4, f+6*k+10⟩ := by
  rw [show (3*k+3 : ℕ) = 0 + (3*k+3) from by ring]
  apply stepStar_stepPlus_stepPlus (d_to_b (b := 0) (d := 0))
  simp only [Nat.zero_add]
  rw [show f+3*k+5 = (f+3*k+4) + 1 from by ring,
      show (3*k+3 : ℕ) = (3*k+2) + 1 from by ring]
  step fm; step fm
  -- Interleave k rounds
  rw [show (3*k+2 : ℕ) = 2 + 3*k from by ring,
      show f+3*k+4 = (f+2*k+4) + k from by ring]
  apply stepStar_trans (interleave (b := 2) (c := 1) (d := 2) (e := f+2*k+4))
  -- R3+R1x2+R2
  rw [show 1 + 2 * k + 1 = (2 * k + 1) + 1 from by ring,
      show f + 2 * k + 4 = (f + 2 * k + 3) + 1 from by ring]
  step fm; rw [show 2 + 3 * k = 3 * k + 2 from by ring]
  step fm; step fm; step fm
  -- Drain
  rw [show 2 * k + 3 = 0 + (2 * k + 3) from by ring,
      show f + 2 * k + 3 + 1 = (f + 1) + (2 * k + 3) from by ring]
  apply stepStar_trans (drain (c := 0) (k := 2*k+3) (d := 3*k+4) (e := f+1))
  ring_nf; finish

-- D = 0 case
theorem trans_zero : ⟨0, 0, 0, 0, f+2⟩ [fm]⊢⁺ ⟨0, 0, 0, 1, f+4⟩ := by
  step fm; step fm; step fm; step fm; step fm; step fm; finish

-- Main transition
theorem main_trans (D E : ℕ) (hE : E ≥ D + 2) :
    ⟨0, 0, 0, D, E⟩ [fm]⊢⁺ ⟨(0 : ℕ), 0, 0, D+1, E+D+2⟩ := by
  rcases D with _ | D
  · -- D = 0
    obtain ⟨f, rfl⟩ : ∃ f, E = f + 2 := ⟨E - 2, by omega⟩
    rw [show f + 2 + 0 + 2 = f + 4 from by ring]
    exact trans_zero
  · -- D ≥ 1
    obtain ⟨q, r, hr, rfl⟩ : ∃ q r, r < 3 ∧ D = 3 * q + r := by
      exact ⟨D / 3, D % 3, Nat.mod_lt D (by omega), (Nat.div_add_mod D 3).symm⟩
    rcases (show r = 0 ∨ r = 1 ∨ r = 2 from by omega) with rfl | rfl | rfl
    · -- r = 0: d+1 = 3q+1
      obtain ⟨f, rfl⟩ : ∃ f, E = f + 3*q + 3 := ⟨E - 3*q - 3, by omega⟩
      rw [show 3 * q + 0 + 1 = 3*q + 1 from by ring,
          show 3 * q + 0 + 1 + 1 = 3*q + 2 from by ring,
          show f + 3*q + 3 + (3*q + 0 + 1) + 2 = f + 6*q + 6 from by ring]
      exact trans_r0
    · -- r = 1: d+1 = 3q+2
      obtain ⟨f, rfl⟩ : ∃ f, E = f + 3*q + 4 := ⟨E - 3*q - 4, by omega⟩
      rw [show 3 * q + 1 + 1 = 3*q + 2 from by ring,
          show 3 * q + 1 + 1 + 1 = 3*q + 3 from by ring,
          show f + 3*q + 4 + (3*q + 1 + 1) + 2 = f + 6*q + 8 from by ring]
      exact trans_r1
    · -- r = 2: d+1 = 3q+3
      obtain ⟨f, rfl⟩ : ∃ f, E = f + 3*q + 5 := ⟨E - 3*q - 5, by omega⟩
      rw [show 3 * q + 2 + 1 = 3*q + 3 from by ring,
          show 3 * q + 2 + 1 + 1 = 3*q + 4 from by ring,
          show f + 3*q + 5 + (3*q + 2 + 1) + 2 = f + 6*q + 10 from by ring]
      exact trans_r2

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨0, 0, 0, 1, 3⟩) (by execute fm 7)
  apply progress_nonhalt (fm := fm)
    (P := fun q ↦ ∃ d e, q = ⟨0, 0, 0, d, e⟩ ∧ e ≥ d + 2)
  · intro c ⟨d, e, hq, he⟩; subst hq
    exact ⟨⟨0, 0, 0, d+1, e+d+2⟩, ⟨d+1, e+d+2, rfl, by omega⟩, main_trans d e he⟩
  · exact ⟨1, 3, rfl, by omega⟩

end Sz22_2003_unofficial_586
