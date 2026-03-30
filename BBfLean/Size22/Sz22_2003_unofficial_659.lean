import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #659: [35/6, 1573/2, 4/65, 3/7, 14/11]

Vector representation:
```
-1 -1  1  1  0  0
-1  0  0  0  2  1
 2  0 -1  0  0 -1
 0  1  0 -1  0  0
 1  0  0  1 -1  0
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_659

def Q := ℕ × ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a+1, b+1, c, d, e, f⟩ => some ⟨a, b, c+1, d+1, e, f⟩
  | ⟨a+1, b, c, d, e, f⟩ => some ⟨a, b, c, d, e+2, f+1⟩
  | ⟨a, b, c+1, d, e, f+1⟩ => some ⟨a+2, b, c, d, e, f⟩
  | ⟨a, b, c, d+1, e, f⟩ => some ⟨a, b+1, c, d, e, f⟩
  | ⟨a, b, c, d, e+1, f⟩ => some ⟨a+1, b, c, d+1, e, f⟩
  | _ => none

-- R4 repeated: move d to b.
theorem d_to_b : ∀ k b d, ⟨0, b, 0, d + k, e, f⟩ [fm]⊢* ⟨0, b + k, 0, d, e, f⟩ := by
  intro k; induction' k with k ih <;> intro b d
  · exists 0
  · rw [show d + (k + 1) = d + k + 1 from by ring]
    step fm
    apply stepStar_trans (ih (b + 1) d)
    ring_nf; finish

-- Drain: R3+R2+R2 repeated.
theorem drain : ∀ c d e f, ⟨0, 0, c, d, e, f + 1⟩ [fm]⊢* ⟨0, 0, 0, d, e + 4 * c, f + 1 + c⟩ := by
  intro c; induction' c with c ih <;> intro d e f
  · exists 0
  · step fm
    step fm
    step fm
    rw [show f + 2 = (f + 1) + 1 from by ring]
    apply stepStar_trans (ih d (e + 4) (f + 1))
    ring_nf; finish

-- Interleave loop: k rounds of R3+R1+R1.
theorem interleave_loop : ∀ k b c d f,
    ⟨0, 2 * k + b, c + 1, d, e, f + k⟩ [fm]⊢* ⟨0, b, c + k + 1, d + 2 * k, e, f⟩ := by
  intro k; induction' k with k ih <;> intro b c d f
  · ring_nf; exists 0
  · rw [show 2 * (k + 1) + b = 2 * k + (b + 2) from by ring,
        show f + (k + 1) = (f + 1) + k from by ring]
    apply stepStar_trans (ih (b + 2) c d (f + 1))
    step fm
    step fm
    step fm
    rw [show c + k + 2 = c + (k + 1) + 1 from by ring,
        show d + 2 * k + 2 = d + 2 * (k + 1) from by ring]
    finish

-- Odd case: n = 2k+3.
theorem main_odd (k : ℕ) :
    ⟨0, 0, 0, 2 * k + 3, (2 * k + 3) * (2 * k + 3) + 2, 2 * k + 4⟩ [fm]⊢⁺
    ⟨0, 0, 0, 2 * k + 4, (2 * k + 4) * (2 * k + 4) + 2, 2 * k + 5⟩ := by
  apply stepStar_stepPlus_stepPlus
  · have h := d_to_b (e := (2 * k + 3) * (2 * k + 3) + 2) (f := 2 * k + 4)
        (2 * k + 3) 0 0
    simp only [Nat.zero_add] at h; exact h
  -- (0, 2k+3, 0, 0, E, 2k+4). R5 then R1.
  step fm
  step fm
  -- (0, 2k+2, 1, 2, E', 2k+4) where E' = E-1.
  -- Interleave k+1 rounds: b = 2*(k+1).
  rw [show 2 * k + 2 = 2 * (k + 1) + 0 from by ring,
      show (1 : ℕ) = 0 + 1 from by ring,
      show 2 * k + 4 = (k + 3) + (k + 1) from by ring]
  apply stepStar_trans (interleave_loop (k + 1) 0 0 2 (k + 3))
  -- (0, 0, k+2, 2k+4, E', k+3)
  rw [show 0 + (k + 1) + 1 = k + 2 from by ring,
      show 2 + 2 * (k + 1) = 2 * k + 4 from by ring,
      show (k + 3 : ℕ) = (k + 2) + 1 from by ring]
  -- Drain with c = k+2.
  -- The e value after step fm reductions is (2*k+3)*(2*k+3) + (0+1).
  -- Lean sees it as (2*k+3)*(2*k+3) + 1. Apply drain directly.
  apply stepStar_trans (drain (k + 2) (2 * k + 4)
    ((2 * k + 3) * (2 * k + 3) + 1) (k + 2))
  -- Goal: ... = (0, 0, 0, 2k+4, (2k+4)^2+2, 2k+5)
  -- LHS e: (2k+3)^2+1+4*(k+2) = 4k^2+12k+9+1+4k+8 = 4k^2+16k+18
  -- RHS e: (2k+4)^2+2 = 4k^2+16k+16+2 = 4k^2+16k+18. Match!
  ring_nf; finish

-- Even case: n = 2k+2.
theorem main_even (k : ℕ) :
    ⟨0, 0, 0, 2 * k + 2, (2 * k + 2) * (2 * k + 2) + 2, 2 * k + 3⟩ [fm]⊢⁺
    ⟨0, 0, 0, 2 * k + 3, (2 * k + 3) * (2 * k + 3) + 2, 2 * k + 4⟩ := by
  apply stepStar_stepPlus_stepPlus
  · have h := d_to_b (e := (2 * k + 2) * (2 * k + 2) + 2) (f := 2 * k + 3)
        (2 * k + 2) 0 0
    simp only [Nat.zero_add] at h; exact h
  -- (0, 2k+2, 0, 0, E, 2k+3). R5 then R1.
  step fm
  step fm
  -- (0, 2k+1, 1, 2, E', 2k+3). Interleave k rounds with b=1.
  rw [show 2 * k + 1 = 2 * k + 1 from rfl,
      show (1 : ℕ) = 0 + 1 from by ring,
      show 2 * k + 3 = (k + 3) + k from by ring]
  apply stepStar_trans (interleave_loop k 1 0 2 (k + 3))
  rw [show 0 + k + 1 = k + 1 from by ring,
      show 2 + 2 * k = 2 * k + 2 from by ring]
  -- (0, 1, k+1, 2k+2, E', k+3). Three extra steps: R3, R1, R2.
  step fm
  step fm
  step fm
  -- (0, 0, k+1, 2k+3, E'+2, k+3)
  -- E' = (2k+2)^2+1, E'+2 = (2k+2)^2+3.
  -- After step fm, Lean has computed E'+2 = (2*k+2)*(2*k+2) + 1 + 2 = (2*k+2)*(2*k+2) + 3.
  rw [show (k + 3 : ℕ) = (k + 2) + 1 from by ring]
  apply stepStar_trans (drain (k + 1) (2 * k + 3)
    ((2 * k + 2) * (2 * k + 2) + 1 + 2) (k + 2))
  ring_nf; finish

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨0, 0, 0, 2, 6, 3⟩)
  · execute fm 9
  apply progress_nonhalt_simple (fm := fm) (A := ℕ)
    (fun n ↦ ⟨0, 0, 0, n + 2, (n + 2) * (n + 2) + 2, n + 3⟩) 0
  intro n
  rcases Nat.even_or_odd n with ⟨k, hk⟩ | ⟨k, hk⟩
  · subst hk
    exact ⟨2 * k + 1, by
      show ⟨0, 0, 0, k + k + 2, (k + k + 2) * (k + k + 2) + 2, k + k + 3⟩ [fm]⊢⁺
           ⟨0, 0, 0, 2 * k + 1 + 2, (2 * k + 1 + 2) * (2 * k + 1 + 2) + 2, 2 * k + 1 + 3⟩
      rw [show k + k + 2 = 2 * k + 2 from by ring,
          show k + k + 3 = 2 * k + 3 from by ring,
          show 2 * k + 1 + 2 = 2 * k + 3 from by ring,
          show 2 * k + 1 + 3 = 2 * k + 4 from by ring]
      exact main_even k⟩
  · subst hk
    exact ⟨2 * k + 2, by
      show ⟨0, 0, 0, 2 * k + 1 + 2, (2 * k + 1 + 2) * (2 * k + 1 + 2) + 2, 2 * k + 1 + 3⟩ [fm]⊢⁺
           ⟨0, 0, 0, 2 * k + 2 + 2, (2 * k + 2 + 2) * (2 * k + 2 + 2) + 2, 2 * k + 2 + 3⟩
      rw [show 2 * k + 1 + 2 = 2 * k + 3 from by ring,
          show 2 * k + 1 + 3 = 2 * k + 4 from by ring,
          show 2 * k + 2 + 2 = 2 * k + 4 from by ring,
          show 2 * k + 2 + 3 = 2 * k + 5 from by ring]
      exact main_odd k⟩

end Sz22_2003_unofficial_659
