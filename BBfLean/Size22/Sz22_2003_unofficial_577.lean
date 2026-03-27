import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #577: [35/6, 11/2, 4/55, 3/7, 350/11]

Vector representation:
```
-1 -1  1  1  0
-1  0  0  0  1
 2  0 -1  0 -1
 0  1  0 -1  0
 1  0  2  1 -1
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_577

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a+1, b+1, c, d, e⟩ => some ⟨a, b, c+1, d+1, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b, c, d, e+1⟩
  | ⟨a, b, c+1, d, e+1⟩ => some ⟨a+2, b, c, d, e⟩
  | ⟨a, b, c, d+1, e⟩ => some ⟨a, b+1, c, d, e⟩
  | ⟨a, b, c, d, e+1⟩ => some ⟨a+1, b, c+2, d+1, e⟩
  | _ => none

-- R4 repeated: convert d to b
theorem d_to_b : ⟨0, b, 0, k, e⟩ [fm]⊢* ⟨0, b + k, 0, 0, e⟩ := by
  have many_step : ∀ k b, ⟨0, b, 0, k, e⟩ [fm]⊢* ⟨0, b + k, 0, 0, e⟩ := by
    intro k; induction' k with k h <;> intro b
    · exists 0
    step fm
    apply stepStar_trans (h _)
    ring_nf; finish
  exact many_step k b

-- R3+R2+R2 drain: (0, 0, k, D, E+1) ->* (0, 0, 0, D, E+1+k)
theorem r3r2r2_drain : ⟨0, 0, k, D, E + 1⟩ [fm]⊢* ⟨0, 0, 0, D, E + 1 + k⟩ := by
  have many_step : ∀ k E, ⟨0, 0, k, D, E + 1⟩ [fm]⊢* ⟨0, 0, 0, D, E + 1 + k⟩ := by
    intro k; induction' k with k h <;> intro E
    · exists 0
    step fm; step fm; step fm
    apply stepStar_trans (h _)
    ring_nf; finish
  exact many_step k E

-- R1+R1+R3 chain: (2, B+2*k, C, D, E+k) ->* (2, B, C+k, D+2*k, E)
theorem r1r1r3_chain : ⟨2, B + 2 * k, C, D, E + k⟩ [fm]⊢* ⟨2, B, C + k, D + 2 * k, E⟩ := by
  have many_step : ∀ k C D E, ⟨2, B + 2 * k, C, D, E + k⟩ [fm]⊢* ⟨2, B, C + k, D + 2 * k, E⟩ := by
    intro k; induction' k with k h <;> intro C D E
    · exists 0
    rw [show B + 2 * (k + 1) = (B + 2 * k) + 1 + 1 from by omega,
        show E + (k + 1) = (E + k) + 1 from by omega]
    step fm; step fm; step fm
    apply stepStar_trans (h _ _ _)
    ring_nf; finish
  exact many_step k C D E

-- Even tail: from (2, 2*k, 2, 2, 3*k+1+k) to (0, 0, 0, 2*k+2, 4*k+5)
theorem tail_even (k : ℕ) :
    ⟨2, 2 * k, 2, 2, 3 * k + 1 + k⟩ [fm]⊢* ⟨0, 0, 0, 2 * k + 2, 4 * k + 5⟩ := by
  rw [show 2 * k = 0 + 2 * k from by omega]
  apply stepStar_trans (r1r1r3_chain (B := 0) (k := k) (C := 2) (D := 2) (E := 3 * k + 1))
  simp only [Nat.zero_add]
  step fm; step fm
  rw [show 3 * k + 3 = (3 * k + 2) + 1 from by omega]
  apply stepStar_trans (r3r2r2_drain (k := 2 + k) (D := 2 + 2 * k) (E := 3 * k + 2))
  ring_nf; finish

-- Odd tail: from (2, 1+2*k, 2, 2, 3*k+3+k) to (0, 0, 0, 2*k+3, 4*k+7)
theorem tail_odd (k : ℕ) :
    ⟨2, 1 + 2 * k, 2, 2, 3 * k + 3 + k⟩ [fm]⊢* ⟨0, 0, 0, 2 * k + 3, 4 * k + 7⟩ := by
  apply stepStar_trans (r1r1r3_chain (B := 1) (k := k) (C := 2) (D := 2) (E := 3 * k + 3))
  step fm; step fm
  rw [show 2 + k + 1 = 3 + k from by omega,
      show 2 + 2 * k + 1 = 3 + 2 * k from by omega,
      show 3 * k + 4 = (3 * k + 3) + 1 from by omega]
  apply stepStar_trans (r3r2r2_drain (k := 3 + k) (D := 3 + 2 * k) (E := 3 * k + 3))
  ring_nf; finish

-- Main transition for odd n (n = 2*k+1):
theorem main_odd (k : ℕ) : ⟨0, 0, 0, 2 * k + 1, 4 * k + 3⟩ [fm]⊢⁺ ⟨0, 0, 0, 2 * k + 2, 4 * k + 5⟩ := by
  apply stepStar_stepPlus_stepPlus (d_to_b (b := 0) (k := 2 * k + 1) (e := 4 * k + 3))
  simp only [Nat.zero_add]
  rw [show 4 * k + 3 = (4 * k + 2) + 1 from by omega]
  step fm; step fm; step fm
  rw [show 4 * k + 1 = 3 * k + 1 + k from by omega]
  apply stepStar_trans (tail_even k)
  finish

-- Main transition for even n (n = 2*k+2):
theorem main_even (k : ℕ) : ⟨0, 0, 0, 2 * k + 2, 4 * k + 5⟩ [fm]⊢⁺ ⟨0, 0, 0, 2 * k + 3, 4 * k + 7⟩ := by
  apply stepStar_stepPlus_stepPlus (d_to_b (b := 0) (k := 2 * k + 2) (e := 4 * k + 5))
  simp only [Nat.zero_add]
  rw [show 4 * k + 5 = (4 * k + 4) + 1 from by omega]
  step fm; step fm; step fm
  rw [show 2 * k + 1 = 1 + 2 * k from by omega,
      show 4 * k + 3 = 3 * k + 3 + k from by omega]
  apply stepStar_trans (tail_odd k)
  finish

-- Base case: n=0
theorem base_case : ⟨0, 0, 0, 0, 1⟩ [fm]⊢⁺ ⟨0, 0, 0, 1, 3⟩ := by
  execute fm 8

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨0, 0, 0, 0, 1⟩) (by execute fm 1)
  apply progress_nonhalt (fm := fm)
    (P := fun q ↦ ∃ n, q = ⟨0, 0, 0, n, 2 * n + 1⟩)
  · intro c ⟨n, hq⟩; subst hq
    rcases n with _ | n
    · exact ⟨⟨0, 0, 0, 1, 3⟩, ⟨1, rfl⟩, base_case⟩
    rcases Nat.even_or_odd n with ⟨k, hk⟩ | ⟨k, hk⟩
    · -- n even: n = 2k, so n+1 = 2k+1
      subst hk
      refine ⟨⟨0, 0, 0, 2 * k + 2, 4 * k + 5⟩, ⟨2 * k + 2, by ring_nf⟩, ?_⟩
      rw [show k + k + 1 = 2 * k + 1 from by omega,
          show 2 * (2 * k + 1) + 1 = 4 * k + 3 from by omega]
      exact main_odd k
    · -- n odd: n = 2k+1, so n+1 = 2k+2
      subst hk
      refine ⟨⟨0, 0, 0, 2 * k + 3, 4 * k + 7⟩, ⟨2 * k + 3, by ring_nf⟩, ?_⟩
      rw [show 2 * k + 1 + 1 = 2 * k + 2 from by omega,
          show 2 * (2 * k + 2) + 1 = 4 * k + 5 from by omega]
      exact main_even k
  · exact ⟨0, rfl⟩
