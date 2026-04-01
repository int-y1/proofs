import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #1354: [63/10, 4/33, 11/2, 5/7, 28/11]

Vector representation:
```
-1  2 -1  1  0
 2 -1  0  0 -1
-1  0  0  0  1
 0  0  1 -1  0
 2  0  0  1 -1
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_1354

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a+1, b, c+1, d, e⟩ => some ⟨a, b+2, c, d+1, e⟩
  | ⟨a, b+1, c, d, e+1⟩ => some ⟨a+2, b, c, d, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b, c, d, e+1⟩
  | ⟨a, b, c, d+1, e⟩ => some ⟨a, b, c+1, d, e⟩
  | ⟨a, b, c, d, e+1⟩ => some ⟨a+2, b, c, d+1, e⟩
  | _ => none

-- R3 drain: (a, 0, 0, D, e) →* (0, 0, 0, D, e + a)
theorem r3_drain : ∀ a D e, ⟨a, 0, 0, D, e⟩ [fm]⊢* ⟨0, 0, 0, D, e + a⟩ := by
  intro a; induction' a with a ih <;> intro D e
  · exists 0
  · step fm
    apply stepStar_trans (ih D (e + 1))
    ring_nf; finish

-- R4 chain: (0, 0, c, d+k, e) →* (0, 0, c+k, d, e)
theorem d_to_c : ∀ k c d e, ⟨0, 0, c, d + k, e⟩ [fm]⊢* ⟨0, 0, c + k, d, e⟩ := by
  intro k; induction' k with k ih <;> intro c d e
  · exists 0
  · rw [show d + (k + 1) = (d + k) + 1 from by ring]
    step fm
    apply stepStar_trans (ih (c + 1) d e)
    ring_nf; finish

-- Interleaved R1,R1,R2 rounds: (2, b, c+2k, D, E+k) →* (2, b+3k, c, D+2k, E)
theorem round_chain : ∀ k b c D E, ⟨2, b, c + 2 * k, D, E + k⟩ [fm]⊢* ⟨2, b + 3 * k, c, D + 2 * k, E⟩ := by
  intro k; induction' k with k ih <;> intro b c D E
  · exists 0
  · rw [show c + 2 * (k + 1) = (c + 2 * k) + 1 + 1 from by ring,
        show E + (k + 1) = (E + k) + 1 from by ring]
    step fm; step fm; step fm
    rw [show D + 1 + 1 = (D + 2) from by ring]
    apply stepStar_trans (ih (b + 3) c (D + 2) E)
    ring_nf; finish

-- Drain: (a+1, b, 0, D, e) →* (0, 0, 0, D, a+1+b+e)
theorem drain : ∀ b a D e, ⟨a + 1, b, 0, D, e⟩ [fm]⊢* ⟨0, 0, 0, D, a + 1 + b + e⟩ := by
  intro b; induction' b with b ih <;> intro a D e
  · apply stepStar_trans (r3_drain (a + 1) D e)
    ring_nf; finish
  · rcases e with _ | e
    · step fm; step fm
      rw [show a + 2 = (a + 1) + 1 from by ring]
      apply stepStar_trans (ih (a + 1) D 0)
      ring_nf; finish
    · rw [show (b + 1 : ℕ) = b + 1 from rfl]
      step fm
      rw [show a + 3 = (a + 2) + 1 from by ring]
      apply stepStar_trans (ih (a + 2) D e)
      ring_nf; finish

-- Even case: (0,0,0,2m,E+m+1) ⊢⁺ (0,0,0,2m+1,E+3m+2)
theorem main_trans_even (m E : ℕ) :
    ⟨0, 0, 0, 2 * m, E + m + 1⟩ [fm]⊢⁺ ⟨0, 0, 0, 2 * m + 1, E + 3 * m + 2⟩ := by
  -- d_to_c
  rw [show (2 * m : ℕ) = 0 + 2 * m from by ring]
  apply stepStar_stepPlus_stepPlus (d_to_c (2 * m) 0 0 (E + m + 1))
  rw [show 0 + 2 * m = 2 * m from by ring]
  -- R5
  rw [show E + m + 1 = (E + m) + 1 from by ring]
  step fm
  -- round_chain
  rw [show (2 * m : ℕ) = 0 + 2 * m from by ring,
      show E + m = E + m from rfl]
  apply stepStar_trans (round_chain m 0 0 1 E)
  -- drain
  rw [show 0 + 3 * m = 3 * m from by ring,
      show 1 + 2 * m = 2 * m + 1 from by ring,
      show (2 : ℕ) = 1 + 1 from by ring]
  apply stepStar_trans (drain (3 * m) 1 (2 * m + 1) E)
  ring_nf; finish

-- Odd case: (0,0,0,2m+1,E+m+1) ⊢⁺ (0,0,0,2m+2,E+3m+3)
theorem main_trans_odd (m E : ℕ) :
    ⟨0, 0, 0, 2 * m + 1, E + m + 1⟩ [fm]⊢⁺ ⟨0, 0, 0, 2 * m + 2, E + 3 * m + 3⟩ := by
  -- d_to_c
  rw [show (2 * m + 1 : ℕ) = 0 + (2 * m + 1) from by ring]
  apply stepStar_stepPlus_stepPlus (d_to_c (2 * m + 1) 0 0 (E + m + 1))
  rw [show 0 + (2 * m + 1) = 2 * m + 1 from by ring]
  -- R5
  rw [show E + m + 1 = (E + m) + 1 from by ring]
  step fm
  -- round_chain
  rw [show (2 * m + 1 : ℕ) = 1 + 2 * m from by ring,
      show E + m = E + m from rfl]
  apply stepStar_trans (round_chain m 0 1 1 E)
  -- R1
  rw [show 0 + 3 * m = 3 * m from by ring,
      show 1 + 2 * m = 2 * m + 1 from by ring,
      show (1 : ℕ) = 0 + 1 from by ring]
  step fm
  -- drain
  rw [show 2 * m + 1 + 1 = 2 * m + 2 from by ring,
      show (1 : ℕ) = 0 + 1 from by ring]
  apply stepStar_trans (drain (3 * m + 2) 0 (2 * m + 2) E)
  ring_nf; finish

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨0, 0, 0, 0, 1⟩) (by execute fm 1)
  apply progress_nonhalt (fm := fm)
    (P := fun q ↦ ∃ d E, q = ⟨0, 0, 0, d, E + d / 2 + 1⟩)
  · intro c ⟨d, E, hq⟩; subst hq
    rcases Nat.even_or_odd d with ⟨m, hm⟩ | ⟨m, hm⟩
    · -- d even: d = m + m
      rw [show m + m = 2 * m from by ring] at hm; subst hm
      rw [show 2 * m / 2 = m from Nat.mul_div_cancel_left m (by omega)]
      refine ⟨⟨0, 0, 0, 2 * m + 1, E + 3 * m + 2⟩,
        ⟨2 * m + 1, E + 2 * m + 1, ?_⟩, main_trans_even m E⟩
      rw [show (2 * m + 1) / 2 = m from by omega]
      ring_nf
    · -- d odd: d = 2 * m + 1
      rw [show 2 * m + 1 = 2 * m + 1 from rfl] at hm; subst hm
      rw [show (2 * m + 1) / 2 = m from by omega]
      refine ⟨⟨0, 0, 0, 2 * m + 2, E + 3 * m + 3⟩,
        ⟨2 * m + 2, E + 2 * m + 1, ?_⟩, main_trans_odd m E⟩
      rw [show (2 * m + 2) / 2 = m + 1 from by omega]
      ring_nf
  · exact ⟨0, 0, by simp⟩
