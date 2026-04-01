import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #1241: [5/6, 77/2, 4/35, 9/7, 245/11]

Vector representation:
```
-1 -1  1  0  0
-1  0  0  1  1
 2  0 -1 -1  0
 0  2  0 -1  0
 0  0  1  2 -1
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_1241

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a+1, b+1, c, d, e⟩ => some ⟨a, b, c+1, d, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b, c, d+1, e+1⟩
  | ⟨a, b, c+1, d+1, e⟩ => some ⟨a+2, b, c, d, e⟩
  | ⟨a, b, c, d+1, e⟩ => some ⟨a, b+2, c, d, e⟩
  | ⟨a, b, c, d, e+1⟩ => some ⟨a, b, c+1, d+2, e⟩
  | _ => none

-- R4 chain: (0, b, 0, d+k, e) →* (0, b+2k, 0, d, e)
theorem d_to_b : ∀ k b d e, ⟨0, b, 0, d + k, e⟩ [fm]⊢* ⟨0, b + 2 * k, 0, d, e⟩ := by
  intro k; induction' k with k ih <;> intro b d e
  · exists 0
  · rw [show d + (k + 1) = (d + 1) + k from by ring]
    apply stepStar_trans (ih b (d + 1) e)
    rw [show b + 2 * (k + 1) = b + 2 * k + 2 from by ring]
    step fm
    finish

-- Full interleaved round: (0, b+4, c, 0, e+1) →* (0, b, c+3, 0, e)
-- Sequence: R5, R3, R1, R1, R3, R1, R1
theorem full_round : ∀ b c e, ⟨(0 : ℕ), b + 4, c, 0, e + 1⟩ [fm]⊢* ⟨(0 : ℕ), b, c + 3, 0, e⟩ := by
  intro b c e
  step fm  -- R5: (0, b+4, c+1, 2, e)
  step fm  -- R3: (2, b+4, c, 1, e)
  step fm  -- R1: (1, b+3, c+1, 1, e)
  -- For R1 here, Lean sees b+3. Need b+3 = (b+2)+1
  rw [show b + 3 = (b + 2) + 1 from by ring]
  step fm  -- R1: (0, b+2, c+1+1, 1, e)
  step fm  -- R3: (2, b+2, c+1, 0, e)
  step fm  -- R1: (1, b+1, c+1+1, 0, e)
  step fm  -- R1: (0, b, c+1+1+1, 0, e)
  rw [show c + 1 + 1 + 1 = c + 3 from by ring]
  finish

-- k full rounds: (0, b + 4k, c, 0, e + k) →* (0, b, c + 3k, 0, e)
theorem full_rounds : ∀ k b c e, ⟨0, b + 4 * k, c, 0, e + k⟩ [fm]⊢* ⟨0, b, c + 3 * k, 0, e⟩ := by
  intro k; induction' k with k ih <;> intro b c e
  · exists 0
  · rw [show b + 4 * (k + 1) = (b + 4) + 4 * k from by ring,
        show e + (k + 1) = (e + 1) + k from by ring]
    apply stepStar_trans (ih (b + 4) c (e + 1))
    apply stepStar_trans (full_round b (c + 3 * k) e)
    ring_nf; finish

-- Even tail: (0, 0, c, 0, e+1) →⁺ (0, 0, c, 3, e+2)
-- Sequence: R5, R3, R2, R2
theorem even_tail (c e : ℕ) : ⟨(0 : ℕ), 0, c, 0, e + 1⟩ [fm]⊢⁺ ⟨(0 : ℕ), 0, c, 3, e + 2⟩ := by
  step fm; step fm; step fm; step fm
  finish

-- Odd tail: (0, 2, c, 0, e+1) →⁺ (0, 0, c+1, 2, e+2)
-- Sequence: R5, R3, R1, R1, R3, R2, R2
theorem odd_tail (c e : ℕ) : ⟨(0 : ℕ), 2, c, 0, e + 1⟩ [fm]⊢⁺ ⟨(0 : ℕ), 0, c + 1, 2, e + 2⟩ := by
  step fm; step fm; step fm; step fm; step fm; step fm; step fm
  finish

-- R3R2R2 drain: (0, 0, c+k, d+1, e) →* (0, 0, c, d+k+1, e+2k)
-- Each round: R3, R2, R2
theorem r3r2r2_drain : ∀ k c d e, ⟨0, 0, c + k, d + 1, e⟩ [fm]⊢* ⟨0, 0, c, d + k + 1, e + 2 * k⟩ := by
  intro k; induction' k with k ih <;> intro c d e
  · exists 0
  · rw [show c + (k + 1) = (c + k) + 1 from by ring]
    step fm; step fm; step fm
    rw [show d + 2 = (d + 1) + 1 from by ring]
    apply stepStar_trans (ih c (d + 1) (e + 2))
    ring_nf; finish

-- Even transition: (0,0,0,2*(k+1),E+(k+1)+1) →⁺ (0,0,0,3*(k+1)+3,E+6*(k+1)+2)
theorem trans_even (k E : ℕ) :
    ⟨(0 : ℕ), 0, 0, 2 * (k + 1), E + (k + 1) + 1⟩ [fm]⊢⁺
    ⟨(0 : ℕ), 0, 0, 3 * (k + 1) + 3, E + 6 * (k + 1) + 2⟩ := by
  rw [show 2 * (k + 1) = 0 + 2 * (k + 1) from by ring]
  apply stepStar_stepPlus_stepPlus (d_to_b (2 * (k + 1)) 0 0 (E + (k + 1) + 1))
  rw [show 0 + 2 * (2 * (k + 1)) = 0 + 4 * (k + 1) from by ring,
      show E + (k + 1) + 1 = (E + 1) + (k + 1) from by ring]
  apply stepStar_stepPlus_stepPlus (full_rounds (k + 1) 0 0 (E + 1))
  rw [show 0 + 3 * (k + 1) = 3 * (k + 1) from by ring]
  apply stepPlus_stepStar_stepPlus (even_tail (3 * (k + 1)) E)
  rw [show 3 * (k + 1) = 0 + 3 * (k + 1) from by ring,
      show 3 = 2 + 1 from by ring]
  apply stepStar_trans (r3r2r2_drain (3 * (k + 1)) 0 2 (E + 2))
  ring_nf; finish

-- Odd transition: (0,0,0,2*k+1,E+k+1) →⁺ (0,0,0,3*k+3,E+6*k+4)
theorem trans_odd (k E : ℕ) :
    ⟨(0 : ℕ), 0, 0, 2 * k + 1, E + k + 1⟩ [fm]⊢⁺
    ⟨(0 : ℕ), 0, 0, 3 * k + 3, E + 6 * k + 4⟩ := by
  rw [show 2 * k + 1 = 0 + (2 * k + 1) from by ring]
  apply stepStar_stepPlus_stepPlus (d_to_b (2 * k + 1) 0 0 (E + k + 1))
  rw [show 0 + 2 * (2 * k + 1) = 2 + 4 * k from by ring,
      show E + k + 1 = (E + 1) + k from by ring]
  apply stepStar_stepPlus_stepPlus (full_rounds k 2 0 (E + 1))
  rw [show 0 + 3 * k = 3 * k from by ring]
  apply stepPlus_stepStar_stepPlus (odd_tail (3 * k) E)
  rw [show 3 * k + 1 = 0 + (3 * k + 1) from by ring,
      show 2 = 1 + 1 from by ring]
  apply stepStar_trans (r3r2r2_drain (3 * k + 1) 0 1 (E + 2))
  ring_nf; finish

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨0, 0, 0, 1, 1⟩) (by execute fm 1)
  apply progress_nonhalt (fm := fm)
    (P := fun q ↦ ∃ d e, q = ⟨0, 0, 0, d, e⟩ ∧ d ≥ 1 ∧ e ≥ d / 2 + 1)
  · intro q ⟨d, e, hq, hd, he⟩; subst hq
    rcases Nat.even_or_odd d with ⟨k, hk⟩ | ⟨k, hk⟩
    · -- d = k + k (even)
      rw [show k + k = 2 * k from by ring] at hk; subst hk
      have hk1 : k ≥ 1 := by omega
      obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
      obtain ⟨E, rfl⟩ : ∃ E, e = E + (k' + 1) + 1 := ⟨e - (k' + 1) - 1, by omega⟩
      refine ⟨_, ⟨3 * (k' + 1) + 3, E + 6 * (k' + 1) + 2, rfl, by omega, by omega⟩, ?_⟩
      exact trans_even k' E
    · -- d = 2k + 1 (odd)
      subst hk
      obtain ⟨E, rfl⟩ : ∃ E, e = E + k + 1 := ⟨e - k - 1, by omega⟩
      refine ⟨_, ⟨3 * k + 3, E + 6 * k + 4, rfl, by omega, by omega⟩, ?_⟩
      exact trans_odd k E
  · exact ⟨1, 1, rfl, by omega, by omega⟩

end Sz22_2003_unofficial_1241
