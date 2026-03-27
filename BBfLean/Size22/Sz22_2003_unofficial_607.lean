import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #607: [35/6, 121/2, 4/55, 3/7, 70/11]

Vector representation:
```
-1 -1  1  1  0
-1  0  0  0  2
 2  0 -1  0 -1
 0  1  0 -1  0
 1  0  1  1 -1
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_607

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a+1, b+1, c, d, e⟩ => some ⟨a, b, c+1, d+1, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b, c, d, e+2⟩
  | ⟨a, b, c+1, d, e+1⟩ => some ⟨a+2, b, c, d, e⟩
  | ⟨a, b, c, d+1, e⟩ => some ⟨a, b+1, c, d, e⟩
  | ⟨a, b, c, d, e+1⟩ => some ⟨a+1, b, c+1, d+1, e⟩
  | _ => none

-- R4 repeated: convert d to b
theorem d_to_b : ⟨0, b, 0, d + k, e⟩ [fm]⊢* ⟨0, b + k, 0, d, e⟩ := by
  have many_step : ∀ k b, ⟨0, b, 0, d + k, e⟩ [fm]⊢* ⟨0, b + k, 0, d, e⟩ := by
    intro k; induction' k with k h <;> intro b
    · finish
    rw [show d + (k + 1) = (d + k) + 1 from by ring]
    step fm
    apply stepStar_trans (h _)
    ring_nf; finish
  exact many_step k b

-- R3R1R1 chain: 3 steps per round, consuming 2 from b and 1 from e
theorem r3r1r1_chain : ⟨0, 2 * k + b, c + 1, d, e + k⟩ [fm]⊢* ⟨0, b, c + k + 1, d + 2 * k, e⟩ := by
  have many_step : ∀ k c d e, ⟨0, 2 * k + b, c + 1, d, e + k⟩ [fm]⊢* ⟨0, b, c + k + 1, d + 2 * k, e⟩ := by
    intro k; induction' k with k h <;> intro c d e
    · simp; finish
    rw [show 2 * (k + 1) + b = (2 * k + b) + 1 + 1 from by ring,
        show e + (k + 1) = (e + k) + 1 from by ring]
    step fm; step fm; step fm
    apply stepStar_trans (h _ _ _)
    ring_nf; finish
  exact many_step k c d e

-- R3R2R2 drain: 3 steps per round, consuming 1 from c and adding 3 to e
theorem r3r2r2_drain : ⟨0, 0, c + k, d, e + 1⟩ [fm]⊢* ⟨0, 0, c, d, e + 3 * k + 1⟩ := by
  have many_step : ∀ k c e, ⟨0, 0, c + k, d, e + 1⟩ [fm]⊢* ⟨0, 0, c, d, e + 3 * k + 1⟩ := by
    intro k; induction' k with k h <;> intro c e
    · simp; finish
    rw [show c + (k + 1) = (c + k) + 1 from by ring]
    step fm; step fm; step fm
    apply stepStar_trans (h _ _)
    ring_nf; finish
  exact many_step k c e

-- Even tail: when b=1 remains after the R3R1R1 chain
theorem even_tail : ⟨0, 1, c + 1, d, e + 1⟩ [fm]⊢* ⟨0, 0, c + 1, d + 1, e + 2⟩ := by
  step fm; step fm; step fm; finish

-- d=0 case: (0,0,0,0,e+1) →⁺ (0,0,0,1,e+5)
theorem d0_step : ⟨0, 0, 0, 0, e + 1⟩ [fm]⊢⁺ ⟨0, 0, 0, 1, e + 5⟩ := by
  execute fm 5

-- Odd d transition: (0, 0, 0, 2m+1, e+m+2) →⁺ (0, 0, 0, 2m+2, e+3m+7)
theorem odd_trans :
    ⟨0, 0, 0, 2 * m + 1, e + m + 2⟩ [fm]⊢⁺ ⟨0, 0, 0, 2 * m + 2, e + 3 * m + 7⟩ := by
  -- R4 chain: (0,0,0,2m+1,e+m+2) →* (0,2m+1,0,0,e+m+2)
  rw [show 2 * m + 1 = 0 + (2 * m + 1) from by ring]
  apply stepStar_stepPlus_stepPlus (d_to_b (b := 0) (d := 0) (e := e + m + 2))
  simp only [Nat.zero_add]
  -- R5, R1: (0,2m+1,0,0,e+m+2) →⁺ (0,2m,2,2,e+m+1)
  step fm; step fm
  -- R3R1R1 chain k=m: (0,2m,2,2,e+m+1) →* (0,0,m+2,2m+2,e+1)
  rw [show (2 : ℕ) * m = 2 * m + 0 from by ring,
      show e + m + 1 = e + 1 + m from by ring]
  refine stepStar_trans (@r3r1r1_chain m 0 1 2 (e + 1)) ?_
  -- After chain: (0, 0, m+2, 2m+2, e+1)
  -- R3R2R2 drain k=m+2: (0,0,m+2,2m+2,e+1) →* (0,0,0,2m+2,e+3m+7)
  rw [show 1 + m + 1 = 0 + (m + 2) from by ring,
      show 2 + 2 * m = 2 * m + 2 from by ring]
  refine stepStar_trans (@r3r2r2_drain 0 (m + 2) (2 * m + 2) e) ?_
  ring_nf; finish

-- Even d transition: (0, 0, 0, 2m+2, e+m+3) →⁺ (0, 0, 0, 2m+3, e+3m+9)
theorem even_trans :
    ⟨0, 0, 0, 2 * m + 2, e + m + 3⟩ [fm]⊢⁺ ⟨0, 0, 0, 2 * m + 3, e + 3 * m + 9⟩ := by
  -- R4 chain: (0,0,0,2m+2,e+m+3) →* (0,2m+2,0,0,e+m+3)
  rw [show 2 * m + 2 = 0 + (2 * m + 2) from by ring]
  apply stepStar_stepPlus_stepPlus (d_to_b (b := 0) (d := 0) (e := e + m + 3))
  simp only [Nat.zero_add]
  -- R5, R1: (0,2m+2,0,0,e+m+3) →⁺ (0,2m+1,2,2,e+m+2)
  step fm; step fm
  -- R3R1R1 chain k=m: (0,2m+1,2,2,e+m+2) →* (0,1,m+2,2m+2,e+2)
  rw [show (2 : ℕ) * m + 1 = 2 * m + 1 from by ring,
      show e + m + 2 = e + 2 + m from by ring]
  refine stepStar_trans (@r3r1r1_chain m 1 1 2 (e + 2)) ?_
  -- After chain: (0, 1, m+2, 2m+2, e+2)
  -- Even tail: (0, 1, m+2, 2m+2, e+2) →* (0, 0, m+2, 2m+3, e+3)
  rw [show 1 + m + 1 = (m + 1) + 1 from by ring,
      show 2 + 2 * m = 2 * m + 2 from by ring,
      show e + 2 = e + 1 + 1 from by ring]
  refine stepStar_trans (@even_tail (m + 1) (2 * m + 2) (e + 1)) ?_
  -- R3R2R2 drain k=m+2: (0,0,m+2,2m+3,e+3) →* (0,0,0,2m+3,e+3m+9)
  rw [show (m + 1) + 1 = 0 + (m + 2) from by ring,
      show 2 * m + 2 + 1 = 2 * m + 3 from by ring,
      show e + 1 + 2 = e + 2 + 1 from by ring]
  refine stepStar_trans (@r3r2r2_drain 0 (m + 2) (2 * m + 3) (e + 2)) ?_
  ring_nf; finish

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨0, 0, 0, 0, 2⟩) (by execute fm 1)
  apply progress_nonhalt (fm := fm)
    (P := fun q ↦ ∃ d E, q = ⟨0, 0, 0, d, E⟩ ∧ E ≥ d + 2)
  · intro c ⟨d, E, hq, hE⟩; subst hq
    rcases d with _ | d
    · -- d = 0
      obtain ⟨e, rfl⟩ : ∃ e, E = e + 1 := ⟨E - 1, by omega⟩
      exact ⟨⟨0, 0, 0, 1, e + 5⟩, ⟨1, e + 5, rfl, by omega⟩, d0_step⟩
    rcases Nat.even_or_odd d with ⟨K, hK⟩ | ⟨K, hK⟩
    · -- d even: d = 2K, so d+1 = 2K+1 (odd)
      rw [show K + K = 2 * K from by ring] at hK; subst hK
      obtain ⟨e, rfl⟩ : ∃ e, E = e + K + 2 := ⟨E - K - 2, by omega⟩
      exact ⟨⟨0, 0, 0, 2 * K + 2, e + 3 * K + 7⟩,
        ⟨2 * K + 2, e + 3 * K + 7, rfl, by omega⟩, odd_trans⟩
    · -- d odd: d = 2K+1, so d+1 = 2K+2 (even)
      subst hK
      obtain ⟨e, rfl⟩ : ∃ e, E = e + K + 3 := ⟨E - K - 3, by omega⟩
      exact ⟨⟨0, 0, 0, 2 * K + 3, e + 3 * K + 9⟩,
        ⟨2 * K + 3, e + 3 * K + 9, rfl, by omega⟩, even_trans⟩
  · exact ⟨0, 2, rfl, by omega⟩
