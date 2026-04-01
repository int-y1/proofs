import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #1289: [63/10, 11/2, 28/33, 5/7, 6/11]

Vector representation:
```
-1  2 -1  1  0
-1  0  0  0  1
 2 -1  0  1 -1
 0  0  1 -1  0
 1  1  0  0 -1
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_1289

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a+1, b, c+1, d, e⟩ => some ⟨a, b+2, c, d+1, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b, c, d, e+1⟩
  | ⟨a, b+1, c, d, e+1⟩ => some ⟨a+2, b, c, d+1, e⟩
  | ⟨a, b, c, d+1, e⟩ => some ⟨a, b, c+1, d, e⟩
  | ⟨a, b, c, d, e+1⟩ => some ⟨a+1, b+1, c, d, e⟩
  | _ => none

-- R4 repeated: (0, 0, c, d+k, e) →* (0, 0, c+k, d, e)
theorem d_to_c : ∀ k c d e, ⟨(0 : ℕ), 0, c, d + k, e⟩ [fm]⊢* ⟨(0 : ℕ), 0, c + k, d, e⟩ := by
  intro k; induction' k with k ih <;> intro c d e
  · exists 0
  · rw [show d + (k + 1) = (d + k) + 1 from by ring]
    step fm
    apply stepStar_trans (ih (c + 1) d e)
    ring_nf; finish

-- R3+R1+R1 chain: (0, B+1, C+2k, D', E'+k) →* (0, B+1+3k, C, D'+3k, E')
theorem r3r1r1_chain : ∀ k, ∀ B C D' E',
    ⟨(0 : ℕ), B + 1, C + 2 * k, D', E' + k⟩ [fm]⊢*
    ⟨(0 : ℕ), B + 1 + 3 * k, C, D' + 3 * k, E'⟩ := by
  intro k; induction' k with k ih <;> intro B C D' E'
  · simp; exists 0
  · rw [show C + 2 * (k + 1) = (C + 2 * k + 1) + 1 from by ring,
        show E' + (k + 1) = (E' + k) + 1 from by ring]
    step fm; step fm; step fm
    rw [show B + 4 = (B + 3) + 1 from by ring]
    apply stepStar_trans (ih (B + 3) C (D' + 3) E')
    ring_nf; finish

-- R3+R2+R2 chain: (0, k, 0, D', E'+1) →* (0, 0, 0, D'+k, E'+1+k)
theorem r3r2r2_chain : ∀ k D' E',
    ⟨(0 : ℕ), k, 0, D', E' + 1⟩ [fm]⊢* ⟨(0 : ℕ), 0, 0, D' + k, E' + 1 + k⟩ := by
  intro k; induction' k with k ih <;> intro D' E'
  · exists 0
  · step fm; step fm; step fm
    rw [show E' + 2 = (E' + 1) + 1 from by ring]
    apply stepStar_trans (ih (D' + 1) (E' + 1))
    ring_nf; finish

-- D odd: (0, 0, 0, 2m+1, E+m+2) →⁺ (0, 0, 0, 6m+4, E+3m+4)
theorem main_trans_odd (m : ℕ) (E : ℕ) :
    ⟨(0 : ℕ), 0, 0, 2 * m + 1, E + m + 2⟩ [fm]⊢⁺
    ⟨(0 : ℕ), 0, 0, 6 * m + 4, E + 3 * m + 4⟩ := by
  -- Phase 1: R4 drain
  rw [show 2 * m + 1 = 0 + (2 * m + 1) from by ring]
  apply stepStar_stepPlus_stepPlus (d_to_c (2 * m + 1) 0 0 (E + m + 2))
  rw [show (0 : ℕ) + (2 * m + 1) = (2 * m) + 1 from by ring]
  -- Phase 2: R5 + R1
  rw [show E + m + 2 = (E + m + 1) + 1 from by ring]
  step fm
  step fm
  -- State: (0, 3, 2m, 1, E+m+1)
  -- Phase 3: R3+R1+R1 × m rounds
  rw [show (3 : ℕ) = 2 + 1 from by ring,
      show 2 * m = 0 + 2 * m from by ring,
      show E + m + 1 = (E + 1) + m from by ring]
  apply stepStar_trans (r3r1r1_chain m 2 0 1 (E + 1))
  rw [show 2 + 1 + 3 * m = 3 * m + 3 from by ring,
      show 1 + 3 * m = 3 * m + 1 from by ring]
  -- State: (0, 3m+3, 0, 3m+1, E+1)
  -- Phase 4: R3+R2+R2 × (3m+3) rounds
  apply stepStar_trans (r3r2r2_chain (3 * m + 3) (3 * m + 1) E)
  ring_nf; finish

-- D even: (0, 0, 0, 2m+2, E+m+2) →⁺ (0, 0, 0, 6m+7, E+3m+5)
theorem main_trans_even (m : ℕ) (E : ℕ) :
    ⟨(0 : ℕ), 0, 0, 2 * m + 2, E + m + 2⟩ [fm]⊢⁺
    ⟨(0 : ℕ), 0, 0, 6 * m + 7, E + 3 * m + 5⟩ := by
  -- Phase 1: R4 drain
  rw [show 2 * m + 2 = 0 + (2 * m + 2) from by ring]
  apply stepStar_stepPlus_stepPlus (d_to_c (2 * m + 2) 0 0 (E + m + 2))
  rw [show (0 : ℕ) + (2 * m + 2) = (2 * m + 1) + 1 from by ring]
  -- Phase 2: R5 + R1
  rw [show E + m + 2 = (E + m + 1) + 1 from by ring]
  step fm
  step fm
  -- State: (0, 3, 2m+1, 1, E+m+1)
  -- Phase 3: R3+R1+R1 × m rounds
  rw [show (3 : ℕ) = 2 + 1 from by ring,
      show 2 * m + 1 = 1 + 2 * m from by ring,
      show E + m + 1 = (E + 1) + m from by ring]
  apply stepStar_trans (r3r1r1_chain m 2 1 1 (E + 1))
  rw [show 2 + 1 + 3 * m = 3 * m + 3 from by ring,
      show 1 + 3 * m = 3 * m + 1 from by ring]
  -- State: (0, 3m+3, 1, 3m+1, E+1)
  -- Phase 4: trailing R3+R1+R2
  rw [show 3 * m + 3 = (3 * m + 2) + 1 from by ring,
      show E + 1 = E + 1 from rfl]
  step fm  -- R3: (2, 3m+2, 1, 3m+2, E)
  step fm  -- R1: (1, 3m+4, 0, 3m+3, E)
  step fm  -- R2: (0, 3m+4, 0, 3m+3, E+1)
  -- Phase 5: R3+R2+R2 × (3m+4) rounds
  apply stepStar_trans (r3r2r2_chain (3 * m + 4) (3 * m + 3) E)
  ring_nf; finish

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨0, 0, 0, 4, 4⟩) (by execute fm 18)
  apply progress_nonhalt (fm := fm)
    (P := fun q ↦ ∃ d e, q = ⟨0, 0, 0, d, e⟩ ∧ d ≥ 1 ∧ e ≥ d / 2 + 2)
  · intro c ⟨d, e, hq, hd, he⟩; subst hq
    rcases Nat.even_or_odd d with ⟨m, hm⟩ | ⟨m, hm⟩
    · -- d even: d = m + m = 2m
      rw [show m + m = 2 * m from by ring] at hm; subst hm
      have hm1 : m ≥ 1 := by omega
      obtain ⟨m', rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
      obtain ⟨E, rfl⟩ : ∃ E, e = E + m' + 2 := ⟨e - m' - 2, by omega⟩
      refine ⟨⟨0, 0, 0, 6 * m' + 7, E + 3 * m' + 5⟩,
        ⟨6 * m' + 7, E + 3 * m' + 5, rfl, by omega, by omega⟩, ?_⟩
      show ⟨(0 : ℕ), 0, 0, 2 * (m' + 1), E + m' + 2⟩ [fm]⊢⁺ _
      rw [show 2 * (m' + 1) = 2 * m' + 2 from by ring]
      exact main_trans_even m' E
    · -- d odd: d = 2m + 1
      subst hm
      obtain ⟨E, rfl⟩ : ∃ E, e = E + m + 2 := ⟨e - m - 2, by omega⟩
      refine ⟨⟨0, 0, 0, 6 * m + 4, E + 3 * m + 4⟩,
        ⟨6 * m + 4, E + 3 * m + 4, rfl, by omega, by omega⟩, ?_⟩
      exact main_trans_odd m E
  · exact ⟨4, 4, rfl, by omega, by omega⟩

end Sz22_2003_unofficial_1289
