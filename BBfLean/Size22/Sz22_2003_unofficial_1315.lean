import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #1315: [63/10, 143/2, 28/33, 5/7, 3/13]

Vector representation:
```
-1  2 -1  1  0  0
-1  0  0  0  1  1
 2 -1  0  1 -1  0
 0  0  1 -1  0  0
 0  1  0  0  0 -1
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_1315

def Q := ℕ × ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a+1, b, c+1, d, e, f⟩ => some ⟨a, b+2, c, d+1, e, f⟩
  | ⟨a+1, b, c, d, e, f⟩ => some ⟨a, b, c, d, e+1, f+1⟩
  | ⟨a, b+1, c, d, e+1, f⟩ => some ⟨a+2, b, c, d+1, e, f⟩
  | ⟨a, b, c, d+1, e, f⟩ => some ⟨a, b, c+1, d, e, f⟩
  | ⟨a, b, c, d, e, f+1⟩ => some ⟨a, b+1, c, d, e, f⟩
  | _ => none

-- R4 repeated: move d to c
theorem d_to_c : ∀ k c d e f, ⟨(0 : ℕ), (0 : ℕ), c, d + k, e, f⟩ [fm]⊢*
    ⟨(0 : ℕ), (0 : ℕ), c + k, d, e, f⟩ := by
  intro k; induction' k with k ih
  · intro c d e f; exists 0
  · intro c d e f
    rw [show d + (k + 1) = (d + k) + 1 from by ring]
    step fm
    apply stepStar_trans (ih (c + 1) d e f)
    ring_nf; finish

-- R3,R1,R1 chain: k rounds
theorem r3r1r1_chain : ∀ k B C D E F, ⟨(0 : ℕ), B + 1, C + 2 * k, D, E + k, F⟩ [fm]⊢*
    ⟨(0 : ℕ), B + 3 * k + 1, C, D + 3 * k, E, F⟩ := by
  intro k; induction' k with k ih
  · intro B C D E F; simp; exists 0
  · intro B C D E F
    rw [show C + 2 * (k + 1) = (C + 2) + 2 * k from by ring,
        show E + (k + 1) = (E + 1) + k from by ring]
    apply stepStar_trans (ih B (C + 2) D (E + 1) F)
    rw [show B + 3 * k + 1 = (B + 3 * k) + 1 from by ring]
    step fm; step fm; step fm
    rw [show B + 3 * k + 4 = B + 3 * (k + 1) + 1 from by ring,
        show D + 3 * k + 3 = D + 3 * (k + 1) from by ring]
    finish

-- R3,R2,R2 drain chain: k rounds
theorem r3r2r2_chain : ∀ k D E F, ⟨(0 : ℕ), k, (0 : ℕ), D, E + 1, F⟩ [fm]⊢*
    ⟨(0 : ℕ), (0 : ℕ), (0 : ℕ), D + k, E + k + 1, F + 2 * k⟩ := by
  intro k; induction' k with k ih
  · intro D E F; simp; exists 0
  · intro D E F
    rw [show (k + 1 : ℕ) = k + 1 from rfl]
    step fm; step fm; step fm
    rw [show E + 2 = (E + 1) + 1 from by ring]
    apply stepStar_trans (ih (D + 1) (E + 1) (F + 2))
    rw [show D + 1 + k = D + (k + 1) from by ring,
        show E + 1 + k + 1 = E + (k + 1) + 1 from by ring,
        show F + 2 + 2 * k = F + 2 * (k + 1) from by ring]
    finish

-- Handle c=1 remainder: R3,R1,R2
theorem c1_handle : ∀ B D E F, ⟨(0 : ℕ), B + 1, 1, D, E + 1, F⟩ [fm]⊢*
    ⟨(0 : ℕ), B + 2, (0 : ℕ), D + 2, E + 1, F + 1⟩ := by
  intro B D E F
  step fm; step fm; step fm; finish

-- Even case: d = 2(m+1), m >= 0
-- Transition: (0,0,0, 2(m+1), e, f) ->+ (0,0,0, 6m+7, e+2m+3, f+6m+7)
-- Requires e >= m+2, f >= 1
theorem transition_even (m : ℕ) (E F : ℕ) :
    ⟨(0 : ℕ), (0 : ℕ), 0, 2 * m + 2, E + m + 2, F + 1⟩ [fm]⊢⁺
    ⟨(0 : ℕ), (0 : ℕ), 0, 6 * m + 7, E + 3 * m + 5, F + 6 * m + 8⟩ := by
  -- d to c
  rw [show 2 * m + 2 = 0 + (2 * m + 2) from by ring]
  apply stepStar_stepPlus_stepPlus (d_to_c (2 * m + 2) 0 0 (E + m + 2) (F + 1))
  rw [show 0 + (2 * m + 2) = (2 * m) + 2 from by ring,
      show E + m + 2 = (E + m + 1) + 1 from by ring]
  -- R5, R3, R1, R1
  step fm
  rw [show 2 * m + 2 = (2 * m + 1) + 1 from by ring]
  step fm
  rw [show 2 * m + 1 + 1 = (2 * m) + 2 from by ring]
  step fm; step fm
  -- State: (0, 4, 2m, 3, E+m+1, F)
  rw [show (4 : ℕ) = 3 + 1 from by ring,
      show 2 * m = 0 + 2 * m from by ring,
      show E + m + 1 = (E + 1) + m from by ring]
  apply stepStar_trans (r3r1r1_chain m 3 0 3 (E + 1) F)
  rw [show 3 + 3 * m + 1 = 3 * m + 4 from by ring,
      show 3 + 3 * m = 3 * m + 3 from by ring]
  -- State: (0, 3m+4, 0, 3m+3, E+1, F)
  -- Drain
  rw [show E + 1 = E + 1 from rfl]
  apply stepStar_trans (r3r2r2_chain (3 * m + 4) (3 * m + 3) E F)
  rw [show 3 * m + 3 + (3 * m + 4) = 6 * m + 7 from by ring,
      show E + (3 * m + 4) + 1 = E + 3 * m + 5 from by ring,
      show F + 2 * (3 * m + 4) = F + 6 * m + 8 from by ring]
  finish

-- Odd case: d = 2m+3, m >= 0
-- Transition: (0,0,0, 2m+3, e, f) ->+ (0,0,0, 6m+10, e+2m+4, f+6m+10)
-- Requires e >= m+2, f >= 1
theorem transition_odd (m : ℕ) (E F : ℕ) :
    ⟨(0 : ℕ), (0 : ℕ), 0, 2 * m + 3, E + m + 2, F + 1⟩ [fm]⊢⁺
    ⟨(0 : ℕ), (0 : ℕ), 0, 6 * m + 10, E + 3 * m + 6, F + 6 * m + 11⟩ := by
  -- d to c
  rw [show 2 * m + 3 = 0 + (2 * m + 3) from by ring]
  apply stepStar_stepPlus_stepPlus (d_to_c (2 * m + 3) 0 0 (E + m + 2) (F + 1))
  rw [show 0 + (2 * m + 3) = (2 * m + 1) + 2 from by ring,
      show E + m + 2 = (E + m + 1) + 1 from by ring]
  -- R5, R3, R1, R1
  step fm
  rw [show 2 * m + 1 + 2 = (2 * m + 2) + 1 from by ring]
  step fm
  rw [show 2 * m + 2 = (2 * m + 1) + 1 from by ring]
  step fm; step fm
  -- State: (0, 4, 2m+1, 3, E+m+1, F)
  rw [show (4 : ℕ) = 3 + 1 from by ring,
      show 2 * m + 1 = 1 + 2 * m from by ring,
      show E + m + 1 = (E + 1) + m from by ring]
  apply stepStar_trans (r3r1r1_chain m 3 1 3 (E + 1) F)
  rw [show 3 + 3 * m + 1 = (3 * m + 3) + 1 from by ring,
      show 3 + 3 * m = 3 * m + 3 from by ring]
  -- c1_handle
  apply stepStar_trans (c1_handle (3 * m + 3) (3 * m + 3) E F)
  rw [show 3 * m + 3 + 2 = 3 * m + 5 from by ring,
      show 3 * m + 3 + 2 = 3 * m + 5 from by ring]
  -- State: (0, 3m+5, 0, 3m+5, E+1, F+1)
  -- Drain
  rw [show E + 1 = E + 1 from rfl]
  apply stepStar_trans (r3r2r2_chain (3 * m + 5) (3 * m + 5) E (F + 1))
  rw [show 3 * m + 5 + (3 * m + 5) = 6 * m + 10 from by ring,
      show E + (3 * m + 5) + 1 = E + 3 * m + 6 from by ring,
      show F + 1 + 2 * (3 * m + 5) = F + 6 * m + 11 from by ring]
  finish

-- Main transition
theorem main_transition (d e f : ℕ) (hd : d ≥ 2) (he : 2 * e ≥ d + 2) (hf : f ≥ 1) :
    ⟨(0 : ℕ), (0 : ℕ), 0, d, e, f⟩ [fm]⊢⁺
    ⟨(0 : ℕ), (0 : ℕ), 0, 3 * d + 1, e + d + 1, f + 3 * d + 1⟩ := by
  obtain ⟨E, rfl⟩ : ∃ E, e = E + d / 2 + 1 := ⟨e - d / 2 - 1, by omega⟩
  obtain ⟨F, rfl⟩ : ∃ F, f = F + 1 := ⟨f - 1, by omega⟩
  rcases Nat.even_or_odd d with ⟨K, hK⟩ | ⟨K, hK⟩
  · rw [show K + K = 2 * K from by ring] at hK
    obtain ⟨m, rfl⟩ : ∃ m, K = m + 1 := ⟨K - 1, by omega⟩
    subst hK
    rw [show E + 2 * (m + 1) / 2 + 1 = E + m + 2 from by omega]
    have h := transition_even m E F
    rw [show 6 * m + 7 = 3 * (2 * m + 2) + 1 from by ring,
        show E + 3 * m + 5 = (E + m + 2) + (2 * m + 2) + 1 from by ring,
        show F + 6 * m + 8 = (F + 1) + 3 * (2 * m + 2) + 1 from by ring,
        show 2 * m + 2 = 2 * (m + 1) from by ring] at h
    exact h
  · obtain ⟨m, rfl⟩ : ∃ m, K = m + 1 := ⟨K - 1, by omega⟩
    subst hK
    rw [show E + (2 * (m + 1) + 1) / 2 + 1 = E + m + 2 from by omega]
    have h := transition_odd m E F
    rw [show 6 * m + 10 = 3 * (2 * m + 3) + 1 from by ring,
        show E + 3 * m + 6 = (E + m + 2) + (2 * m + 3) + 1 from by ring,
        show F + 6 * m + 11 = (F + 1) + 3 * (2 * m + 3) + 1 from by ring] at h
    exact h

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨0, 0, 0, 4, 4, 6⟩) (by execute fm 16)
  apply progress_nonhalt (fm := fm)
    (P := fun q ↦ ∃ d e f, q = ⟨0, 0, 0, d, e, f⟩ ∧ d ≥ 2 ∧ 2 * e ≥ d + 2 ∧ f ≥ 1)
  · intro c ⟨d, e, f, hq, hd, he, hf⟩; subst hq
    refine ⟨⟨0, 0, 0, 3 * d + 1, e + d + 1, f + 3 * d + 1⟩,
      ⟨3 * d + 1, e + d + 1, f + 3 * d + 1, rfl, ?_, ?_, ?_⟩,
      main_transition d e f hd he hf⟩
    · omega
    · omega
    · omega
  · exact ⟨4, 4, 6, rfl, by omega, by omega, by omega⟩

end Sz22_2003_unofficial_1315
