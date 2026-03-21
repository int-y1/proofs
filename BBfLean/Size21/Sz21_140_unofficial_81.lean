import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz21_140_unofficial #81: [5/6, 44/35, 539/2, 3/11, 5/7]

Vector representation:
```
-1 -1  1  0  0
 2  0 -1 -1  1
-1  0  0  2  1
 0  1  0  0 -1
 0  0  1 -1  0
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz21_140_unofficial_81

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a+1, b+1, c, d, e⟩ => some ⟨a, b, c+1, d, e⟩
  | ⟨a, b, c+1, d+1, e⟩ => some ⟨a+2, b, c, d, e+1⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b, c, d+2, e+1⟩
  | ⟨a, b, c, d, e+1⟩ => some ⟨a, b+1, c, d, e⟩
  | ⟨a, b, c, d+1, e⟩ => some ⟨a, b, c+1, d, e⟩
  | _ => none

-- R4 chain: e → b
theorem e_to_b : ∀ k, ∀ b d, ⟨0, b, 0, d, k⟩ [fm]⊢* ⟨0, b + k, 0, d, 0⟩ := by
  intro k; induction' k with k h <;> intro b d
  · exists 0
  -- State: (0, b, 0, d, k+1). R4 pattern: e+1 = k+1. ✓
  step fm  -- R4: → (0, b+1, 0, d, k)
  apply stepStar_trans (h _ _)
  ring_nf; finish

-- R3 chain: a → d,e
theorem a_to_de : ∀ k, ∀ a d e, ⟨a + k, 0, 0, d, e⟩ [fm]⊢* ⟨a, 0, 0, d + 2 * k, e + k⟩ := by
  intro k; induction' k with k h <;> intro a d e
  · exists 0
  rw [← Nat.add_assoc]
  step fm
  apply stepStar_trans (h _ _ _)
  ring_nf; finish

-- R1R1R2 chain: 3 steps per round
-- (2, B+2k, C, D+k, E) →* (2, B, C+k, D, E+k)
theorem r1r1r2_chain : ∀ k, ∀ B C D E, ⟨2, B + 2 * k, C, D + k, E⟩ [fm]⊢* ⟨2, B, C + k, D, E + k⟩ := by
  intro k; induction' k with k h <;> intro B C D E
  · exists 0
  -- Rewrite to expose R1 pattern: (a+1, b+1, c, d, e)
  rw [show B + 2 * (k + 1) = (B + 1 + 2 * k) + 1 from by ring,
      show D + (k + 1) = (D + k) + 1 from by ring,
      show (2 : ℕ) = (1 : ℕ) + 1 from by ring]
  step fm  -- R1: (1+1, (B+1+2k)+1, C, (D+k)+1, E) → (1, B+1+2k, C+1, (D+k)+1, E)
  rw [show B + 1 + 2 * k = (B + 2 * k) + 1 from by ring]
  step fm  -- R1: (1, (B+2k)+1, C+1, (D+k)+1, E) → (0, B+2k, C+2, (D+k)+1, E)
  -- Now R2: (0, B+2k, C+2, (D+k)+1, E) = (0, B+2k, (C+1)+1, (D+k)+1, E)
  rw [show C + 2 = (C + 1) + 1 from by ring]
  step fm  -- R2: → (2, B+2k, C+1, D+k, E+1)
  apply stepStar_trans (h _ _ _ _)
  ring_nf; finish

-- Process lemma: (A, 0, C, D, E) with A >= 1 reaches (0, 0, 0, D+2A+3C, E+A+3C)
theorem process : ∀ C, ∀ A D E, A ≥ 1 →
    ⟨A, 0, C, D, E⟩ [fm]⊢* ⟨0, 0, 0, D + 2 * A + 3 * C, E + A + 3 * C⟩ := by
  intro C; induction' C with C ih <;> intro A D E hA
  · -- C=0: R3 chain
    simp only [Nat.mul_zero, Nat.add_zero]
    obtain ⟨k, rfl⟩ : ∃ k, A = k + 1 := ⟨A - 1, by omega⟩
    have h := a_to_de (k + 1) 0 D E
    simp only [Nat.zero_add] at h
    refine stepStar_trans h ?_
    ring_nf; finish
  · -- C+1: case split on D
    rcases D with _ | D'
    · -- D = 0: R3 step, then R2 step, then IH
      obtain ⟨k, rfl⟩ : ∃ k, A = k + 1 := ⟨A - 1, by omega⟩
      step fm  -- R3
      step fm  -- R2
      apply stepStar_trans (ih (k + 2) 1 (E + 2) (by omega))
      ring_nf; finish
    · -- D = D'+1: R2 step, then IH
      step fm  -- R2
      apply stepStar_trans (ih (A + 2) D' (E + 1) (by omega))
      ring_nf; finish

-- Middle transition for e even (e = 2m, m >= 1)
-- From (2, 2m, 0, d, 1) with d >= m:
-- Chain: (2, 0, m, d-m, m+1), then process.
theorem middle_even (m : ℕ) (_hm : m ≥ 1) (d : ℕ) (hd : d ≥ m) :
    ⟨2, 2 * m, 0, d, 1⟩ [fm]⊢* ⟨0, 0, 0, d + 2 * m + 4, 4 * m + 3⟩ := by
  obtain ⟨d', rfl⟩ : ∃ d', d = d' + m := ⟨d - m, by omega⟩
  have h1 := r1r1r2_chain m 0 0 d' 1
  simp only [Nat.zero_add] at h1
  refine stepStar_trans h1 ?_
  -- goal: (2, 0, m, d', 1 + m) ⊢* (0, 0, 0, d' + m + 2*m + 4, 4*m + 3)
  -- = (2, 0, m, d', m+1) ⊢* (0, 0, 0, d'+3m+4, 4m+3)
  -- process gives: D+2A+3C = d'+4+3m, E+A+3C = (1+m)+2+3m = 3+4m
  -- need to match (1+m) to E in process call
  rw [show (1 : ℕ) + m = m + 1 from by ring]
  apply stepStar_trans (process m 2 d' (m + 1) (by omega))
  ring_nf; finish

-- Middle transition for e odd (e = 2m+1, m >= 0)
-- From (2, 2m+1, 0, d, 1) with d >= m:
-- Chain: (2, 1, m, d-m, m+1), R1: (1, 0, m+1, d-m, m+1), then process.
theorem middle_odd (m : ℕ) (d : ℕ) (hd : d ≥ m) :
    ⟨2, 2 * m + 1, 0, d, 1⟩ [fm]⊢* ⟨0, 0, 0, d + 2 * m + 5, 4 * m + 5⟩ := by
  obtain ⟨d', rfl⟩ : ∃ d', d = d' + m := ⟨d - m, by omega⟩
  -- Chain: (2, 1+2*m, 0, d'+m, 1) →* (2, 1, m, d', 1+m)
  rw [show 2 * m + 1 = 1 + 2 * m from by ring]
  have h1 := r1r1r2_chain m 1 0 d' 1
  simp only [Nat.zero_add] at h1
  refine stepStar_trans h1 ?_
  -- (2, 1, m, d', 1+m)
  rw [show (1 : ℕ) + m = m + 1 from by ring]
  -- R1: (2, 1, m, d', m+1) → (1, 0, m+1, d', m+1)
  rw [show (2 : ℕ) = 1 + 1 from by ring, show (1 : ℕ) = 0 + 1 from by ring]
  apply stepStar_trans (c₂ := ⟨1, 0, m + 1, d', m + 1⟩)
  · step fm; finish
  -- Process: (1, 0, m+1, d', m+1) → (0, 0, 0, d'+2+3(m+1), (m+1)+1+3(m+1))
  apply stepStar_trans (process (m + 1) 1 d' (m + 1) (by omega))
  ring_nf; finish

-- Full cycle transition
theorem main_trans (d e : ℕ) (hd : d ≥ 2) (he : e ≥ 1) (hinv : 2 * d ≥ e + 3) :
    ⟨0, 0, 0, d, e⟩ [fm]⊢⁺ ⟨0, 0, 0, d + e + 2, 2 * e + 3⟩ := by
  -- Phase 1: R4 chain: (0, 0, 0, d, e) →* (0, e, 0, d, 0)
  apply stepStar_stepPlus_stepPlus (e_to_b e 0 d)
  simp only [Nat.zero_add]
  -- Phase 2: R5 (gives stepPlus via step)
  obtain ⟨d', rfl⟩ : ∃ d', d = d' + 2 := ⟨d - 2, by omega⟩
  rw [show d' + 2 = (d' + 1) + 1 from by ring]
  apply step_stepStar_stepPlus
  · show fm ⟨0, e, 0, (d' + 1) + 1, 0⟩ = some ⟨0, e, 1, d' + 1, 0⟩; simp [fm]
  -- R2 step
  apply stepStar_trans (c₂ := ⟨2, e, 0, d', 1⟩)
  · rw [show d' + 1 = d' + 1 from rfl]
    step fm; finish
  -- Now: (2, e, 0, d', 1) ⊢* target
  -- Phase 3: parity of e
  rcases Nat.even_or_odd e with ⟨m, hm⟩ | ⟨m, hm⟩
  · rw [show m + m = 2 * m from by ring] at hm; subst hm
    refine stepStar_trans (middle_even m (by omega) d' (by omega)) ?_
    ring_nf; finish
  · subst hm
    refine stepStar_trans (middle_odd m d' (by omega)) ?_
    ring_nf; finish

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨0, 0, 0, 2, 1⟩) (by execute fm 1)
  apply progress_nonhalt (fm := fm)
    (P := fun q ↦ ∃ d e, q = ⟨0, 0, 0, d, e⟩ ∧ d ≥ 2 ∧ e ≥ 1 ∧ 2 * d ≥ e + 3)
  · intro c ⟨d, e, hq, hd, he, hinv⟩; subst hq
    exact ⟨⟨0, 0, 0, d + e + 2, 2 * e + 3⟩,
      ⟨d + e + 2, 2 * e + 3, rfl, by omega, by omega, by omega⟩,
      main_trans d e hd he hinv⟩
  · exact ⟨2, 1, rfl, by omega, by omega, by omega⟩

end Sz21_140_unofficial_81
