import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #38: [1/15, 36/77, 49/3, 5/49, 33/2]

Vector representation:
```
 0 -1 -1  0  0
 2  2  0 -1 -1
 0 -1  0  2  0
 0  0  1 -2  0
-1  1  0  0  1
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_38

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a, b+1, c+1, d, e⟩ => some ⟨a, b, c, d, e⟩
  | ⟨a, b, c, d+1, e+1⟩ => some ⟨a+2, b+2, c, d, e⟩
  | ⟨a, b+1, c, d, e⟩ => some ⟨a, b, c, d+2, e⟩
  | ⟨a, b, c, d+2, e⟩ => some ⟨a, b, c+1, d, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b+1, c, d, e+1⟩
  | _ => none

-- R3-R2-R2 chain: k rounds, each: R3 (b-=1, d+=2), R2 (a+=2, b+=2, d-=1, e-=1), R2 again
-- Net per round: a+=4, b+=3, e-=2
-- (A, B+1, 0, 0, E+2k) ⊢* (A+4k, B+1+3k, 0, 0, E)
theorem r3r2r2_chain : ∀ k, ∀ A B E,
    ⟨A, B+1, 0, 0, E+2*k⟩ [fm]⊢* ⟨A+4*k, B+1+3*k, 0, 0, E⟩ := by
  intro k; induction' k with k ih <;> intro A B E
  · ring_nf; finish
  -- One R3-R2-R2 round then apply ih
  have h1 : ⟨A, B+1, 0, 0, E+2*(k+1)⟩ [fm]⊢ ⟨A, B, 0, 2, E+2*(k+1)⟩ := by simp [fm]
  have h2 : ⟨A, B, 0, 2, E+2*(k+1)⟩ [fm]⊢ ⟨A+2, B+2, 0, 1, E+2*k+1⟩ := by
    show fm ⟨A, B, 0, 2, E + 2 * (k + 1)⟩ = _
    rw [show E + 2 * (k + 1) = (E + 2 * k + 1) + 1 from by ring]
    simp [fm]
  have h3 : ⟨A+2, B+2, 0, 1, E+2*k+1⟩ [fm]⊢ ⟨A+4, B+4, 0, 0, E+2*k⟩ := by
    show fm ⟨A + 2, B + 2, 0, 1, E + 2 * k + 1⟩ = _
    rw [show E + 2 * k + 1 = (E + 2 * k) + 1 from by ring]
    simp [fm]
  apply stepStar_trans (step_stepStar h1)
  apply stepStar_trans (step_stepStar h2)
  apply stepStar_trans (step_stepStar h3)
  apply stepStar_trans (ih (A + 4) (B + 3) E)
  ring_nf; finish

-- R3 drain with e=0: moves b into d
theorem r3_drain_e0 : ∀ k, ∀ A D,
    ⟨A, k, 0, D, 0⟩ [fm]⊢* ⟨A, 0, 0, D+2*k, 0⟩ := by
  intro k; induction' k with k ih <;> intro A D
  · exists 0
  have h1 : ⟨A, k+1, 0, D, 0⟩ [fm]⊢ ⟨A, k, 0, D+2, 0⟩ := by simp [fm]
  apply stepStar_trans (step_stepStar h1)
  apply stepStar_trans (ih A (D+2))
  ring_nf; finish

-- R4 drain: converts pairs of d into c (b=0, e=0)
theorem r4_drain : ∀ k, ∀ A C D,
    ⟨A, 0, C, D+2*k, 0⟩ [fm]⊢* ⟨A, 0, C+k, D, 0⟩ := by
  intro k; induction' k with k ih <;> intro A C D
  · exists 0
  rw [show D + 2 * (k + 1) = (D + 2 * k) + 2 from by ring]
  step fm
  apply stepStar_trans (ih _ _ _)
  ring_nf; finish

-- R5-R1 drain: alternating R5, R1 (d=0, b=0 initially)
theorem r5r1_drain : ∀ k, ∀ A E,
    ⟨A+k, 0, k, 0, E⟩ [fm]⊢* ⟨A, 0, 0, 0, E+k⟩ := by
  intro k; induction' k with k ih <;> intro A E
  · exists 0
  rw [show A + (k + 1) = (A + k) + 1 from by ring]
  step fm
  step fm
  apply stepStar_trans (ih _ _)
  ring_nf; finish

-- Tail: (A+1, 0, C+3, 1, 0) -> (A+2, 0, C, 0, 0) via R5 R1 R2 R1 R1
theorem tail_d1 : ∀ A C,
    ⟨A+1, 0, C+3, 1, 0⟩ [fm]⊢* ⟨A+2, 0, C, 0, 0⟩ := by
  intro A C
  -- R5: (A+1, 0, C+3, 1, 0) -> (A, 1, C+3, 1, 1)
  step fm
  -- R1: (A, 1, C+3, 1, 1) -> need b+1=1, c+1=C+3. So b=0, c=C+2.
  rw [show C + 3 = (C + 2) + 1 from by ring]
  step fm
  -- R2: (A, 0, C+2, 1, 1) -> (A+2, 2, C+2, 0, 0). d=1, e=1.
  rw [show (1 : ℕ) = 0 + 1 from by ring, show (1 : ℕ) = 0 + 1 from by ring]
  step fm
  -- R1: (A+2, 2, C+2, 0, 0) -> b+1=2, c+1=C+2. b=1, c=C+1.
  rw [show C + 2 = (C + 1) + 1 from by ring]
  step fm
  -- R1: (A+2, 1, C+1, 0, 0) -> b+1=1, c+1=C+1. b=0, c=C.
  rw [show C + 1 = C + 1 from rfl]
  step fm
  ring_nf; finish

-- Even e transition: (a+1, 0, 0, 0, 2m+2) ⊢⁺ (a+m+5, 0, 0, 0, 3m+2)
theorem trans_even (a m : ℕ) :
    ⟨a+1, 0, 0, 0, 2*m+2⟩ [fm]⊢⁺ ⟨a+m+5, 0, 0, 0, 3*m+2⟩ := by
  -- R5: (a+1, 0, 0, 0, 2m+2) -> (a, 1, 0, 0, 2m+3)
  apply step_stepStar_stepPlus
  · show fm ⟨a + 1, 0, 0, 0, 2 * m + 2⟩ = some ⟨a, 1, 0, 0, 2 * m + 3⟩; simp [fm]
  -- Chain m+1 rounds of R3-R2-R2: (a, 1, 0, 0, 2m+3) -> (a+4(m+1), 1+3(m+1), 0, 0, 2m+3-2(m+1))
  -- = (a+4m+4, 3m+4, 0, 0, 1)
  -- Using r3r2r2_chain with k=m+1, A=a, B=0, E=1:
  -- (a, 0+1, 0, 0, 1+2*(m+1)) = (a, 1, 0, 0, 2m+3) ✓
  -- -> (a+4*(m+1), 0+1+3*(m+1), 0, 0, 1) = (a+4m+4, 3m+4, 0, 0, 1) ✓
  apply stepStar_trans (c₂ := ⟨a+4*m+4, 3*m+4, 0, 0, 1⟩)
  · rw [show 2 * m + 3 = 1 + 2 * (m + 1) from by ring,
        show a + 4 * m + 4 = a + 4 * (m + 1) from by ring,
        show 3 * m + 4 = 0 + 1 + 3 * (m + 1) from by ring,
        show (1 : ℕ) = 0 + 1 from by ring]
    exact r3r2r2_chain (m+1) a 0 1
  -- R3: (a+4m+4, 3m+4, 0, 0, 1) -> (a+4m+4, 3m+3, 0, 2, 1)
  have h1 : ⟨a+4*m+4, 3*m+4, 0, 0, 1⟩ [fm]⊢ ⟨a+4*m+4, 3*m+3, 0, 2, 1⟩ := by
    show fm ⟨a + 4 * m + 4, 3 * m + 4, 0, 0, 1⟩ = _
    rw [show 3 * m + 4 = (3 * m + 3) + 1 from by ring]; simp [fm]
  -- R2: (a+4m+4, 3m+3, 0, 2, 1) -> (a+4m+6, 3m+5, 0, 1, 0)
  have h2 : ⟨a+4*m+4, 3*m+3, 0, 2, 1⟩ [fm]⊢ ⟨a+4*m+6, 3*m+5, 0, 1, 0⟩ := by
    simp [fm]
  apply stepStar_trans (step_stepStar h1)
  apply stepStar_trans (step_stepStar h2)
  -- R3 drain b=3m+5 with e=0: (a+4m+6, 3m+5, 0, 1, 0) -> (a+4m+6, 0, 0, 1+2*(3m+5), 0)
  apply stepStar_trans (c₂ := ⟨a+4*m+6, 0, 0, 1+2*(3*m+5), 0⟩)
  · exact r3_drain_e0 (3*m+5) (a+4*m+6) 1
  -- R4 drain (3m+5) rounds: (a+4m+6, 0, 0, 6m+11, 0) -> (a+4m+6, 0, 3m+5, 1, 0)
  apply stepStar_trans (c₂ := ⟨a+4*m+6, 0, 0+(3*m+5), 1, 0⟩)
  · exact r4_drain (3*m+5) (a+4*m+6) 0 1
  simp only [Nat.zero_add]
  -- Tail: (a+4m+6, 0, 3m+5, 1, 0) -> (a+4m+7, 0, 3m+2, 0, 0)
  apply stepStar_trans (c₂ := ⟨a+4*m+7, 0, 3*m+2, 0, 0⟩)
  · rw [show a + 4 * m + 6 = (a + 4 * m + 5) + 1 from by ring,
        show 3 * m + 5 = (3 * m + 2) + 3 from by ring,
        show a + 4 * m + 7 = (a + 4 * m + 5) + 2 from by ring]
    exact tail_d1 (a+4*m+5) (3*m+2)
  -- R5-R1 drain: (a+4m+7, 0, 3m+2, 0, 0) -> (a+m+5, 0, 0, 0, 3m+2)
  rw [show a + 4 * m + 7 = (a + m + 5) + (3 * m + 2) from by ring,
      show (3 * m + 2 : ℕ) = 3 * m + 2 from rfl]
  apply stepStar_trans (r5r1_drain (3*m+2) (a+m+5) 0)
  ring_nf; finish

-- Odd e transition: (a+1, 0, 0, 0, 2m+3) ⊢⁺ (a+m+1, 0, 0, 0, 3m+7)
theorem trans_odd (a m : ℕ) :
    ⟨a+1, 0, 0, 0, 2*m+3⟩ [fm]⊢⁺ ⟨a+m+1, 0, 0, 0, 3*m+7⟩ := by
  -- R5: (a+1, 0, 0, 0, 2m+3) -> (a, 1, 0, 0, 2m+4)
  apply step_stepStar_stepPlus
  · show fm ⟨a + 1, 0, 0, 0, 2 * m + 3⟩ = some ⟨a, 1, 0, 0, 2 * m + 4⟩; simp [fm]
  -- Chain m+2 rounds of R3-R2-R2: (a, 1, 0, 0, 2m+4) -> (a+4(m+2), 1+3(m+2), 0, 0, 0)
  -- = (a+4m+8, 3m+7, 0, 0, 0)
  apply stepStar_trans (c₂ := ⟨a+4*m+8, 3*m+7, 0, 0, 0⟩)
  · rw [show 2 * m + 4 = 0 + 2 * (m + 2) from by ring,
        show a + 4 * m + 8 = a + 4 * (m + 2) from by ring,
        show 3 * m + 7 = 0 + 1 + 3 * (m + 2) from by ring,
        show (1 : ℕ) = 0 + 1 from by ring]
    exact r3r2r2_chain (m+2) a 0 0
  -- R3 drain b=3m+7 with e=0: (a+4m+8, 3m+7, 0, 0, 0) -> (a+4m+8, 0, 0, 2*(3m+7), 0)
  apply stepStar_trans (c₂ := ⟨a+4*m+8, 0, 0, 0+2*(3*m+7), 0⟩)
  · exact r3_drain_e0 (3*m+7) (a+4*m+8) 0
  -- R4 drain (3m+7) rounds: -> (a+4m+8, 0, 3m+7, 0, 0)
  apply stepStar_trans (c₂ := ⟨a+4*m+8, 0, 0+(3*m+7), 0, 0⟩)
  · exact r4_drain (3*m+7) (a+4*m+8) 0 0
  simp only [Nat.zero_add]
  -- R5-R1 drain: (a+4m+8, 0, 3m+7, 0, 0) -> (a+m+1, 0, 0, 0, 3m+7)
  apply stepStar_trans (c₂ := ⟨a+m+1, 0, 0, 0, 0+(3*m+7)⟩)
  · rw [show a + 4 * m + 8 = (a + m + 1) + (3 * m + 7) from by ring]
    exact r5r1_drain (3*m+7) (a+m+1) 0
  simp only [Nat.zero_add]; finish

-- Main transition
theorem main_trans (a e : ℕ) (ha : a ≥ 1) (he : e ≥ 2) :
    ∃ a' e', a' ≥ 1 ∧ e' ≥ 2 ∧ ⟨a, 0, 0, 0, e⟩ [fm]⊢⁺ ⟨a', 0, 0, 0, e'⟩ := by
  rcases Nat.even_or_odd e with ⟨M, hM⟩ | ⟨M, hM⟩
  · obtain ⟨m, hm⟩ : ∃ m, M = m + 1 := ⟨M - 1, by omega⟩
    obtain ⟨A, hA⟩ : ∃ A, a = A + 1 := ⟨a - 1, by omega⟩
    subst hA; subst hm; rw [hM]
    rw [show (m + 1) + (m + 1) = 2 * m + 2 from by ring]
    exact ⟨A+m+5, 3*m+2, by omega, by omega, trans_even A m⟩
  · obtain ⟨m, hm⟩ : ∃ m, M = m + 1 := ⟨M - 1, by omega⟩
    obtain ⟨A, hA⟩ : ∃ A, a = A + 1 := ⟨a - 1, by omega⟩
    subst hA; subst hm; rw [hM]
    rw [show 2 * (m + 1) + 1 = 2 * m + 3 from by ring]
    exact ⟨A+m+1, 3*m+7, by omega, by omega, trans_odd A m⟩

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨1, 0, 0, 0, 4⟩) (by execute fm 35)
  apply progress_nonhalt (fm := fm)
    (P := fun q ↦ ∃ a e, q = ⟨a, 0, 0, 0, e⟩ ∧ a ≥ 1 ∧ e ≥ 2)
  · intro c ⟨a, e, hq, ha, he⟩; subst hq
    obtain ⟨a', e', ha', he', htrans⟩ := main_trans a e ha he
    exact ⟨⟨a', 0, 0, 0, e'⟩, ⟨a', e', rfl, ha', he'⟩, htrans⟩
  · exact ⟨1, 4, rfl, by omega, by omega⟩

end Sz22_2003_unofficial_38
