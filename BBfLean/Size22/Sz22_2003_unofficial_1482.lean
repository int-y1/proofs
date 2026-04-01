import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #1482: [7/15, 484/3, 18/77, 5/2, 3/5]

Vector representation:
```
 0 -1 -1  1  0
 2 -1  0  0  2
 1  2  0 -1 -1
-1  0  1  0  0
 0  1 -1  0  0
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_1482

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a, b+1, c+1, d, e⟩ => some ⟨a, b, c, d+1, e⟩
  | ⟨a, b+1, c, d, e⟩ => some ⟨a+2, b, c, d, e+2⟩
  | ⟨a, b, c, d+1, e+1⟩ => some ⟨a+1, b+2, c, d, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b, c+1, d, e⟩
  | ⟨a, b, c+1, d, e⟩ => some ⟨a, b+1, c, d, e⟩
  | _ => none

-- R4 drain: (j, 0, c, 0, e) ⊢* (0, 0, c+j, 0, e).
theorem r4_drain : ∀ j, ∀ c e, ⟨j, 0, c, 0, e⟩ [fm]⊢* ⟨0, 0, c + j, 0, e⟩ := by
  intro j; induction' j with j ih
  · intro c e; exists 0
  · intro c e; step fm
    apply stepStar_trans (ih (c + 1) e); ring_nf; finish

-- R3R1R1 chain: each round uses R3, R1, R1.
-- Processes 2 units of c per round.
theorem r3r1r1_chain : ∀ k, ∀ A C D E,
    ⟨A, 0, C + 2 * k, D + 1, E + k⟩ [fm]⊢* ⟨A + k, 0, C, D + k + 1, E⟩ := by
  intro k; induction' k with k ih
  · intro A C D E; exists 0
  · intro A C D E
    rw [show C + 2 * (k + 1) = (C + 2 * k) + 1 + 1 from by ring,
        show E + (k + 1) = (E + k) + 1 from by ring]
    step fm; step fm; step fm
    apply stepStar_trans (ih (A + 1) C (D + 1) E); ring_nf; finish

-- R3R2R2 chain: each round uses R3, R2, R2.
-- Drains d, adding 5 to a and 3 to e per round.
theorem r3r2r2_chain : ∀ k, ∀ A e,
    ⟨A, 0, 0, k + 1, e + 1⟩ [fm]⊢* ⟨A + 5 * (k + 1), 0, 0, 0, e + 3 * k + 4⟩ := by
  intro k; induction' k with k ih
  · intro A e; step fm; step fm; step fm; ring_nf; finish
  · intro A e
    step fm; step fm; step fm
    rw [show e + 2 + 2 = (e + 3) + 1 from by ring]
    apply stepStar_trans (ih (A + 1 + 2 + 2) (e + 3)); ring_nf; finish

-- Even transition: a = 2m+2 (even, ≥ 2), e = m+F+1 (so 2e ≥ a).
-- (2m+2, 0, 0, 0, m+F+1) ⊢⁺ (6m+5, 0, 0, 0, 3m+F+4).
theorem main_even (m F : ℕ) :
    ⟨2 * m + 2, 0, 0, 0, m + F + 1⟩ [fm]⊢⁺ ⟨6 * m + 5, 0, 0, 0, 3 * m + F + 4⟩ := by
  -- R4 first step (⊢⁺)
  rw [show (2 * m + 2 : ℕ) = (2 * m + 1) + 1 from by ring]
  step fm
  -- R4 drain remaining 2m+1 steps
  apply stepStar_trans (r4_drain (2 * m + 1) 1 (m + F + 1))
  -- Now at (0, 0, 2m+2, 0, m+F+1). R5+R1 setup.
  rw [show 1 + (2 * m + 1) = (0 + 2 * m) + 1 + 1 from by ring]
  step fm; step fm
  -- Now at (0, 0, 2m, 1, m+F+1).
  -- R3R1R1 chain: m rounds.
  -- Need form (A, 0, C+2k, D+1, E+k) with k=m, A=0, C=0, D=0, E=F+1.
  rw [show m + F + 1 = (F + 1) + m from by ring]
  apply stepStar_trans (r3r1r1_chain m 0 0 0 (F + 1))
  rw [show 0 + m + 1 = m + 1 from by ring,
      show (0 + m : ℕ) = m from by ring]
  apply stepStar_trans (r3r2r2_chain m m F)
  ring_nf; finish

-- Odd transition: a = 2M+3 (odd, ≥ 3), e = M+G+2 (so 2e ≥ a).
-- (2M+3, 0, 0, 0, M+G+2) ⊢⁺ (6M+8, 0, 0, 0, 3M+G+6).
theorem main_odd (M G : ℕ) :
    ⟨2 * M + 3, 0, 0, 0, M + G + 2⟩ [fm]⊢⁺ ⟨6 * M + 8, 0, 0, 0, 3 * M + G + 6⟩ := by
  -- R4 first step (⊢⁺)
  rw [show (2 * M + 3 : ℕ) = (2 * M + 2) + 1 from by ring]
  step fm
  -- R4 drain remaining 2M+2 steps
  apply stepStar_trans (r4_drain (2 * M + 2) 1 (M + G + 2))
  -- Now at (0, 0, 2M+3, 0, M+G+2). R5+R1 setup.
  rw [show 1 + (2 * M + 2) = (1 + 2 * M) + 1 + 1 from by ring]
  step fm; step fm
  -- Now at (0, 0, 2M+1, 1, M+G+2).
  -- R3R1R1 chain: M rounds. C=1, k=M.
  -- Need form (A, 0, C+2k, D+1, E+k) with k=M, A=0, C=1, D=0, E=G+2.
  rw [show M + G + 2 = (G + 2) + M from by ring]
  apply stepStar_trans (r3r1r1_chain M 0 1 0 (G + 2))
  rw [show (G + 2 : ℕ) = (G + 1) + 1 from by ring]
  -- R3R1R2 step: R3, R1, R2.
  step fm; step fm; step fm
  -- Now at (0+M+1+2, 0, 0, 0+M+1, G+1+2).
  rw [show 0 + M + 1 + 2 = M + 3 from by ring,
      show (0 + M + 1 : ℕ) = M + 1 from by ring,
      show G + 1 + 2 = (G + 2) + 1 from by ring]
  -- R3R2R2 chain: M+1 rounds.
  apply stepStar_trans (r3r2r2_chain M (M + 3) (G + 2))
  ring_nf; finish

-- Two-step transition: even -> odd -> even.
theorem main_trans (m F : ℕ) :
    ⟨2 * m + 2, 0, 0, 0, m + F + 1⟩ [fm]⊢⁺ ⟨18 * m + 14, 0, 0, 0, 9 * m + F + 10⟩ := by
  apply stepPlus_stepStar_stepPlus (main_even m F)
  -- Need (6m+5, 0, 0, 0, 3m+F+4) ⊢* (18m+14, 0, 0, 0, 9m+F+10)
  -- Odd step: 6m+5 = 2(3m+1)+3, M=3m+1, G=F+1.
  -- (2(3m+1)+3, 0, 0, 0, (3m+1)+(F+1)+2) = (6m+5, 0, 0, 0, 3m+F+4) ✓
  -- Result: (6(3m+1)+8, 0, 0, 0, 3(3m+1)+(F+1)+6) = (18m+14, 0, 0, 0, 9m+F+10) ✓
  have h := main_odd (3 * m + 1) (F + 1)
  rw [show 2 * (3 * m + 1) + 3 = 6 * m + 5 from by ring,
      show (3 * m + 1) + (F + 1) + 2 = 3 * m + F + 4 from by ring,
      show 6 * (3 * m + 1) + 8 = 18 * m + 14 from by ring,
      show 3 * (3 * m + 1) + (F + 1) + 6 = 9 * m + F + 10 from by ring] at h
  exact stepPlus_stepStar h

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨2, 0, 0, 0, 2⟩) (by execute fm 3)
  apply progress_nonhalt_simple (fm := fm) (A := ℕ × ℕ)
    (fun ⟨m, F⟩ ↦ ⟨2 * m + 2, 0, 0, 0, m + F + 1⟩) ⟨0, 1⟩
  intro ⟨m, F⟩
  exact ⟨⟨9 * m + 6, F + 3⟩, by
    show (2 * m + 2, 0, 0, 0, m + F + 1) [fm]⊢⁺ (2 * (9 * m + 6) + 2, 0, 0, 0, (9 * m + 6) + (F + 3) + 1)
    rw [show 2 * (9 * m + 6) + 2 = 18 * m + 14 from by ring,
        show (9 * m + 6) + (F + 3) + 1 = 9 * m + F + 10 from by ring]
    exact main_trans m F⟩

end Sz22_2003_unofficial_1482
