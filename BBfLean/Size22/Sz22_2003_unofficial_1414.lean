import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #1414: [7/15, 121/3, 18/77, 125/2, 3/5]

Vector representation:
```
 0 -1 -1  1  0
 0 -1  0  0  2
 1  2  0 -1 -1
-1  0  3  0  0
 0  1 -1  0  0
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_1414

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a, b+1, c+1, d, e⟩ => some ⟨a, b, c, d+1, e⟩
  | ⟨a, b+1, c, d, e⟩ => some ⟨a, b, c, d, e+2⟩
  | ⟨a, b, c, d+1, e+1⟩ => some ⟨a+1, b+2, c, d, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b, c+3, d, e⟩
  | ⟨a, b, c+1, d, e⟩ => some ⟨a, b+1, c, d, e⟩
  | _ => none

-- R3/R1/R1 chain: each round consumes 2 from c and 1 from e, adds 1 to a and d.
theorem r3r1r1_chain : ∀ k a c d e,
    ⟨a, 0, c + 2 * k, d + 1, e + k⟩ [fm]⊢* ⟨a + k, 0, c, d + 1 + k, e⟩ := by
  intro k; induction' k with k ih <;> intro a c d e
  · exists 0
  · rw [show c + 2 * (k + 1) = (c + 2 * k + 1) + 1 from by ring,
        show e + (k + 1) = (e + k) + 1 from by ring]
    step fm; step fm; step fm
    rw [show d + 2 = (d + 1) + 1 from by ring]
    apply stepStar_trans (ih (a + 1) c (d + 1) e)
    ring_nf; finish

-- R3/R2/R2 chain: each round drains 1 from d, adds 3 to e.
theorem r3r2r2_chain : ∀ k a d e,
    ⟨a, 0, 0, d + k, e + 1⟩ [fm]⊢* ⟨a + k, 0, 0, d, e + 1 + 3 * k⟩ := by
  intro k; induction' k with k ih <;> intro a d e
  · exists 0
  · rw [show d + (k + 1) = (d + k) + 1 from by ring]
    step fm; step fm; step fm
    rw [show e + 4 = (e + 3) + 1 from by ring]
    apply stepStar_trans (ih (a + 1) d (e + 3))
    ring_nf; finish

-- R4 chain: drain a, producing c.
theorem r4_chain : ∀ k a c e,
    ⟨a + k, 0, c, 0, e⟩ [fm]⊢* ⟨a, 0, c + 3 * k, 0, e⟩ := by
  intro k; induction' k with k ih <;> intro a c e
  · exists 0
  · rw [show a + (k + 1) = (a + k) + 1 from by ring]
    step fm
    apply stepStar_trans (ih a (c + 3) e)
    ring_nf; finish

-- Even case: C = 2m+2.
-- (0, 0, 2m+2, 0, e+m+1) ⊢⁺ (0, 0, 6m+3, 0, e+3m+4)
theorem main_even (m e : ℕ) :
    ⟨0, 0, 2 * m + 2, 0, e + m + 1⟩ [fm]⊢⁺ ⟨0, 0, 6 * m + 3, 0, e + 3 * m + 4⟩ := by
  rw [show 2 * m + 2 = (2 * m + 1) + 1 from by ring]
  step fm; step fm
  rw [show (2 * m : ℕ) = 0 + 2 * m from by ring,
      show (1 : ℕ) = 0 + 1 from by ring,
      show e + m + 1 = (e + 1) + m from by ring]
  apply stepStar_trans (r3r1r1_chain m 0 0 0 (e + 1))
  rw [show 0 + m = m from by ring,
      show 0 + 1 + m = m + 1 from by ring]
  rw [show (m + 1 : ℕ) = 0 + (m + 1) from by ring]
  apply stepStar_trans (r3r2r2_chain (m + 1) m 0 e)
  rw [show m + (m + 1) = 0 + (2 * m + 1) from by ring]
  apply stepStar_trans (r4_chain (2 * m + 1) 0 0 (e + 1 + 3 * (m + 1)))
  ring_nf; finish

-- Odd case: C = 2m+3.
-- (0, 0, 2m+3, 0, e+m+1) ⊢⁺ (0, 0, 6m+6, 0, e+3m+5)
theorem main_odd (m e : ℕ) :
    ⟨0, 0, 2 * m + 3, 0, e + m + 1⟩ [fm]⊢⁺ ⟨0, 0, 6 * m + 6, 0, e + 3 * m + 5⟩ := by
  rw [show 2 * m + 3 = (2 * m + 2) + 1 from by ring]
  step fm
  rw [show (2 * m + 2 : ℕ) = (2 * m + 1) + 1 from by ring]
  step fm
  rw [show (2 * m + 1 : ℕ) = 1 + 2 * m from by ring,
      show (1 : ℕ) = 0 + 1 from by ring,
      show e + m + 1 = (e + 1) + m from by ring]
  apply stepStar_trans (r3r1r1_chain m 0 1 0 (e + 1))
  rw [show 0 + m = m from by ring,
      show 0 + 1 + m = m + 1 from by ring]
  -- State: (m, 0, 1, m+1, e+1). R3 fires (d=m+1>=1, e=e+1>=1, takes priority over R5).
  rw [show (1 : ℕ) = 0 + 1 from by ring]
  step fm; step fm; step fm
  -- State: (m+1, 0, 0, m+1, e+2)
  -- Phase 3: (m+1) rounds R3/R2/R2
  have h3 := r3r2r2_chain (m + 1) (m + 1) 0 (e + 1)
  rw [show 0 + (m + 1) = m + 1 from by ring,
      show e + 1 + 1 = e + 2 from by ring] at h3
  apply stepStar_trans h3
  -- Phase 4: R4 chain
  rw [show m + 1 + (m + 1) = 0 + (2 * m + 2) from by ring]
  apply stepStar_trans (r4_chain (2 * m + 2) 0 0 (e + 1 + 1 + 3 * (m + 1)))
  ring_nf; finish

-- Combined transition.
theorem main_trans (C E : ℕ) (hC : C ≥ 3) (hE : 2 * E ≥ C) :
    ⟨0, 0, C, 0, E⟩ [fm]⊢⁺ ⟨0, 0, 3 * C - 3, 0, E + C + 1⟩ := by
  rcases Nat.even_or_odd C with ⟨m, hm⟩ | ⟨m, hm⟩
  · rw [show m + m = 2 * m from by ring] at hm; subst hm
    have hm1 : m ≥ 1 := by omega
    obtain ⟨m', rfl⟩ : ∃ k, m = k + 1 := ⟨m - 1, by omega⟩
    have hE' : E ≥ m' + 1 := by omega
    obtain ⟨e', rfl⟩ : ∃ k, E = k + (m' + 1) := ⟨E - (m' + 1), by omega⟩
    rw [show 2 * (m' + 1) = 2 * m' + 2 from by ring,
        show e' + (m' + 1) = e' + m' + 1 from by ring,
        show 3 * (2 * m' + 2) - 3 = 6 * m' + 3 from by omega,
        show e' + m' + 1 + (2 * m' + 2) + 1 = e' + 3 * m' + 4 from by ring]
    exact main_even m' e'
  · subst hm
    have hm1 : m ≥ 1 := by omega
    obtain ⟨m', rfl⟩ : ∃ k, m = k + 1 := ⟨m - 1, by omega⟩
    have hE' : E ≥ m' + 1 := by omega
    obtain ⟨e', rfl⟩ : ∃ k, E = k + (m' + 1) := ⟨E - (m' + 1), by omega⟩
    rw [show 2 * (m' + 1) + 1 = 2 * m' + 3 from by ring,
        show e' + (m' + 1) = e' + m' + 1 from by ring,
        show 3 * (2 * m' + 3) - 3 = 6 * m' + 6 from by omega,
        show e' + m' + 1 + (2 * m' + 3) + 1 = e' + 3 * m' + 5 from by ring]
    exact main_odd m' e'

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨0, 0, 3, 0, 5⟩) (by execute fm 9)
  apply progress_nonhalt (fm := fm)
    (P := fun q ↦ ∃ C E, q = ⟨0, 0, C, 0, E⟩ ∧ C ≥ 3 ∧ 2 * E ≥ C)
  · intro q ⟨C, E, hq, hC, hE⟩
    subst hq
    exact ⟨⟨0, 0, 3 * C - 3, 0, E + C + 1⟩,
      ⟨3 * C - 3, E + C + 1, rfl, by omega, by omega⟩,
      main_trans C E hC hE⟩
  · exact ⟨3, 5, rfl, by omega, by omega⟩

end Sz22_2003_unofficial_1414
