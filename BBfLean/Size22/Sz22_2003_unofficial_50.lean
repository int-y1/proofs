import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #50: [1/15, 7/3, 54/77, 5/49, 363/2]

Vector representation:
```
 0 -1 -1  0  0
 0 -1  0  1  0
 1  3  0 -1 -1
 0  0  1 -2  0
-1  1  0  0  2
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_50

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a, b+1, c+1, d, e⟩ => some ⟨a, b, c, d, e⟩
  | ⟨a, b+1, c, d, e⟩ => some ⟨a, b, c, d+1, e⟩
  | ⟨a, b, c, d+1, e+1⟩ => some ⟨a+1, b+3, c, d, e⟩
  | ⟨a, b, c, d+2, e⟩ => some ⟨a, b, c+1, d, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b+1, c, d, e+2⟩
  | _ => none

-- Rising chain: k rounds of R3+R2x3, starting with d >= 1 and running until e = 0.
-- Each round: (A, 0, 0, d, e) -> (A+1, 0, 0, d+2, e-1), needs d >= 1, e >= 1.
-- We parameterize with d growing as d₀+2*i and e shrinking from k to 0.
theorem rising_chain : ∀ k, ∀ A d₀,
    (⟨A, 0, 0, d₀+1, k⟩ : Q) [fm]⊢* ⟨A+k, 0, 0, d₀+2*k+1, 0⟩ := by
  intro k; induction' k with k ih <;> intro A d₀
  · simp; exists 0
  -- Goal: (A, 0, 0, d₀+1, k+1) ⊢* (A+k+1, 0, 0, d₀+2*(k+1)+1, 0)
  -- One round: R3+R2x3 takes us to (A+1, 0, 0, d₀+3, k)
  -- R3 needs d >= 1, e >= 1: d₀+1 >= 1 ✓, k+1 >= 1 ✓
  step fm; step fm; step fm; step fm
  -- Now at (A+1, 0, 0, d₀+3, k) = (A+1, 0, 0, (d₀+2)+1, k)
  apply stepStar_trans (ih (A+1) (d₀+2))
  ring_nf; finish

-- R4 drain: k applications of R4. Each: d -= 2, c += 1.
theorem r4_drain : ∀ k, ∀ A c d,
    (⟨A, 0, c, d+2*k, 0⟩ : Q) [fm]⊢* ⟨A, 0, c+k, d, 0⟩ := by
  intro k; induction' k with k ih <;> intro A c d
  · simp; exists 0
  rw [show d + 2 * (k + 1) = (d + 2 * k) + 2 from by ring]
  step fm
  apply stepStar_trans (ih A (c+1) d)
  ring_nf; finish

-- Phase 4a: R5+R1+R3+R1x3 (6 steps).
-- (A+1, 0, C+4, 1, 0) -> (A+1, 0, C, 0, 1)
theorem phase4a (A C : ℕ) :
    (⟨A+1, 0, C+4, 1, 0⟩ : Q) [fm]⊢* ⟨A+1, 0, C, 0, 1⟩ := by
  step fm; step fm; step fm; step fm; step fm; step fm; finish

-- R5+R1 chain: k rounds. Each: a -= 1, c -= 1, e += 2.
theorem r5r1_chain : ∀ k, ∀ A E,
    (⟨A+k, 0, k, 0, E⟩ : Q) [fm]⊢* ⟨A, 0, 0, 0, E+2*k⟩ := by
  intro k; induction' k with k ih <;> intro A E
  · simp; exists 0
  rw [show A + (k + 1) = (A + k) + 1 from by ring]
  step fm; step fm
  apply stepStar_trans (ih A (E+2))
  ring_nf; finish

-- Main transition: (a+1, 0, 0, 0, e+2) ⊢⁺ (a+4, 0, 0, 0, 2*e+1)
theorem main_trans (a e : ℕ) :
    (⟨a+1, 0, 0, 0, e+2⟩ : Q) [fm]⊢⁺ ⟨a+4, 0, 0, 0, 2*e+1⟩ := by
  -- Phase 1: R5 + R2: -> (a, 0, 0, 1, e+4)
  step fm; step fm
  -- Now at: (a, 0, 0, 1, e+4) = (a, 0, 0, 0+1, e+4)
  -- Phase 2: Rising chain with k = e+4 rounds, d₀ = 0
  -- (a, 0, 0, 0+1, e+4) -> (a+(e+4), 0, 0, 0+2*(e+4)+1, 0) = (a+e+4, 0, 0, 2*e+9, 0)
  apply stepStar_trans (rising_chain (e+4) a 0)
  -- Now Lean sees: (a+(e+4), 0, 0, 0+2*(e+4)+1, 0). Normalize to use r4_drain.
  rw [show 0 + 2 * (e + 4) + 1 = 1 + 2 * (e + 4) from by ring]
  -- Phase 3: R4 drain (e+4 times)
  apply stepStar_trans (r4_drain (e+4) (a+(e+4)) 0 1)
  -- Phase 4a: (a+e+4, 0, e+4, 1, 0) -> (a+e+4, 0, e, 0, 1)
  -- Need e+4 = e+4 in C+4 form: C = e. So A+1 = a+(e+4), A = a+e+3.
  -- But Lean sees 0+(e+4) for c and 1 for d. Let me normalize c.
  rw [show (0 : ℕ) + (e + 4) = e + 4 from by ring,
      show a + (e + 4) = (a + e + 3) + 1 from by ring]
  apply stepStar_trans (phase4a (a+e+3) e)
  -- Phase 4b: (a+e+3+1, 0, e, 0, 1) -> (a+4, 0, 0, 0, 2*e+1)
  -- r5r1_chain e (a+4) 1: ((a+4)+e, 0, e, 0, 1) -> (a+4, 0, 0, 0, 1+2*e)
  rw [show a + e + 3 + 1 = (a + 4) + e from by ring]
  apply stepStar_trans (r5r1_chain e (a+4) 1)
  ring_nf; finish

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨1, 0, 0, 0, 4⟩) (by execute fm 28)
  apply progress_nonhalt (fm := fm)
    (P := fun q ↦ ∃ a e, q = ⟨a, 0, 0, 0, e⟩ ∧ a ≥ 1 ∧ e ≥ 4)
  · intro c ⟨a, e, hq, ha, he⟩
    subst hq
    obtain ⟨a', rfl⟩ := Nat.exists_eq_add_of_le ha
    obtain ⟨e', rfl⟩ := Nat.exists_eq_add_of_le he
    refine ⟨⟨a' + 4, 0, 0, 0, 2 * e' + 5⟩,
            ⟨a' + 4, 2 * e' + 5, rfl, by omega, by omega⟩, ?_⟩
    rw [show 1 + a' = a' + 1 from by ring,
        show 4 + e' = (e' + 2) + 2 from by ring]
    exact main_trans a' (e' + 2)
  · exact ⟨1, 4, rfl, by omega, by omega⟩

end Sz22_2003_unofficial_50
