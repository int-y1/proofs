import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #1508: [7/15, 9/77, 50/7, 11/5, 147/2]

Vector representation:
```
 0 -1 -1  1  0
 0  2  0 -1 -1
 1  0  2 -1  0
 0  0 -1  0  1
-1  1  0  2  0
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_1508

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a, b+1, c+1, d, e⟩ => some ⟨a, b, c, d+1, e⟩
  | ⟨a, b, c, d+1, e+1⟩ => some ⟨a, b+2, c, d, e⟩
  | ⟨a, b, c, d+1, e⟩ => some ⟨a+1, b, c+2, d, e⟩
  | ⟨a, b, c+1, d, e⟩ => some ⟨a, b, c, d, e+1⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b+1, c, d+2, e⟩
  | _ => none

-- R4 chain: transfer c to e (b=0, d=0).
theorem c_to_e : ∀ k, ∀ a c e, ⟨a, (0 : ℕ), c + k, (0 : ℕ), e⟩ [fm]⊢* ⟨a, 0, c, 0, e + k⟩ := by
  intro k; induction' k with k ih <;> intro a c e
  · exists 0
  · rw [show c + (k + 1) = (c + k) + 1 from by ring]
    step fm
    apply stepStar_trans (ih a c (e + 1))
    rw [show e + 1 + k = e + (k + 1) from by ring]; exists 0

-- R5R2R2 chain: each round drains a by 1 and e by 2, building b by 5.
theorem r5r2r2_chain : ∀ k, ∀ a b e, ⟨a + k, b, (0 : ℕ), (0 : ℕ), e + 2 * k⟩ [fm]⊢*
    ⟨a, b + 5 * k, 0, 0, e⟩ := by
  intro k; induction' k with k ih <;> intro a b e
  · simp; exists 0
  · rw [show a + (k + 1) = (a + k) + 1 from by ring,
        show e + 2 * (k + 1) = (e + 2 * k) + 2 from by ring]
    step fm; step fm; step fm
    apply stepStar_trans (ih a (b + 5) e)
    rw [show b + 5 + 5 * k = b + 5 * (k + 1) from by ring]; exists 0

-- R3 drain: b=0, e=0, drain d building c.
theorem r3_drain : ∀ k, ∀ a c d, ⟨a, (0 : ℕ), c, d + k, (0 : ℕ)⟩ [fm]⊢*
    ⟨a + k, 0, c + 2 * k, d, 0⟩ := by
  intro k; induction' k with k ih <;> intro a c d
  · simp; exists 0
  · rw [show d + (k + 1) = (d + k) + 1 from by ring]
    step fm
    apply stepStar_trans (ih (a + 1) (c + 2) d)
    rw [show a + 1 + k = a + (k + 1) from by ring,
        show c + 2 + 2 * k = c + 2 * (k + 1) from by ring]; exists 0

-- Full drain: R3R1R1 chain then R3 drain from (a, B, 0, d+1, 0).
-- Uses strong induction on B.
theorem full_drain : ∀ B, ∀ a d, ⟨a, B, (0 : ℕ), d + 1, (0 : ℕ)⟩ [fm]⊢*
    ⟨a + B + d + 1, 0, B + 2 * d + 2, 0, 0⟩ := by
  intro B; induction' B using Nat.strongRecOn with B ih; intro a d
  rcases B with _ | _ | B
  · -- B=0: R3 drain (d+1) steps.
    rw [show d + 1 = 0 + (d + 1) from by ring]
    apply stepStar_trans (r3_drain (d + 1) a 0 0)
    rw [show a + (d + 1) = a + 0 + d + 1 from by ring,
        show 0 + 2 * (d + 1) = 0 + 2 * d + 2 from by ring]; exists 0
  · -- B=1: R3, R1, then R3 drain (d+1) steps with c=1.
    step fm; step fm
    rw [show d + 1 = 0 + (d + 1) from by ring]
    apply stepStar_trans (r3_drain (d + 1) (a + 1) 1 0)
    rw [show a + 1 + (d + 1) = a + 1 + d + 1 from by ring,
        show 1 + 2 * (d + 1) = 1 + 2 * d + 2 from by ring]; exists 0
  · -- B+2 ≥ 2: R3, R1, R1, then recurse with B, d+1.
    step fm; step fm; step fm
    rw [show (d + 1 : ℕ) + 1 = (d + 1) + 1 from by ring]
    apply stepStar_trans (ih B (by omega) (a + 1) (d + 1))
    rw [show a + 1 + B + (d + 1) + 1 = a + (B + 2) + d + 1 from by ring,
        show B + 2 * (d + 1) + 2 = B + 2 + 2 * d + 2 from by ring]; exists 0

-- Transition for odd c = 2m+1: requires a ≥ m+1.
-- (a, 0, 2m+1, 0, 0) ⊢⁺ (a+4m+3, 0, 5m+5, 0, 0).
theorem trans_odd (F m : ℕ) :
    ⟨F + m + 1, (0 : ℕ), 2 * m + 1, (0 : ℕ), (0 : ℕ)⟩ [fm]⊢⁺
    ⟨F + 5 * m + 4, 0, 5 * m + 5, 0, 0⟩ := by
  -- Phase 1: R4 drain.
  rw [show 2 * m + 1 = 0 + (2 * m + 1) from by ring]
  apply stepStar_stepPlus_stepPlus (c_to_e (2 * m + 1) (F + m + 1) 0 0)
  show ⟨F + m + 1, 0, 0, 0, 0 + (2 * m + 1)⟩ [fm]⊢⁺ _
  rw [show (0 : ℕ) + (2 * m + 1) = 1 + 2 * m from by ring,
      show F + m + 1 = (F + 1) + m from by ring]
  -- Phase 2: R5R2R2 chain for m rounds.
  apply stepStar_stepPlus_stepPlus (r5r2r2_chain m (F + 1) 0 1)
  show ⟨F + 1, 0 + 5 * m, 0, 0, 1⟩ [fm]⊢⁺ _
  rw [show (0 : ℕ) + 5 * m = 5 * m from by ring]
  -- Phase 3: R5 (use simp [fm] since 5*m is opaque).
  apply step_stepStar_stepPlus
    (show (⟨F + 1, 5 * m, 0, 0, 1⟩ : Q) [fm]⊢ ⟨F, 5 * m + 1, 0, 2, 1⟩ from by simp [fm])
  -- R2, R3, R1, R1.
  step fm; step fm; step fm; step fm
  -- Now at (F+1, 5*m+1, 0, 2, 0). Rewrite 2 = 1+1 for full_drain.
  rw [show (2 : ℕ) = 1 + 1 from rfl]
  apply stepStar_trans (full_drain (5 * m + 1) (F + 1) 1)
  rw [show F + 1 + (5 * m + 1) + 1 + 1 = F + 5 * m + 4 from by ring,
      show 5 * m + 1 + 2 * 1 + 2 = 5 * m + 5 from by ring]; finish

-- Transition for even c = 2*(m+1): requires a ≥ m+2.
-- (a, 0, 2m+2, 0, 0) ⊢⁺ (a+4m+6, 0, 5m+10, 0, 0).
theorem trans_even (F m : ℕ) :
    ⟨F + m + 2, (0 : ℕ), 2 * m + 2, (0 : ℕ), (0 : ℕ)⟩ [fm]⊢⁺
    ⟨F + 5 * m + 8, 0, 5 * m + 10, 0, 0⟩ := by
  -- Phase 1: R4 drain.
  rw [show 2 * m + 2 = 0 + (2 * m + 2) from by ring]
  apply stepStar_stepPlus_stepPlus (c_to_e (2 * m + 2) (F + m + 2) 0 0)
  show ⟨F + m + 2, 0, 0, 0, 0 + (2 * m + 2)⟩ [fm]⊢⁺ _
  rw [show (0 : ℕ) + (2 * m + 2) = 0 + 2 * (m + 1) from by ring,
      show F + m + 2 = (F + 1) + (m + 1) from by ring]
  -- Phase 2: R5R2R2 chain for m+1 rounds.
  apply stepStar_stepPlus_stepPlus (r5r2r2_chain (m + 1) (F + 1) 0 0)
  show ⟨F + 1, 0 + 5 * (m + 1), 0, 0, 0⟩ [fm]⊢⁺ _
  rw [show (0 : ℕ) + 5 * (m + 1) = 5 * m + 5 from by ring]
  -- Phase 3: R5, R3, R1, R1.
  step fm; step fm; step fm; step fm
  -- Now at (F+1, 5*m+4, 0, 3, 0). Rewrite 3 = 2+1 for full_drain.
  rw [show (3 : ℕ) = 2 + 1 from rfl]
  apply stepStar_trans (full_drain (5 * m + 4) (F + 1) 2)
  rw [show F + 1 + (5 * m + 4) + 2 + 1 = F + 5 * m + 8 from by ring,
      show 5 * m + 4 + 2 * 2 + 2 = 5 * m + 10 from by ring]; finish

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨3, 0, 5, 0, 0⟩) (by execute fm 5)
  apply progress_nonhalt (fm := fm)
    (P := fun q ↦ ∃ a c, q = ⟨a, 0, c, 0, 0⟩ ∧ 2 * a ≥ c + 1 ∧ c ≥ 5)
  · intro q ⟨a, c, hq, ha, hc⟩; subst hq
    rcases Nat.even_or_odd c with ⟨k, hk⟩ | ⟨k, hk⟩
    · -- c even: c = k+k, k ≥ 3.
      rw [show k + k = 2 * k from by ring] at hk; subst hk
      obtain ⟨m, rfl⟩ : ∃ m, k = m + 1 := ⟨k - 1, by omega⟩
      obtain ⟨F, rfl⟩ : ∃ F, a = F + m + 2 := ⟨a - m - 2, by omega⟩
      exact ⟨⟨F + 5 * m + 8, 0, 5 * m + 10, 0, 0⟩,
        ⟨F + 5 * m + 8, 5 * m + 10, rfl, by omega, by omega⟩,
        trans_even F m⟩
    · -- c odd: c = 2k+1, k ≥ 2.
      subst hk
      obtain ⟨F, rfl⟩ : ∃ F, a = F + k + 1 := ⟨a - k - 1, by omega⟩
      exact ⟨⟨F + 5 * k + 4, 0, 5 * k + 5, 0, 0⟩,
        ⟨F + 5 * k + 4, 5 * k + 5, rfl, by omega, by omega⟩,
        trans_odd F k⟩
  · exact ⟨3, 5, rfl, by omega, by omega⟩

end Sz22_2003_unofficial_1508
