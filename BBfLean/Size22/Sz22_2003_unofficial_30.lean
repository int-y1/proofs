import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #30: [1/15, 27/77, 98/3, 5/49, 33/2]

Vector representation:
```
 0 -1 -1  0  0
 0  3  0 -1 -1
 1 -1  0  2  0
 0  0  1 -2  0
-1  1  0  0  1
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_30

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a, b+1, c+1, d, e⟩ => some ⟨a, b, c, d, e⟩
  | ⟨a, b, c, d+1, e+1⟩ => some ⟨a, b+3, c, d, e⟩
  | ⟨a, b+1, c, d, e⟩ => some ⟨a+1, b, c, d+2, e⟩
  | ⟨a, b, c, d+2, e⟩ => some ⟨a, b, c+1, d, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b+1, c, d, e+1⟩
  | _ => none

-- R4 repeated: d to c
theorem d_to_c : ∀ k c, ⟨a, 0, c, d + 2 * k, 0⟩ [fm]⊢* ⟨a, 0, c + k, d, 0⟩ := by
  intro k; induction' k with k h <;> intro c
  · exists 0
  rw [Nat.mul_succ, ← Nat.add_assoc]
  step fm
  apply stepStar_trans (h _)
  ring_nf; finish

-- R5+R1 repeated: a,c to e
theorem ac_to_ae : ∀ k a e, ⟨a + k, 0, k, 0, e⟩ [fm]⊢* ⟨a, 0, 0, 0, e + k⟩ := by
  intro k; induction' k with k h <;> intro a e
  · exists 0
  rw [← Nat.add_assoc]
  step fm; step fm
  apply stepStar_trans (h _ _)
  ring_nf; finish

-- R3 repeated: b to a,d
theorem r3_chain : ∀ k a d, ⟨a, b + k, 0, d, 0⟩ [fm]⊢* ⟨a + k, b, 0, d + 2 * k, 0⟩ := by
  intro k; induction' k with k h <;> intro a d
  · exists 0
  rw [show b + (k + 1) = (b + k) + 1 from by ring]
  step fm
  apply stepStar_trans (h _ _)
  ring_nf; finish

-- R2/R3 pump: (A, B, 0, 2, E) →* (A+B+3E, 0, 0, 2B+5E+2, 0)
theorem r2r3_phase : ∀ E, ∀ A B, ⟨A, B, 0, 2, E⟩ [fm]⊢* ⟨A + B + 3 * E, 0, 0, 2 * B + 5 * E + 2, 0⟩ := by
  intro E; induction' E using Nat.strongRecOn with E ih; intro A B
  rcases E with _ | _ | E'
  · have h := @r3_chain 0 B A 2; rw [Nat.zero_add] at h
    apply stepStar_trans h; ring_nf; finish
  · step fm; step fm
    have h := @r3_chain 0 (B + 2) (A + 1) 3; rw [Nat.zero_add] at h
    apply stepStar_trans h; ring_nf; finish
  · step fm; step fm; step fm
    apply stepStar_trans (ih E' (by omega) _ _)
    ring_nf; finish

-- Even transition: (a+1, 0, 0, 0, 2*(E+1)) →⁺ (a+E+5, 0, 0, 0, 5*E+4)
theorem even_trans : ∀ E, ∀ a,
    ⟨a + 1, 0, 0, 0, 2 * (E + 1)⟩ [fm]⊢⁺ ⟨a + E + 5, 0, 0, 0, 5 * E + 4⟩ := by
  intro E a
  -- R5, R3 (2 steps): (a+1, 0, 0, 0, 2E+2) -> (a+1, 0, 0, 2, 2E+3)
  rw [show 2 * (E + 1) = (2 * E + 1) + 1 from by ring]
  step fm; step fm
  -- r2r3_phase with E_phase = 2E+3: -> (a+1+3*(2E+3), 0, 0, 5*(2E+3)+2, 0) = (a+6E+10, 0, 0, 10E+17, 0)
  rw [show 2 * E + 1 + 1 + 1 = 2 * E + 3 from by ring]
  apply stepStar_trans (r2r3_phase (2 * E + 3) (a + 1) 0)
  rw [show a + 1 + 0 + 3 * (2 * E + 3) = a + 6 * E + 10 from by ring]
  rw [show 2 * 0 + 5 * (2 * E + 3) + 2 = 1 + 2 * (5 * E + 8) from by ring]
  -- R4 (5E+8 times): -> (a+6E+10, 0, 5E+8, 1, 0)
  apply stepStar_trans (d_to_c (5 * E + 8) 0)
  simp only [Nat.zero_add]
  -- R5, R1, R2, R1, R1, R1 (6 steps): (a+6E+10, 0, 5E+8, 1, 0) -> (a+6E+9, 0, 5E+4, 0, 0)
  step fm; step fm; step fm; step fm; step fm; step fm
  -- drain: ac_to_ae (5E+4 pairs of R5, R1)
  rw [show a + 6 * E + 9 = (a + E + 5) + (5 * E + 4) from by ring]
  apply stepStar_trans (ac_to_ae (5 * E + 4) _ _)
  ring_nf; finish

-- Odd transition: (a+1, 0, 0, 0, 2*E+1) →⁺ (a+E+1, 0, 0, 0, 5*E+6)
theorem odd_trans : ∀ E, ∀ a,
    ⟨a + 1, 0, 0, 0, 2 * E + 1⟩ [fm]⊢⁺ ⟨a + E + 1, 0, 0, 0, 5 * E + 6⟩ := by
  intro E a
  -- R5, R3 (2 steps): (a+1, 0, 0, 0, 2E+1) -> (a+1, 0, 0, 2, 2E+2)
  step fm; step fm
  -- r2r3_phase with E_phase = 2E+2: -> (a+1+3*(2E+2), 0, 0, 5*(2E+2)+2, 0) = (a+6E+7, 0, 0, 10E+12, 0)
  rw [show 2 * E + 1 + 1 = 2 * E + 2 from by ring]
  apply stepStar_trans (r2r3_phase (2 * E + 2) (a + 1) 0)
  rw [show a + 1 + 0 + 3 * (2 * E + 2) = a + 6 * E + 7 from by ring]
  rw [show 2 * 0 + 5 * (2 * E + 2) + 2 = 0 + 2 * (5 * E + 6) from by ring]
  -- R4 (5E+6 times): -> (a+6E+7, 0, 5E+6, 0, 0)
  apply stepStar_trans (d_to_c (5 * E + 6) 0)
  simp only [Nat.zero_add]
  -- drain: ac_to_ae (5E+6 pairs of R5, R1)
  rw [show a + 6 * E + 7 = (a + E + 1) + (5 * E + 6) from by ring]
  apply stepStar_trans (ac_to_ae (5 * E + 6) _ _)
  ring_nf; finish

theorem nonhalt : ¬halts fm c₀ := by
  -- c₀ = (1,0,0,0,0) reaches (3,0,0,0,1) in 18 steps
  apply stepStar_not_halts_not_halts (c₂ := ⟨3, 0, 0, 0, 1⟩) (by execute fm 18)
  -- Invariant: (a, 0, 0, 0, e) with a >= 1 and e >= 1
  apply progress_nonhalt (fm := fm)
    (P := fun q ↦ ∃ a e, q = ⟨a, 0, 0, 0, e⟩ ∧ a ≥ 1 ∧ e ≥ 1)
  · intro c ⟨A, E, hq, hA, hE⟩; subst hq
    obtain ⟨a, rfl⟩ : ∃ a, A = a + 1 := ⟨A - 1, by omega⟩
    rcases Nat.even_or_odd E with ⟨K, hK⟩ | ⟨K, hK⟩
    · -- E even: E = K + K = 2K
      rw [show K + K = 2 * K from by ring] at hK; subst hK
      obtain ⟨k, rfl⟩ : ∃ k, K = k + 1 := ⟨K - 1, by omega⟩
      refine ⟨⟨a + k + 5, 0, 0, 0, 5 * k + 4⟩,
        ⟨a + k + 5, 5 * k + 4, rfl, by omega, by omega⟩, ?_⟩
      exact even_trans k a
    · -- E odd: E = 2K+1
      subst hK
      refine ⟨⟨a + K + 1, 0, 0, 0, 5 * K + 6⟩,
        ⟨a + K + 1, 5 * K + 6, rfl, by omega, by omega⟩, ?_⟩
      exact odd_trans K a
  · exact ⟨3, 1, rfl, by omega, by omega⟩

end Sz22_2003_unofficial_30
