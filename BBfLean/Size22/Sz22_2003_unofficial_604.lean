import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #604: [35/6, 121/2, 4/55, 3/7, 35/11]

Vector representation:
```
-1 -1  1  1  0
-1  0  0  0  2
 2  0 -1  0 -1
 0  1  0 -1  0
 0  0  1  1 -1
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_604

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a+1, b+1, c, d, e⟩ => some ⟨a, b, c+1, d+1, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b, c, d, e+2⟩
  | ⟨a, b, c+1, d, e+1⟩ => some ⟨a+2, b, c, d, e⟩
  | ⟨a, b, c, d+1, e⟩ => some ⟨a, b+1, c, d, e⟩
  | ⟨a, b, c, d, e+1⟩ => some ⟨a, b, c+1, d+1, e⟩
  | _ => none

-- R4 repeated: convert d to b
theorem d_to_b : ∀ k b, ⟨0, b, 0, d+k, e⟩ [fm]⊢* ⟨0, b+k, 0, d, e⟩ := by
  intro k; induction' k with k h <;> intro b
  · exists 0
  rw [show d + (k + 1) = d + k + 1 from by ring]
  step fm
  apply stepStar_trans (h _)
  ring_nf; finish

-- R1,R1,R3 chain: each round consumes 2 from b, 1 from e, adds 1 to c, 2 to d
theorem r1r1r3_chain : ∀ k c d, ⟨2, b+2*k, c, d, e+k⟩ [fm]⊢* ⟨2, b, c+k, d+2*k, e⟩ := by
  intro k; induction' k with k h <;> intro c d
  · exists 0
  rw [show b + 2 * (k + 1) = (b + 2 * k) + 1 + 1 from by ring,
      show e + (k + 1) = (e + k) + 1 from by ring]
  step fm; step fm; step fm
  apply stepStar_trans (h _ _)
  ring_nf; finish

-- R2,R2,R3 drain: each round consumes 1 from c, adds 3 to e
theorem r2r2r3_drain : ∀ k c e, ⟨2, 0, c+k, d, e⟩ [fm]⊢* ⟨2, 0, c, d, e+3*k⟩ := by
  intro k; induction' k with k h <;> intro c e
  · exists 0
  rw [show c + (k + 1) = (c + k) + 1 from by ring]
  step fm; step fm; step fm
  apply stepStar_trans (h _ _)
  ring_nf; finish

-- Even transition: (1,0,0,2*(m+1),E+(m+1)) ⊢⁺ (1,0,0,2*(m+1)+1,E+2*(m+1)+2+(m+1))
-- i.e., with e = E+(m+1), target e = E+3*(m+1)+2
theorem even_trans : ⟨1, 0, 0, 2*(m+1), E+(m+1)⟩ [fm]⊢⁺ ⟨1, 0, 0, 2*(m+1)+1, E+3*(m+1)+2⟩ := by
  -- Phase 1: R2
  step fm
  -- Phase 2: d_to_b
  have h1 := @d_to_b 0 (E+(m+1)+2) (2*(m+1)) 0
  rw [Nat.zero_add] at h1
  apply stepStar_trans h1
  -- Phase 3: R5, R3
  have h2 : ⟨0, 2*(m+1), 0, 0, E+(m+1)+2⟩ [fm]⊢* ⟨2, 2*(m+1), 0, 1, E+(m+1)⟩ := by
    step fm; step fm; finish
  apply stepStar_trans h2
  -- Phase 4: r1r1r3_chain (m+1 rounds)
  have h3 := @r1r1r3_chain 0 E (m+1) 0 1
  simp only [Nat.zero_add] at h3
  refine stepStar_trans h3 ?_
  -- Phase 5: r2r2r3_drain (m+1 rounds)
  have h4 := @r2r2r3_drain (1+2*(m+1)) (m+1) 0 E
  simp only [Nat.zero_add] at h4
  apply stepStar_trans h4
  -- Final R2
  rw [show 1 + 2 * (m + 1) = 2 * (m + 1) + 1 from by ring]
  step fm
  ring_nf; finish

-- Odd transition: (1,0,0,2*m+1,E+m) ⊢⁺ (1,0,0,2*m+2,E+3*m+3)
theorem odd_trans : ⟨1, 0, 0, 2*m+1, E+m⟩ [fm]⊢⁺ ⟨1, 0, 0, 2*m+2, E+3*m+3⟩ := by
  -- Phase 1: R2
  step fm
  -- Phase 2: d_to_b
  have h1 := @d_to_b 0 (E+m+2) (2*m+1) 0
  rw [Nat.zero_add] at h1
  apply stepStar_trans h1
  -- Phase 3: R5, R3
  have h2 : ⟨0, 2*m+1, 0, 0, E+m+2⟩ [fm]⊢* ⟨2, 2*m+1, 0, 1, E+m⟩ := by
    step fm; step fm; finish
  apply stepStar_trans h2
  -- Phase 4: r1r1r3_chain (m rounds, leaving b=1)
  rw [show 2*m+1 = 1+2*m from by ring]
  have h3 := @r1r1r3_chain 1 E m 0 1
  simp only [Nat.zero_add] at h3
  apply stepStar_trans h3
  -- Phase 4b: final R1, R2, R3
  rw [show 1 + 2 * m = 2 * m + 1 from by ring]
  have h4 : ⟨2, 1, m, 2*m+1, E⟩ [fm]⊢* ⟨2, 0, m, 2*(m+1), E+1⟩ := by
    step fm; step fm; step fm
    ring_nf; finish
  apply stepStar_trans h4
  -- Phase 5: r2r2r3_drain (m rounds)
  have h5 := @r2r2r3_drain (2*(m+1)) m 0 (E+1)
  simp only [Nat.zero_add] at h5
  apply stepStar_trans h5
  -- Final R2
  step fm
  ring_nf; finish

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨1, 0, 0, 1, 2⟩) (by execute fm 4)
  apply progress_nonhalt (fm := fm)
    (P := fun q ↦ ∃ d e, q = ⟨1, 0, 0, d+1, e⟩ ∧ e ≥ d + 1)
  · intro c ⟨d, e, hq, he⟩; subst hq
    rcases Nat.even_or_odd d with ⟨K, hK⟩ | ⟨K, hK⟩
    · -- d even: d = K+K
      subst hK
      obtain ⟨E, rfl⟩ : ∃ E, e = E + K := ⟨e - K, by omega⟩
      exact ⟨⟨1, 0, 0, K+K+2, E+3*K+3⟩,
        ⟨K+K+1, E+3*K+3, rfl, by omega⟩,
        by rw [show K + K + 1 = 2 * K + 1 from by ring,
               show K + K + 2 = 2 * K + 2 from by ring]; exact odd_trans⟩
    · -- d odd: d = 2*K+1
      subst hK
      obtain ⟨E, rfl⟩ : ∃ E, e = E + (K + 1) := ⟨e - (K + 1), by omega⟩
      exact ⟨⟨1, 0, 0, 2*(K+1)+1, E+3*(K+1)+2⟩,
        ⟨2*(K+1), E+3*(K+1)+2, rfl, by omega⟩,
        by rw [show 2 * K + 1 + 1 = 2 * (K + 1) from by ring]; exact even_trans⟩
  · exact ⟨0, 2, rfl, by omega⟩
