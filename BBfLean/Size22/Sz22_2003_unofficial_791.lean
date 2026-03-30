import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #791: [35/6, 605/2, 4/385, 3/5, 2/11]

Vector representation:
```
-1 -1  1  1  0
-1  0  1  0  2
 2  0 -1 -1 -1
 0  1 -1  0  0
 1  0  0  0 -1
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_791

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a+1, b+1, c, d, e⟩ => some ⟨a, b, c+1, d+1, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b, c+1, d, e+2⟩
  | ⟨a, b, c+1, d+1, e+1⟩ => some ⟨a+2, b, c, d, e⟩
  | ⟨a, b, c+1, d, e⟩ => some ⟨a, b+1, c, d, e⟩
  | ⟨a, b, c, d, e+1⟩ => some ⟨a+1, b, c, d, e⟩
  | _ => none

-- R4 chain: move c to b (general version with accumulator).
theorem c_to_b : ∀ k, ⟨0, b, c + k, 0, e⟩ [fm]⊢* ⟨0, b + k, c, 0, e⟩ := by
  intro k; induction' k with k ih generalizing b c
  · exists 0
  · rw [show c + (k + 1) = (c + k) + 1 from by ring]
    step fm
    apply stepStar_trans (ih (b := b + 1))
    ring_nf; finish

-- R1-R1-R3 chain with accumulator c.
-- Each round: (2, b+2, c, c, e+1) →* (2, b, c+1, c+1, e)
theorem r1r1r3 : ∀ k, ⟨2, b + 2 * k, c, c, e + k⟩ [fm]⊢* ⟨2, b, c + k, c + k, e⟩ := by
  intro k; induction' k with k ih generalizing b c e
  · exists 0
  · rw [show b + 2 * (k + 1) = (b + 2) + 2 * k from by ring,
        show e + (k + 1) = (e + 1) + k from by ring]
    apply stepStar_trans (ih (b := b + 2) (e := e + 1))
    step fm; step fm; step fm; ring_nf; finish

-- R2-R2-R3 chain with accumulator c.
-- Each round: (2, 0, c, d+1, e) →* (2, 0, c+1, d, e+3)
theorem r2r2r3 : ∀ k, ⟨2, 0, c, k, e⟩ [fm]⊢* ⟨2, 0, c + k, 0, e + 3 * k⟩ := by
  intro k; induction' k with k ih generalizing c e
  · exists 0
  · step fm; step fm; step fm
    show ⟨2, 0, c + 1, k, e + 3⟩ [fm]⊢* _
    apply stepStar_trans (ih (c := c + 1) (e := e + 3))
    ring_nf; finish

-- Odd transition: (0, 0, 2k+1, 0, e+k+2) →⁺ (0, 0, 2k+2, 0, e+3k+4)
theorem odd_trans (k e : ℕ) :
    ⟨0, 0, 2 * k + 1, 0, e + k + 2⟩ [fm]⊢⁺ ⟨0, 0, 2 * k + 2, 0, e + 3 * k + 4⟩ := by
  -- R4 first step
  step fm
  -- R4 chain: (0, 1, 2k, 0, e+k+2) →* (0, 1+2k, 0, 0, e+k+2)
  rw [show (2 * k : ℕ) = 0 + 2 * k from by omega]
  apply stepStar_trans (c_to_b (2 * k) (b := 1) (c := 0) (e := e + k + 2))
  -- Now at (0, 1+2*k, 0, 0, e+k+2). But 1+2*k doesn't match b+1 for R1.
  -- Rewrite to 2*k+1 which is Nat.succ (2*k).
  rw [show 1 + 2 * k = 2 * k + 1 from by ring]
  -- R5, R1, R3
  step fm; step fm; step fm
  -- Now at (2, 2*k, 0, 0, e+k)
  -- r1r1r3 chain with b=0
  rw [show (2 * k : ℕ) = 0 + 2 * k from by omega]
  apply stepStar_trans (r1r1r3 k (b := 0) (c := 0) (e := e))
  -- Now at (2, 0, 0+k, 0+k, e)
  -- r2r2r3 chain. Need to match 0+k in d position.
  apply stepStar_trans (r2r2r3 (0 + k) (c := 0 + k) (e := e))
  -- Final R2, R2
  step fm; step fm
  ring_nf; finish

-- Even transition: (0, 0, 2k+2, 0, e+k+3) →⁺ (0, 0, 2k+3, 0, e+3k+6)
theorem even_trans (k e : ℕ) :
    ⟨0, 0, 2 * k + 2, 0, e + k + 3⟩ [fm]⊢⁺ ⟨0, 0, 2 * k + 3, 0, e + 3 * k + 6⟩ := by
  -- R4 first step
  step fm
  -- R4 chain: (0, 1, 2k+1, 0, e+k+3) →* (0, 1+(2k+1), 0, 0, e+k+3)
  rw [show (2 * k + 1 : ℕ) = 0 + (2 * k + 1) from by omega]
  apply stepStar_trans (c_to_b (2 * k + 1) (b := 1) (c := 0) (e := e + k + 3))
  rw [show 1 + (2 * k + 1) = 2 * k + 2 from by ring]
  -- R5, R1, R3
  step fm; step fm; step fm
  -- Now at (2, 2*k+1, 0, 0, e+k+1)
  -- r1r1r3 chain with b=1, k rounds
  rw [show (2 * k + 1 : ℕ) = 1 + 2 * k from by omega,
      show e + k + 1 = (e + 1) + k from by ring]
  apply stepStar_trans (r1r1r3 k (b := 1) (c := 0) (e := e + 1))
  -- Now at (2, 1, 0+k, 0+k, e+1). 1 matches b+1 since 1 = 0+1.
  -- R1, R2, R3
  step fm; step fm; step fm
  -- Now at (2, 0, (0+k)+1, 0+k, e+2)
  -- r2r2r3 chain with d = 0+k
  apply stepStar_trans (r2r2r3 (0 + k) (c := (0 + k) + 1) (e := e + 2))
  -- Final R2, R2
  step fm; step fm
  ring_nf; finish

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨0, 0, 1, 0, 2⟩) (by execute fm 1)
  apply progress_nonhalt (fm := fm)
    (P := fun q ↦ ∃ n e, q = ⟨0, 0, n + 1, 0, e⟩ ∧ e ≥ n + 2)
  · intro c ⟨n, e, hq, he⟩; subst hq
    rcases Nat.even_or_odd n with ⟨K, hK⟩ | ⟨K, hK⟩
    · -- n even: n = 2*K
      rw [show K + K = 2 * K from by ring] at hK; subst hK
      obtain ⟨f, rfl⟩ : ∃ f, e = f + K + 2 := ⟨e - K - 2, by omega⟩
      refine ⟨⟨0, 0, 2 * K + 2, 0, f + 3 * K + 4⟩,
        ⟨2 * K + 1, f + 3 * K + 4, rfl, by omega⟩, ?_⟩
      rw [show 2 * K + 1 + 1 = 2 * K + 2 from by ring]
      exact odd_trans K f
    · -- n odd: n = 2*K+1
      subst hK
      obtain ⟨f, rfl⟩ : ∃ f, e = f + K + 3 := ⟨e - K - 3, by omega⟩
      refine ⟨⟨0, 0, 2 * K + 3, 0, f + 3 * K + 6⟩,
        ⟨2 * K + 2, f + 3 * K + 6, rfl, by omega⟩, ?_⟩
      rw [show 2 * K + 2 + 1 = 2 * K + 3 from by ring]
      exact even_trans K f
  · exact ⟨0, 2, rfl, by omega⟩
