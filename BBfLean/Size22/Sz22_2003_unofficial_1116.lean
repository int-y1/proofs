import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #1116: [5/6, 4/35, 77/2, 9/7, 245/11]

Vector representation:
```
-1 -1  1  0  0
 2  0 -1 -1  0
-1  0  0  1  1
 0  2  0 -1  0
 0  0  1  2 -1
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_1116

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a+1, b+1, c, d, e⟩ => some ⟨a, b, c+1, d, e⟩
  | ⟨a, b, c+1, d+1, e⟩ => some ⟨a+2, b, c, d, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b, c, d+1, e+1⟩
  | ⟨a, b, c, d+1, e⟩ => some ⟨a, b+2, c, d, e⟩
  | ⟨a, b, c, d, e+1⟩ => some ⟨a, b, c+1, d+2, e⟩
  | _ => none

-- R3 chain: (a+k, 0, 0, d, e) →* (a, 0, 0, d+k, e+k)
theorem a_drain : ∀ k, ∀ a d e, ⟨a + k, 0, 0, d, e⟩ [fm]⊢* ⟨a, 0, 0, d + k, e + k⟩ := by
  intro k; induction' k with k ih <;> intro a d e
  · exists 0
  · rw [show a + (k + 1) = (a + k) + 1 from by ring]
    step fm
    apply stepStar_trans (ih a (d + 1) (e + 1))
    ring_nf; finish

-- R4 chain: (0, b, 0, d+k, e) →* (0, b+2*k, 0, d, e)
theorem d_to_b : ∀ k, ∀ b d e, ⟨0, b, 0, d + k, e⟩ [fm]⊢* ⟨0, b + 2 * k, 0, d, e⟩ := by
  intro k; induction' k with k ih <;> intro b d e
  · exists 0
  · rw [show d + (k + 1) = (d + k) + 1 from by ring]
    step fm
    apply stepStar_trans (ih (b + 2) d e)
    ring_nf; finish

-- Middle round: 7 steps consuming 4 from b, 1 from e, adding 3 to c.
theorem middle_round : ⟨0, b + 4, c, 0, e + 1⟩ [fm]⊢* ⟨0, b, c + 3, 0, e⟩ := by
  step fm; step fm; step fm; step fm; step fm; step fm; step fm; finish

-- Middle loop: k rounds.
theorem middle_loop : ∀ k, ∀ b c e, ⟨0, b + 4 * k, c, 0, e + k⟩ [fm]⊢* ⟨0, b, c + 3 * k, 0, e⟩ := by
  intro k; induction' k with k ih <;> intro b c e
  · exists 0
  · rw [show b + 4 * (k + 1) = (b + 4) + 4 * k from by ring,
        show e + (k + 1) = (e + 1) + k from by ring]
    apply stepStar_trans (ih (b + 4) c (e + 1))
    exact middle_round

-- Odd tail: 5 steps when b=2 remains.
theorem odd_tail : ⟨0, 2, c, 0, e + 1⟩ [fm]⊢* ⟨2, 0, c + 1, 0, e⟩ := by
  step fm; step fm; step fm; step fm; step fm; finish

-- R5+R2+R2: (0, 0, c+1, 0, e+1) →* (4, 0, c, 0, e)
theorem r5r2r2 : ⟨0, 0, c + 1, 0, e + 1⟩ [fm]⊢* ⟨4, 0, c, 0, e⟩ := by
  step fm; step fm; step fm; finish

-- R3+R2 interleave: (a+1, 0, c+k, 0, e) →* (a+1+k, 0, c, 0, e+k)
theorem r3r2_interleave : ∀ k, ∀ a c e, ⟨a + 1, 0, c + k, 0, e⟩ [fm]⊢* ⟨a + 1 + k, 0, c, 0, e + k⟩ := by
  intro k; induction' k with k ih <;> intro a c e
  · exists 0
  · rw [show c + (k + 1) = (c + k) + 1 from by ring]
    step fm; step fm
    rw [show a + 2 = (a + 1) + 1 from by ring]
    apply stepStar_trans (ih (a + 1) c (e + 1))
    ring_nf; finish

-- Even transition: (2*(k+1), 0, 0, 0, e) →⁺ (3*k+6, 0, 0, 0, 4*k+e+2)
theorem even_trans : ⟨2 * k + 2, 0, 0, 0, e⟩ [fm]⊢⁺ ⟨3 * k + 6, 0, 0, 0, 4 * k + e + 2⟩ := by
  -- Phase 1: first R3 step + drain
  rw [show 2 * k + 2 = (2 * k + 1) + 1 from by ring]
  step fm
  rw [show 2 * k + 1 = 0 + (2 * k + 1) from by ring]
  apply stepStar_trans (a_drain (2 * k + 1) 0 1 (e + 1))
  -- Phase 2: R4 drain d to b
  rw [show 1 + (2 * k + 1) = 0 + (2 * k + 2) from by ring,
      show e + 1 + (2 * k + 1) = 2 * k + 2 + e from by ring]
  apply stepStar_trans (d_to_b (2 * k + 2) 0 0 (2 * k + 2 + e))
  -- Phase 3: middle loop, k+1 rounds
  rw [show 0 + 2 * (2 * k + 2) = 0 + 4 * (k + 1) from by ring,
      show 2 * k + 2 + e = (k + 1 + e) + (k + 1) from by ring]
  apply stepStar_trans (middle_loop (k + 1) 0 0 (k + 1 + e))
  -- Phase 4: R5+R2+R2
  rw [show 0 + 3 * (k + 1) = (3 * k + 2) + 1 from by ring,
      show k + 1 + e = (k + e) + 1 from by ring]
  apply stepStar_trans (r5r2r2 (c := 3 * k + 2) (e := k + e))
  -- Phase 5: R3/R2 interleave, 3*k+2 rounds
  rw [show (4 : ℕ) = 3 + 1 from by ring,
      show (3 * k + 2 : ℕ) = 0 + (3 * k + 2) from by ring]
  apply stepStar_trans (r3r2_interleave (3 * k + 2) 3 0 (k + e))
  ring_nf; finish

-- Odd transition: (2*k+1, 0, 0, 0, e) →⁺ (3*k+3, 0, 0, 0, 4*k+e+1)
theorem odd_trans : ⟨2 * k + 1, 0, 0, 0, e⟩ [fm]⊢⁺ ⟨3 * k + 3, 0, 0, 0, 4 * k + e + 1⟩ := by
  -- Phase 1: first R3 step + drain
  rw [show 2 * k + 1 = (2 * k) + 1 from by ring]
  step fm
  rw [show 2 * k = 0 + 2 * k from by ring]
  apply stepStar_trans (a_drain (2 * k) 0 1 (e + 1))
  -- Phase 2: R4 drain d to b
  rw [show 1 + 2 * k = 0 + (2 * k + 1) from by ring,
      show e + 1 + 2 * k = 2 * k + 1 + e from by ring]
  apply stepStar_trans (d_to_b (2 * k + 1) 0 0 (2 * k + 1 + e))
  -- Phase 3: middle loop, k rounds
  rw [show 0 + 2 * (2 * k + 1) = 2 + 4 * k from by ring,
      show 2 * k + 1 + e = (k + 1 + e) + k from by ring]
  apply stepStar_trans (middle_loop k 2 0 (k + 1 + e))
  -- Phase 4: odd tail (b=2)
  rw [show 0 + 3 * k = 3 * k from by ring,
      show k + 1 + e = (k + e) + 1 from by ring]
  apply stepStar_trans (odd_tail (c := 3 * k) (e := k + e))
  -- Phase 5: R3/R2 interleave, 3*k+1 rounds
  rw [show (2 : ℕ) = 1 + 1 from by ring,
      show 3 * k + 1 = 0 + (3 * k + 1) from by ring]
  apply stepStar_trans (r3r2_interleave (3 * k + 1) 1 0 (k + e))
  ring_nf; finish

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨3, 0, 0, 0, 1⟩)
  · execute fm 9
  apply progress_nonhalt (fm := fm)
    (P := fun q ↦ ∃ a e, q = ⟨a, 0, 0, 0, e⟩ ∧ a ≥ 1)
  · intro c ⟨a, e, hq, ha⟩; subst hq
    rcases Nat.even_or_odd a with ⟨K, hK⟩ | ⟨K, hK⟩
    · -- a even: a = K + K = 2*K, K >= 1
      rw [show K + K = 2 * K from by ring] at hK; subst hK
      obtain ⟨k, rfl⟩ : ∃ k, K = k + 1 := ⟨K - 1, by omega⟩
      exact ⟨⟨3 * k + 6, 0, 0, 0, 4 * k + e + 2⟩,
        ⟨3 * k + 6, 4 * k + e + 2, rfl, by omega⟩,
        even_trans⟩
    · -- a odd: a = 2*K + 1
      subst hK
      exact ⟨⟨3 * K + 3, 0, 0, 0, 4 * K + e + 1⟩,
        ⟨3 * K + 3, 4 * K + e + 1, rfl, by omega⟩,
        odd_trans⟩
  · exact ⟨3, 1, rfl, by omega⟩

end Sz22_2003_unofficial_1116
