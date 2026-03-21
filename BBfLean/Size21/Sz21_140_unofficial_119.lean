import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz21_140_unofficial #119: [77/15, 9/14, 2/3, 5/11, 99/2]

Vector representation:
```
 0 -1 -1  1  1
-1  2  0 -1  0
 1 -1  0  0  0
 0  0  1  0 -1
-1  2  0  0  1
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz21_140_unofficial_119

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a, b+1, c+1, d, e⟩ => some ⟨a, b, c, d+1, e+1⟩
  | ⟨a+1, b, c, d+1, e⟩ => some ⟨a, b+2, c, d, e⟩
  | ⟨a, b+1, c, d, e⟩ => some ⟨a+1, b, c, d, e⟩
  | ⟨a, b, c, d, e+1⟩ => some ⟨a, b, c+1, d, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b+2, c, d, e+1⟩
  | _ => none

-- R4 repeated: e → c (with b=0, d=0)
theorem e_to_c : ∀ k, ∀ a c, ⟨a, 0, c, 0, k⟩ [fm]⊢* ⟨a, 0, c+k, 0, 0⟩ := by
  intro k; induction' k with k ih <;> intro a c
  · exists 0
  rw [show c + (k + 1) = (c + k) + 1 from by ring]
  step fm
  apply stepStar_trans (ih _ _); ring_nf; finish

-- R3 repeated: b → a (with c=0, d=0)
theorem b_to_a : ∀ k, ∀ a e, ⟨a, k, 0, 0, e⟩ [fm]⊢* ⟨a+k, 0, 0, 0, e⟩ := by
  intro k; induction' k with k ih <;> intro a e
  · exists 0
  step fm
  apply stepStar_trans (ih _ _); ring_nf; finish

-- One round of (R1, R1, R2): needs a>=1, c>=2, b=2
-- (a+1, 2, c+2, d, e) ->* (a, 2, c, d+1, e+2)
theorem one_round : ∀ a c d e, ⟨a+1, 2, c+2, d, e⟩ [fm]⊢* ⟨a, 2, c, d+1, e+2⟩ := by
  intro a c d e
  step fm; step fm
  rw [show d + 2 = (d + 1) + 1 from by ring]
  step fm; finish

-- K rounds of (R1, R1, R2)
theorem many_rounds : ∀ k, ∀ a c d e, ⟨a+k, 2, c+2*k, d, e⟩ [fm]⊢* ⟨a, 2, c, d+k, e+2*k⟩ := by
  intro k; induction' k with k ih <;> intro a c d e
  · exists 0
  rw [show a + (k + 1) = (a + k) + 1 from by ring,
      show c + 2 * (k + 1) = (c + 2 * k) + 2 from by ring]
  apply stepStar_trans (one_round _ _ _ _)
  apply stepStar_trans (ih _ _ _ _); ring_nf; finish

-- R2 chain: drains a and d (with b arbitrary, c=0)
-- (a+k, b, 0, d+k, e) ->* (a, b+2*k, 0, d, e)
theorem r2_chain : ∀ k, ∀ a b d e, ⟨a+k, b, 0, d+k, e⟩ [fm]⊢* ⟨a, b+2*k, 0, d, e⟩ := by
  intro k; induction' k with k ih <;> intro a b d e
  · exists 0
  rw [show a + (k + 1) = (a + k) + 1 from by ring,
      show d + (k + 1) = (d + k) + 1 from by ring]
  step fm
  apply stepStar_trans (ih _ _ _ _); ring_nf; finish

-- Middle phase for even n = 2K
-- (2K, 2, 2K, 0, 1) ->* (0, 2K+2, 0, 0, 2K+1)
theorem middle_even (K : ℕ) : ⟨2*K, 2, 2*K, 0, 1⟩ [fm]⊢* ⟨0, 2*K+2, 0, 0, 2*K+1⟩ := by
  -- K rounds of R1R1R2: (K+K, 2, 0+2K, 0, 1) ->* (K, 2, 0, K, 2K+1)
  apply stepStar_trans (c₂ := ⟨K, 2, 0, K, 2*K+1⟩)
  · have h := many_rounds K K 0 0 1
    rw [show K + K = 2 * K from by ring,
        show 0 + 2 * K = 2 * K from by ring,
        show 0 + K = K from by ring,
        show 1 + 2 * K = 2 * K + 1 from by ring] at h
    exact h
  -- R2 chain: (0+K, 2, 0, 0+K, 2K+1) ->* (0, 2+2K, 0, 0, 2K+1)
  have h := r2_chain K 0 2 0 (2*K+1)
  rw [show 0 + K = K from by ring,
      show 2 + 2 * K = 2 * K + 2 from by ring] at h
  exact h

-- Middle phase for odd n = 2K+1
-- (2K+1, 2, 2K+1, 0, 1) ->* (0, 2K+3, 0, 0, 2K+2)
theorem middle_odd (K : ℕ) : ⟨2*K+1, 2, 2*K+1, 0, 1⟩ [fm]⊢* ⟨0, 2*K+3, 0, 0, 2*K+2⟩ := by
  -- K rounds: ((K+1)+K, 2, 1+2K, 0, 1) ->* (K+1, 2, 1, K, 2K+1)
  apply stepStar_trans (c₂ := ⟨K+1, 2, 1, K, 2*K+1⟩)
  · have h := many_rounds K (K+1) 1 0 1
    rw [show K + 1 + K = 2 * K + 1 from by ring,
        show 1 + 2 * K = 2 * K + 1 from by ring,
        show 0 + K = K from by ring] at h
    exact h
  -- R1: (K+1, 2, 1, K, 2K+1) -> (K+1, 1, 0, K+1, 2K+2)
  apply stepStar_trans (c₂ := ⟨K+1, 1, 0, K+1, 2*K+2⟩)
  · step fm; ring_nf; finish
  -- R2 chain: ((K+1), 1, 0, (K+1), 2K+2) ->* (0, 1+2*(K+1), 0, 0, 2K+2)
  -- = (0, 2K+3, 0, 0, 2K+2)
  have h := r2_chain (K+1) 0 1 0 (2*K+2)
  rw [show 0 + (K + 1) = K + 1 from by ring,
      show 1 + 2 * (K + 1) = 2 * K + 3 from by ring] at h
  exact h

-- Main transition
theorem main_trans : ⟨n+1, 0, 0, 0, n⟩ [fm]⊢⁺ ⟨n+2, 0, 0, 0, n+1⟩ := by
  -- Phase 1: e_to_c: ->* (n+1, 0, n, 0, 0)
  apply stepStar_stepPlus_stepPlus (c₂ := ⟨n+1, 0, n, 0, 0⟩)
  · have h := e_to_c n (n+1) 0
    rw [show 0 + n = n from by ring] at h; exact h
  -- Phase 2: R5: (n+1, 0, n, 0, 0) -> (n, 2, n, 0, 1)
  apply step_stepStar_stepPlus (c₂ := ⟨n, 2, n, 0, 1⟩)
  · show fm ⟨n + 1, 0, n, 0, 0⟩ = some ⟨n, 2, n, 0, 1⟩; simp [fm]
  -- Phase 3: middle ->* (0, n+2, 0, 0, n+1)
  apply stepStar_trans (c₂ := ⟨0, n+2, 0, 0, n+1⟩)
  · rcases Nat.even_or_odd n with ⟨K, hK⟩ | ⟨K, hK⟩
    · rw [show K + K = 2 * K from by ring] at hK; subst hK
      exact middle_even K
    · subst hK
      have h := middle_odd K
      rw [show 2 * K + 1 + 2 = 2 * K + 3 from by ring,
          show 2 * K + 1 + 1 = 2 * K + 2 from by ring]
      exact h
  -- Phase 4: b_to_a: (0, n+2, 0, 0, n+1) ->* (n+2, 0, 0, 0, n+1)
  have h := b_to_a (n+2) 0 (n+1)
  rw [show 0 + (n + 2) = n + 2 from by ring] at h; exact h

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨1, 0, 0, 0, 0⟩) (by exists 0)
  apply progress_nonhalt_simple (fm := fm) (A := ℕ) (fun n ↦ ⟨n+1, 0, 0, 0, n⟩) 0
  intro n; exact ⟨n+1, main_trans⟩

end Sz21_140_unofficial_119
