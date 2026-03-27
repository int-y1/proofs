import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #488: [28/15, 3/22, 25/2, 11/7, 1/3, 3/5]

Vector representation:
```
 2 -1 -1  1  0
-1  1  0  0 -1
-1  0  2  0  0
 0  0  0 -1  1
 0 -1  0  0  0
 0  1 -1  0  0
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_488

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a, b+1, c+1, d, e⟩ => some ⟨a+2, b, c, d+1, e⟩
  | ⟨a+1, b, c, d, e+1⟩ => some ⟨a, b+1, c, d, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b, c+2, d, e⟩
  | ⟨a, b, c, d+1, e⟩ => some ⟨a, b, c, d, e+1⟩
  | ⟨a, b+1, c, d, e⟩ => some ⟨a, b, c, d, e⟩
  | ⟨a, b, c+1, d, e⟩ => some ⟨a, b+1, c, d, e⟩
  | _ => none

-- R4 chain: (0, 0, c, k, e) →* (0, 0, c, 0, e+k)
theorem r4_chain : ∀ k c e, ⟨0, 0, c, k, e⟩ [fm]⊢* ⟨0, 0, c, 0, e + k⟩ := by
  intro k; induction' k with k ih <;> intro c e
  · exists 0
  · step fm; apply stepStar_trans (ih c (e + 1)); ring_nf; finish

-- R3 chain: (k, 0, c, d, 0) →* (0, 0, c + 2*k, d, 0)
theorem r3_chain : ∀ k c d, ⟨k, 0, c, d, 0⟩ [fm]⊢* ⟨0, 0, c + 2 * k, d, 0⟩ := by
  intro k; induction' k with k ih <;> intro c d
  · exists 0
  · step fm; apply stepStar_trans (ih (c + 2) d); ring_nf; finish

-- R1R2 chain: each round (A, 1, C+1, D, E+1) → R1 → (A+2, 0, C, D+1, E+1) → R2 → (A+1, 1, C, D+1, E)
-- After k rounds: (A, 1, C+k, D, E+k) →* (A+k, 1, C, D+k, E)
theorem r1r2_chain : ∀ k A C D E, ⟨A, 1, C + k, D, E + k⟩ [fm]⊢* ⟨A + k, 1, C, D + k, E⟩ := by
  intro k; induction' k with k ih <;> intro A C D E
  · exists 0
  · rw [show C + (k + 1) = (C + 1) + k from by ring,
        show E + (k + 1) = (E + 1) + k from by ring]
    apply stepStar_trans (ih A (C + 1) D (E + 1))
    step fm; step fm
    ring_nf; finish

-- Main transition: (0, 0, c, n, 0) ⊢⁺ (0, 0, c+n+2, n+1, 0) when c ≥ n+2, n ≥ 1
theorem main_transition (c n : ℕ) (hc : c ≥ n + 2) (hn : n ≥ 1) :
    ⟨0, 0, c, n, 0⟩ [fm]⊢⁺ ⟨0, 0, c + n + 2, n + 1, 0⟩ := by
  -- Phase 1: R4 x n: (0,0,c,n,0) →* (0,0,c,0,n)
  apply stepStar_stepPlus_stepPlus (c₂ := ⟨0, 0, c, 0, n⟩)
  · have h := r4_chain n c 0; simp only [Nat.zero_add] at h; exact h
  -- Phase 2: R6: (0,0,c,0,n) → (0,1,c-1,0,n)
  apply step_stepStar_stepPlus (c₂ := ⟨0, 1, c - 1, 0, n⟩)
  · show fm ⟨0, 0, c, 0, n⟩ = some ⟨0, 1, c - 1, 0, n⟩
    have : c = (c - 1) + 1 := by omega
    conv_lhs => rw [this]; simp [fm]
  -- Phase 3: R1R2 chain x n: (0,1,c-1,0,n) →* (n,1,c-1-n,n,0)
  apply stepStar_trans (c₂ := ⟨n, 1, c - 1 - n, n, 0⟩)
  · have h := r1r2_chain n 0 (c - 1 - n) 0 0
    simp only [Nat.zero_add] at h
    rw [show (c - 1 - n) + n = c - 1 from by omega] at h
    exact h
  -- Phase 3b: Final R1: (n,1,c-1-n,n,0) → (n+2,0,c-n-2,n+1,0)
  apply stepStar_trans (c₂ := ⟨n + 2, 0, c - n - 2, n + 1, 0⟩)
  · rw [show c - 1 - n = (c - n - 2) + 1 from by omega]
    step fm; ring_nf; finish
  -- Phase 4: R3 x (n+2): (n+2,0,c-n-2,n+1,0) →* (0,0,c+n+2,n+1,0)
  have h := r3_chain (n + 2) (c - n - 2) (n + 1)
  have heq : c - n - 2 + 2 * (n + 2) = c + n + 2 := by omega
  rw [heq] at h; exact h

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨0, 0, 4, 1, 0⟩) (by execute fm 5)
  apply progress_nonhalt (fm := fm)
    (P := fun q ↦ ∃ c n, q = ⟨0, 0, c, n, 0⟩ ∧ c ≥ n + 2 ∧ n ≥ 1)
  · intro q ⟨c, n, hq, hc, hn⟩; subst hq
    exact ⟨_, ⟨c + n + 2, n + 1, rfl, by omega, by omega⟩,
           main_transition c n hc hn⟩
  · exact ⟨4, 1, rfl, by omega, by omega⟩

end Sz22_2003_unofficial_488
