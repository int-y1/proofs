import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #1648: [77/15, 28/3, 63/22, 5/7, 3/2]

Vector representation:
```
 0 -1 -1  1  1
 2 -1  0  1  0
-1  2  0  1 -1
 0  0  1 -1  0
-1  1  0  0  0
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_1648

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a, b+1, c+1, d, e⟩ => some ⟨a, b, c, d+1, e+1⟩
  | ⟨a, b+1, c, d, e⟩ => some ⟨a+2, b, c, d+1, e⟩
  | ⟨a+1, b, c, d, e+1⟩ => some ⟨a, b+2, c, d+1, e⟩
  | ⟨a, b, c, d+1, e⟩ => some ⟨a, b, c+1, d, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b+1, c, d, e⟩
  | _ => none

theorem r4_chain : ∀ k, ∀ a c d, ⟨a, 0, c, d + k, 0⟩ [fm]⊢* ⟨a, 0, c + k, d, 0⟩ := by
  intro k; induction' k with k ih <;> intro a c d
  · exists 0
  · rw [show d + (k + 1) = (d + k) + 1 from by ring]
    step fm
    apply stepStar_trans (ih a (c + 1) d); ring_nf; finish

theorem drain_e : ∀ k, ∀ A D,
    ⟨A + 1, 0, 0, D, k⟩ [fm]⊢* ⟨A + 1 + 3 * k, 0, 0, D + 3 * k, 0⟩ := by
  intro k; induction' k with k ih <;> intro A D
  · exists 0
  · rw [show (k : ℕ) + 1 = k + 1 from rfl]
    step fm; step fm; step fm
    rw [show A + 2 + 2 = (A + 3) + 1 from by ring,
        show D + 1 + 1 + 1 = D + 3 from by ring]
    have h := ih (A + 3) (D + 3)
    rw [show A + 3 + 1 + 3 * k = A + 1 + 3 * (k + 1) from by ring,
        show D + 3 + 3 * k = D + 3 * (k + 1) from by ring] at h
    exact h

theorem r3r1r1_chain : ∀ k, ∀ A C D E,
    ⟨A + 1 + k, 0, C + 2 * k, D, E + 1⟩ [fm]⊢* ⟨A + 1, 0, C, D + 3 * k, E + 1 + k⟩ := by
  intro k; induction' k with k ih <;> intro A C D E
  · exists 0
  · rw [show A + 1 + (k + 1) = (A + 1 + k) + 1 from by ring,
        show C + 2 * (k + 1) = (C + 2 * k) + 1 + 1 from by ring,
        show E + 1 = E + 1 from rfl]
    step fm; step fm; step fm
    rw [show D + 1 + 1 + 1 = D + 3 from by ring,
        show E + 1 + 1 = (E + 1) + 1 from by ring]
    have h := ih A C (D + 3) (E + 1)
    rw [show D + 3 + 3 * k = D + 3 * (k + 1) from by ring,
        show E + 1 + 1 + k = E + 1 + (k + 1) from by ring] at h
    exact h

theorem r3r1r2_step (A D E : ℕ) :
    ⟨A + 1, 0, 1, D, E + 1⟩ [fm]⊢* ⟨A + 2, 0, 0, D + 3, E + 1⟩ := by
  step fm; step fm; step fm; ring_nf; finish

-- Even case: c = 2*K
-- From (a, 0, 2*K, 1, 1) to (a+2*K+3, 0, 6*K+4, 0, 0)
-- where a = A+1+K
theorem even_trans (A K : ℕ) :
    ⟨A + 1 + K, 0, 2 * K, 1, 1⟩ [fm]⊢* ⟨A + 3 * K + 4, 0, 6 * K + 4, 0, 0⟩ := by
  -- Phase 1: r3r1r1_chain with k=K, C=0, D=1, E=0
  rw [show 2 * K = 0 + 2 * K from by ring, show (1 : ℕ) = 0 + 1 from by ring]
  apply stepStar_trans (r3r1r1_chain K A 0 1 0)
  -- State: (A+1, 0, 0, 1+3*K, 0+1+K)
  rw [show 1 + 3 * K = 3 * K + 1 from by ring, show 0 + 1 + K = K + 1 from by ring]
  -- Phase 2: drain_e with k=K+1
  apply stepStar_trans (drain_e (K + 1) A (3 * K + 1))
  -- State: (A+1+3*(K+1), 0, 0, 3K+1+3*(K+1), 0) = (A+3K+4, 0, 0, 6K+4, 0)
  rw [show A + 1 + 3 * (K + 1) = A + 3 * K + 4 from by ring,
      show 3 * K + 1 + 3 * (K + 1) = 0 + (6 * K + 4) from by ring]
  -- Phase 3: r4_chain
  apply stepStar_trans (r4_chain (6 * K + 4) (A + 3 * K + 4) 0 0)
  rw [show 0 + (6 * K + 4) = 6 * K + 4 from by ring]; finish

-- Odd case: c = 2*K+1
-- From (a, 0, 2*K+1, 1, 1) to (a+2*K+4, 0, 6*K+7, 0, 0)
-- where a = A+1+K
theorem odd_trans (A K : ℕ) :
    ⟨A + 1 + K, 0, 2 * K + 1, 1, 1⟩ [fm]⊢* ⟨A + 3 * K + 5, 0, 6 * K + 7, 0, 0⟩ := by
  -- Phase 1a: r3r1r1_chain with k=K, C=1, D=1, E=0
  rw [show 2 * K + 1 = 1 + 2 * K from by ring, show (1 : ℕ) = 0 + 1 from by ring]
  apply stepStar_trans (r3r1r1_chain K A 1 1 0)
  -- State: (A+1, 0, 1, 1+3*K, 0+1+K) = (A+1, 0, 1, 3K+1, K+1)
  rw [show 1 + 3 * K = 3 * K + 1 from by ring, show 0 + 1 + K = K + 1 from by ring]
  -- Phase 1b: r3r1r2_step
  rw [show K + 1 = K + 1 from rfl]
  apply stepStar_trans (r3r1r2_step A (3 * K + 1) K)
  -- State: (A+2, 0, 0, 3K+4, K+1)
  rw [show A + 2 = (A + 1) + 1 from by ring]
  -- Phase 2: drain_e
  apply stepStar_trans (drain_e (K + 1) (A + 1) (3 * K + 4))
  rw [show A + 1 + 1 + 3 * (K + 1) = A + 3 * K + 5 from by ring,
      show 3 * K + 4 + 3 * (K + 1) = 0 + (6 * K + 7) from by ring]
  -- Phase 3: r4_chain
  apply stepStar_trans (r4_chain (6 * K + 7) (A + 3 * K + 5) 0 0)
  rw [show 0 + (6 * K + 7) = 6 * K + 7 from by ring]; finish

theorem main_trans (a c : ℕ) (ha : 2 * a ≥ c) :
    ⟨a + 1, 0, c, 0, 0⟩ [fm]⊢⁺ ⟨a + c + 2, 0, 3 * c + 1, 0, 0⟩ := by
  rcases c with _ | c
  · step fm; step fm; step fm; finish
  · -- R5 + R1: two steps give ⊢⁺
    have h1 : ⟨a + 1, 0, c + 1, 0, 0⟩ [fm]⊢⁺ ⟨a, 0, c, 1, 1⟩ := by
      rw [show c + 1 = c + 1 from rfl]; step fm; step fm; finish
    rcases Nat.even_or_odd c with ⟨K, hK⟩ | ⟨K, hK⟩
    · -- c = K + K (even)
      subst hK
      obtain ⟨A, rfl⟩ : ∃ A, a = A + 1 + K := ⟨a - 1 - K, by omega⟩
      rw [show K + K = 2 * K from by ring] at h1 ⊢
      exact stepPlus_stepStar_stepPlus h1
        (show ⟨A + 1 + K, 0, 2 * K, 1, 1⟩ [fm]⊢* ⟨A + 1 + K + (2 * K + 1) + 2, 0, 3 * (2 * K + 1) + 1, 0, 0⟩ by
          have h2 := even_trans A K
          rw [show A + 3 * K + 4 = A + 1 + K + (2 * K + 1) + 2 from by ring,
              show 6 * K + 4 = 3 * (2 * K + 1) + 1 from by ring] at h2
          exact h2)
    · -- c = 2*K + 1 (odd)
      subst hK
      obtain ⟨A, rfl⟩ : ∃ A, a = A + 1 + K := ⟨a - 1 - K, by omega⟩
      exact stepPlus_stepStar_stepPlus h1
        (show ⟨A + 1 + K, 0, 2 * K + 1, 1, 1⟩ [fm]⊢* ⟨A + 1 + K + (2 * K + 1 + 1) + 2, 0, 3 * (2 * K + 1 + 1) + 1, 0, 0⟩ by
          have h2 := odd_trans A K
          rw [show A + 3 * K + 5 = A + 1 + K + (2 * K + 1 + 1) + 2 from by ring,
              show 6 * K + 7 = 3 * (2 * K + 1 + 1) + 1 from by ring] at h2
          exact h2)

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨2, 0, 1, 0, 0⟩) (by execute fm 3)
  apply progress_nonhalt (fm := fm)
    (P := fun q ↦ ∃ a c, q = ⟨a + 1, 0, c, 0, 0⟩ ∧ 2 * a ≥ c)
  · intro q ⟨a, c, hq, ha⟩; subst hq
    exact ⟨⟨a + c + 2, 0, 3 * c + 1, 0, 0⟩,
           ⟨a + c + 1, 3 * c + 1, rfl, by omega⟩,
           main_trans a c ha⟩
  · exact ⟨1, 1, rfl, by omega⟩
