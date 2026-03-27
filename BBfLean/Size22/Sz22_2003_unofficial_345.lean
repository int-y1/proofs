import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #345: [2/15, 1/14, 99/2, 7/3, 5/77, 2/7]

Vector representation:
```
 1 -1 -1  0  0
-1  0  0 -1  0
-1  2  0  0  1
 0 -1  0  1  0
 0  0  1 -1 -1
 1  0  0 -1  0
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_345

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a, b+1, c+1, d, e⟩ => some ⟨a+1, b, c, d, e⟩
  | ⟨a+1, b, c, d+1, e⟩ => some ⟨a, b, c, d, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b+2, c, d, e+1⟩
  | ⟨a, b+1, c, d, e⟩ => some ⟨a, b, c, d+1, e⟩
  | ⟨a, b, c, d+1, e+1⟩ => some ⟨a, b, c+1, d, e⟩
  | ⟨a, b, c, d+1, e⟩ => some ⟨a+1, b, c, d, e⟩
  | _ => none

-- R4 chain: convert b to d
theorem b_to_d : ∀ k b d e, ⟨0, b+k, 0, d, e⟩ [fm]⊢* ⟨0, b, 0, d+k, e⟩ := by
  intro k; induction k with
  | zero => intro b d e; exists 0
  | succ k ih =>
    intro b d e
    rw [show b + (k + 1) = (b + k) + 1 from by ring]
    step fm
    apply stepStar_trans (ih _ _ _)
    ring_nf; finish

-- R5 chain: convert d,e pairs to c
theorem r5_chain : ∀ k c d e, ⟨0, 0, c, d+k, e+k⟩ [fm]⊢* ⟨0, 0, c+k, d, e⟩ := by
  intro k; induction k with
  | zero => intro c d e; exists 0
  | succ k ih =>
    intro c d e
    rw [show d + (k + 1) = (d + k) + 1 from by ring,
        show e + (k + 1) = (e + k) + 1 from by ring]
    step fm
    apply stepStar_trans (ih _ _ _)
    ring_nf; finish

-- R3 chain: convert a to b,e
theorem a_to_b : ∀ k a b e, ⟨a+k, b, 0, 0, e⟩ [fm]⊢* ⟨a, b+2*k, 0, 0, e+k⟩ := by
  intro k; induction k with
  | zero => intro a b e; exists 0
  | succ k ih =>
    intro a b e
    rw [show a + (k + 1) = (a + k) + 1 from by ring]
    step fm
    apply stepStar_trans (ih _ _ _)
    ring_nf; finish

-- Generalized consume loop: (a+1, 0, 2*k, 0, e) ->* (a+1+k, 0, 0, 0, e+k)
theorem consume_even : ∀ k a e, ⟨a+1, 0, 2*k, 0, e⟩ [fm]⊢* ⟨a+1+k, 0, 0, 0, e+k⟩ := by
  intro k; induction k with
  | zero => intro a e; exists 0
  | succ k ih =>
    intro a e
    rw [show 2 * (k + 1) = (2 * k) + 2 from by ring]
    -- R3: (a, 2, 2*k+2, 0, e+1)
    step fm
    rw [show 2 * k + 2 = (2 * k) + 1 + 1 from by ring]
    -- R1: (a+1, 1, 2*k+1, 0, e+1)
    step fm
    -- R1: (a+2, 0, 2*k, 0, e+1)
    step fm
    apply stepStar_trans (ih (a+1) (e+1))
    ring_nf; finish

-- Generalized consume loop for odd: (a+1, 0, 2*k+1, 0, e) ->* (a+1+k, 1, 0, 0, e+k+1)
theorem consume_odd : ∀ k a e, ⟨a+1, 0, 2*k+1, 0, e⟩ [fm]⊢* ⟨a+1+k, 1, 0, 0, e+k+1⟩ := by
  intro k; induction k with
  | zero =>
    intro a e
    step fm  -- R3: (a, 2, 1, 0, e+1)
    step fm  -- R1: (a+1, 1, 0, 0, e+1)
    finish
  | succ k ih =>
    intro a e
    rw [show 2 * (k + 1) + 1 = (2 * k + 1) + 2 from by ring]
    step fm  -- R3
    rw [show 2 * k + 1 + 2 = (2 * k + 1) + 1 + 1 from by ring]
    step fm  -- R1
    step fm  -- R1
    apply stepStar_trans (ih (a+1) (e+1))
    ring_nf; finish

-- Phase 4 for even c: (1, 0, 2*K, 0, 0) ->* (0, 2*K+2, 0, 0, 2*K+1)
theorem phase4_even (K : ℕ) : ⟨1, 0, 2*K, 0, 0⟩ [fm]⊢* ⟨0, 2*K+2, 0, 0, 2*K+1⟩ := by
  apply stepStar_trans (consume_even K 0 0)
  rw [show 0 + 1 + K = K + 1 from by ring, show 0 + K = K from by ring]
  have h := a_to_b (K+1) 0 0 K
  simp only [Nat.zero_add] at h
  rw [show 2 * (K + 1) = 2 * K + 2 from by ring,
      show K + (K + 1) = 2 * K + 1 from by ring] at h
  exact h

-- Phase 4 for odd c: (1, 0, 2*K+1, 0, 0) ->* (0, 2*K+3, 0, 0, 2*K+2)
theorem phase4_odd (K : ℕ) : ⟨1, 0, 2*K+1, 0, 0⟩ [fm]⊢* ⟨0, 2*K+3, 0, 0, 2*K+2⟩ := by
  apply stepStar_trans (consume_odd K 0 0)
  rw [show 0 + 1 + K = K + 1 from by ring, show 0 + K + 1 = K + 1 from by ring]
  -- Now at (K+1, 1, 0, 0, K+1). Apply R3 chain (K+1) times via a_to_b.
  have h := a_to_b (K+1) 0 1 (K+1)
  simp only [Nat.zero_add] at h
  rw [show 1 + 2 * (K + 1) = 2 * K + 3 from by ring,
      show K + 1 + (K + 1) = 2 * K + 2 from by ring] at h
  exact h

-- Phases 1-3: (0, n+2, 0, 0, n+1) ->* (1, 0, n+1, 0, 0)
theorem phases123 (n : ℕ) : ⟨0, n+2, 0, 0, n+1⟩ [fm]⊢⁺ ⟨1, 0, n+1, 0, 0⟩ := by
  -- Phase 1: R4 x (n+2)
  apply stepStar_stepPlus_stepPlus
  · have h := b_to_d (n+2) 0 0 (n+1)
    simp only [Nat.zero_add] at h; exact h
  -- Phase 2: R5 x (n+1)
  apply stepStar_step_stepPlus
  · have h := r5_chain (n+1) 0 1 0
    rw [show 0 + (n + 1) = n + 1 from by ring,
        show 1 + (n + 1) = n + 2 from by ring] at h
    exact h
  -- Phase 3: R6: (0, 0, n+1, 1, 0) -> (1, 0, n+1, 0, 0)
  show fm ⟨0, 0, n + 1, 0 + 1, 0⟩ = some ⟨0 + 1, 0, n + 1, 0, 0⟩
  rfl

-- Main transition: (0, n+2, 0, 0, n+1) ⊢⁺ (0, n+3, 0, 0, n+2)
theorem main_trans (n : ℕ) : ⟨0, n+2, 0, 0, n+1⟩ [fm]⊢⁺ ⟨0, n+3, 0, 0, n+2⟩ := by
  apply stepPlus_stepStar_stepPlus (phases123 n)
  rcases Nat.even_or_odd (n+1) with ⟨K, hK⟩ | ⟨K, hK⟩
  · -- n+1 = 2*K (even), hK : n + 1 = K + K
    have h := phase4_even K
    rw [show 2 * K + 2 = n + 3 from by omega,
        show 2 * K + 1 = n + 2 from by omega,
        show 2 * K = n + 1 from by omega] at h
    exact h
  · -- n+1 = 2*K+1 (odd), hK : n + 1 = 2 * K + 1
    have h := phase4_odd K
    rw [show 2 * K + 3 = n + 3 from by omega,
        show 2 * K + 2 = n + 2 from by omega,
        show 2 * K + 1 = n + 1 from by omega] at h
    exact h

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨0, 2, 0, 0, 1⟩) (by execute fm 1)
  apply progress_nonhalt_simple (fm := fm) (A := ℕ) (fun n ↦ ⟨0, n+2, 0, 0, n+1⟩) 0
  intro n
  exact ⟨n+1, main_trans n⟩

end Sz22_2003_unofficial_345
