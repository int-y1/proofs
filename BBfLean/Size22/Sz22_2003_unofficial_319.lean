import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #319: [154/15, 6/7, 1/3, 25/2, 1/55, 3/5]

Vector representation:
```
 1 -1 -1  1  1
 1  1  0 -1  0
 0 -1  0  0  0
-1  0  2  0  0
 0  0 -1  0 -1
 0  1 -1  0  0
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_319

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a, b+1, c+1, d, e⟩ => some ⟨a+1, b, c, d+1, e+1⟩
  | ⟨a, b, c, d+1, e⟩ => some ⟨a+1, b+1, c, d, e⟩
  | ⟨a, b+1, c, d, e⟩ => some ⟨a, b, c, d, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b, c+2, d, e⟩
  | ⟨a, b, c+1, d, e+1⟩ => some ⟨a, b, c, d, e⟩
  | ⟨a, b, c+1, d, e⟩ => some ⟨a, b+1, c, d, e⟩
  | _ => none

-- R1+R2 chain: (0, 1, c, 0, 0) →* (2*c, 1, 0, 0, c)
-- Each pair: (a, 1, k+1, 0, e) → R1 → (a+1, 0, k, 1, e+1) → R2 → (a+2, 1, k, 0, e+1)
-- After c pairs: (2*c, 1, 0, 0, c)
theorem r12_chain : ∀ k a e,
    ⟨a, 1, k, 0, e⟩ [fm]⊢* ⟨a + 2 * k, 1, 0, 0, e + k⟩ := by
  intro k; induction k with
  | zero => intro a e; exists 0
  | succ k ih =>
    intro a e
    step fm; step fm
    apply stepStar_trans (ih _ _)
    ring_nf; finish

-- R4 chain: (a, 0, c, 0, e) →* (0, 0, c + 2*a, 0, e)
theorem r4_chain : ∀ a c e,
    ⟨a, 0, c, 0, e⟩ [fm]⊢* ⟨0, 0, c + 2 * a, 0, e⟩ := by
  intro a; induction a with
  | zero => intro c e; exists 0
  | succ a ih =>
    intro c e
    step fm
    apply stepStar_trans (ih _ _)
    ring_nf; finish

-- R5 chain: (0, 0, c + e, 0, e) →* (0, 0, c, 0, 0)
theorem r5_chain : ∀ e c,
    ⟨0, 0, c + e, 0, e⟩ [fm]⊢* ⟨0, 0, c, 0, 0⟩ := by
  intro e; induction e with
  | zero => intro c; exists 0
  | succ e ih =>
    intro c
    rw [show c + (e + 1) = (c + e) + 1 from by ring]
    step fm
    apply stepStar_trans (ih _)
    finish

-- Main transition: (0, 0, c+1, 0, 0) →⁺ (0, 0, 3*c, 0, 0) for c ≥ 1
-- Phase 1: R6: (0, 0, c+1, 0, 0) → (0, 1, c, 0, 0)
-- Phase 2: R1+R2 chain: (0, 1, c, 0, 0) →* (2*c, 1, 0, 0, c)
-- Phase 3: R3: (2*c, 1, 0, 0, c) → (2*c, 0, 0, 0, c)
-- Phase 4: R4 chain: (2*c, 0, 0, 0, c) →* (0, 0, 4*c, 0, c)
-- Phase 5: R5 chain: (0, 0, 4*c, 0, c) →* (0, 0, 3*c, 0, 0)
theorem main_trans (c : ℕ) :
    ⟨0, 0, c + 1, 0, 0⟩ [fm]⊢⁺ ⟨0, 0, 3 * c, 0, 0⟩ := by
  -- Phase 1: R6 (produces stepPlus, remaining goal is stepStar)
  step fm
  -- Phase 2: R1+R2 chain
  apply stepStar_trans (r12_chain c 0 0)
  simp only [Nat.zero_add]
  -- Phase 3: R3
  step fm
  -- Phase 4: R4 chain: (2*c, 0, 0, 0, c) →* (0, 0, 4*c, 0, c)
  apply stepStar_trans (r4_chain (2 * c) 0 c)
  -- Phase 5: R5 chain: (0, 0, 4*c, 0, c) →* (0, 0, 3*c, 0, 0)
  rw [show 0 + 2 * (2 * c) = 3 * c + c from by ring]
  apply stepStar_trans (r5_chain c (3 * c))
  finish

def seq : ℕ → ℕ
  | 0 => 3
  | n+1 => 3 * seq n - 3

theorem seq_ge_3 : ∀ n, seq n ≥ 3 := by
  intro n; induction n with
  | zero => simp [seq]
  | succ n ih => simp [seq]; omega

theorem seq_step : ∀ n, ⟨0, 0, seq n, 0, 0⟩ [fm]⊢⁺ ⟨0, 0, seq (n+1), 0, 0⟩ := by
  intro n
  have h1 : seq n = (seq n - 1) + 1 := by have := seq_ge_3 n; omega
  have h2 : seq (n+1) = 3 * (seq n - 1) := by
    simp [seq]; have := seq_ge_3 n; omega
  rw [h1, h2]
  exact main_trans (seq n - 1)

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨0, 0, seq 0, 0, 0⟩)
  · show c₀ [fm]⊢* ⟨0, 0, 3, 0, 0⟩
    execute fm 8
  apply progress_nonhalt_simple
    (C := fun n ↦ (⟨0, 0, seq n, 0, 0⟩ : Q)) (i₀ := 0)
  intro n
  exact ⟨n + 1, seq_step n⟩
