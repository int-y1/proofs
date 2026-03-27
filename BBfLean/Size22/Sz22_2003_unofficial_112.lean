import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #112: [1/30, 63/5, 25/77, 2/7, 605/2]

Vector representation:
```
-1 -1 -1  0  0
 0  2 -1  1  0
 0  0  2 -1 -1
 1  0  0 -1  0
-1  0  1  0  2
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_112

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a+1, b+1, c+1, d, e⟩ => some ⟨a, b, c, d, e⟩
  | ⟨a, b, c+1, d, e⟩ => some ⟨a, b+2, c, d+1, e⟩
  | ⟨a, b, c, d+1, e+1⟩ => some ⟨a, b, c+2, d, e⟩
  | ⟨a, b, c, d+1, e⟩ => some ⟨a+1, b, c, d, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b, c+1, d, e+2⟩
  | _ => none

-- R4 repeated: d → a
theorem d_to_a : ∀ k, ∀ a b, ⟨a, b, 0, k, 0⟩ [fm]⊢* ⟨a + k, b, (0 : ℕ), 0, 0⟩ := by
  intro k; induction k with
  | zero => intro a b; exists 0
  | succ k ih =>
    intro a b
    rw [show (k + 1 : ℕ) = k + 1 from rfl]
    step fm
    apply stepStar_trans (ih _ _)
    ring_nf; finish

-- R5,R1 chain: alternating R5 and R1, draining a and b
theorem r5r1_chain : ∀ k, ∀ a b e,
    ⟨a + 2 * k, b + k, 0, 0, e⟩ [fm]⊢* ⟨a, b, (0 : ℕ), 0, e + 2 * k⟩ := by
  intro k; induction k with
  | zero => intro a b e; simp; exists 0
  | succ k ih =>
    intro a b e
    rw [show a + 2 * (k + 1) = (a + 2 * k + 1) + 1 from by ring,
        show b + (k + 1) = (b + k) + 1 from by ring]
    step fm
    -- After R5: (a+2*k+1, b+k+1, 1, 0, e+2); R1 matches since a+2*k+1≥1, b+k+1≥1, 1≥1
    step fm
    -- After R1: (a+2*k, b+k, 0, 0, e+2)
    rw [show e + 2 * (k + 1) = (e + 2) + 2 * k from by ring]
    exact ih a b (e + 2)

-- Cycle: (R3, R2, R2) repeated k times
-- From (0, b, 0, d+1, e+k) to (0, b+4k, 0, d+1+k, e)
theorem cycle : ∀ k, ∀ b d e,
    ⟨0, b, 0, d + 1, e + k⟩ [fm]⊢* ⟨0, b + 4 * k, (0 : ℕ), d + 1 + k, e⟩ := by
  intro k; induction k with
  | zero => intro b d e; simp; exists 0
  | succ k ih =>
    intro b d e
    rw [show e + (k + 1) = (e + k) + 1 from by ring,
        show d + 1 = d + 1 from rfl]
    -- R3: (0, b, 0, d+1, (e+k)+1) -> (0, b, 2, d, e+k)
    step fm
    -- R2: (0, b, 2, d, e+k) -> (0, b+2, 1, d+1, e+k)
    show ⟨0, b, 2, d, e + k⟩ [fm]⊢* _
    step fm
    -- R2: (0, b+2, 1, d+1, e+k) -> (0, b+4, 0, d+2, e+k)
    show ⟨0, b + 2, 1, d + 1, e + k⟩ [fm]⊢* _
    step fm
    show ⟨0, b + 2 + 2, 0, d + 1 + 1, e + k⟩ [fm]⊢* _
    rw [show d + 1 + 1 = (d + 1) + 1 from by ring]
    apply stepStar_trans (ih (b + 2 + 2) (d + 1) e)
    rw [show b + 2 + 2 + 4 * k = b + 4 * (k + 1) from by ring,
        show d + 1 + 1 + k = d + 1 + (k + 1) from by ring]
    finish

-- Main transition: (2k+1, b, 0, 0, 0) ⊢+ (2k+3, b + 7k + 10, 0, 0, 0) for b ≥ k
theorem main_step : ∀ k b, b ≥ k →
    ⟨2 * k + 1, b, 0, 0, 0⟩ [fm]⊢⁺ ⟨2 * k + 3, b + 7 * k + 10, (0 : ℕ), 0, 0⟩ := by
  intro k b hbk
  -- Phase 1: R5/R1 drain
  -- (2k+1, b, 0, 0, 0) ⊢* (1, b-k, 0, 0, 2k)
  obtain ⟨b', rfl⟩ : ∃ b', b = b' + k := ⟨b - k, by omega⟩
  rw [show 2 * k + 1 = 1 + 2 * k from by ring]
  apply stepStar_stepPlus_stepPlus
  · exact r5r1_chain k 1 b' 0
  -- Now at (1, b', 0, 0, 2k)
  -- Phase 2: R5 then R2
  rw [show (0 : ℕ) + 2 * k = 2 * k from by ring]
  step fm
  -- After R5: (0, b', 1, 0, 2k+2)
  step fm
  -- After R2: (0, b'+2, 0, 1, 2k+2)
  -- Phase 3: cycle (2k+2) times
  rw [show (1 : ℕ) = 0 + 1 from by ring,
      show 2 * k + 2 = 0 + (2 * k + 2) from by ring]
  apply stepStar_trans (cycle (2 * k + 2) (b' + 2) 0 0)
  -- Now at (0, b'+2+4*(2k+2), 0, 1+(2k+2), 0) = (0, b'+8k+10, 0, 2k+3, 0)
  rw [show b' + 2 + 4 * (2 * k + 2) = b' + k + 7 * k + 10 from by ring,
      show 0 + 1 + (2 * k + 2) = 2 * k + 3 from by ring]
  -- Phase 4: R4 repeated (2k+3) times
  apply stepStar_trans (d_to_a (2 * k + 3) 0 (b' + k + 7 * k + 10))
  rw [show 0 + (2 * k + 3) = 2 * k + 3 from by ring]
  finish

-- Bootstrap: c₀ reaches the first canonical state
theorem bootstrap : c₀ [fm]⊢* ⟨3, 10, (0 : ℕ), 0, 0⟩ := by
  unfold c₀; execute fm 11

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts bootstrap
  apply progress_nonhalt (fm := fm)
    (P := fun q ↦ ∃ k b, q = ⟨2 * k + 1, b, (0 : ℕ), 0, 0⟩ ∧ b ≥ k ∧ k ≥ 1)
  · intro q ⟨k, b, hq, hbk, hk⟩
    subst hq
    refine ⟨⟨2 * k + 3, b + 7 * k + 10, (0 : ℕ), 0, 0⟩,
            ⟨k + 1, b + 7 * k + 10, rfl, by omega, by omega⟩,
            main_step k b hbk⟩
  · exact ⟨1, 10, rfl, by omega, by omega⟩

end Sz22_2003_unofficial_112
