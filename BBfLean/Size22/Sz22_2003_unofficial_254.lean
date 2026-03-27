import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #254: [14/15, 1/22, 273/2, 55/7, 4/143]

Vector representation:
```
 1 -1 -1  1  0  0
-1  0  0  0 -1  0
-1  1  0  1  0  1
 0  0  1 -1  1  0
 2  0  0  0 -1 -1
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_254

def Q := ℕ × ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a, b+1, c+1, d, e, f⟩ => some ⟨a+1, b, c, d+1, e, f⟩
  | ⟨a+1, b, c, d, e+1, f⟩ => some ⟨a, b, c, d, e, f⟩
  | ⟨a+1, b, c, d, e, f⟩ => some ⟨a, b+1, c, d+1, e, f+1⟩
  | ⟨a, b, c, d+1, e, f⟩ => some ⟨a, b, c+1, d, e+1, f⟩
  | ⟨a, b, c, d, e+1, f+1⟩ => some ⟨a+2, b, c, d, e, f⟩
  | _ => none

-- R4 chain: (0, 0, c, k, e, f) →* (0, 0, c+k, 0, e+k, f)
theorem r4_chain : ∀ k, ∀ c e f, ⟨0, 0, c, k, e, f⟩ [fm]⊢* ⟨(0 : ℕ), 0, c + k, 0, e + k, f⟩ := by
  intro k; induction k with
  | zero => intro c e f; simp; exists 0
  | succ k ih =>
    intro c e f
    step fm
    apply stepStar_trans (ih _ _ _)
    ring_nf; finish

-- drain_step: (0, 0, C, 0, e+3, f+1) →* (0, 0, C, 0, e, f)
theorem drain_step (C e f : ℕ) : ⟨0, 0, C, 0, e + 3, f + 1⟩ [fm]⊢* ⟨(0 : ℕ), 0, C, 0, e, f⟩ := by
  rw [show e + 3 = (e + 1) + 1 + 1 from by ring]
  step fm
  step fm
  step fm
  finish

-- drain_chain: (0, 0, C, 0, e + 3*k, f + k) →* (0, 0, C, 0, e, f)
theorem drain_chain : ∀ k, ∀ C e f, ⟨0, 0, C, 0, e + 3 * k, f + k⟩ [fm]⊢* ⟨(0 : ℕ), 0, C, 0, e, f⟩ := by
  intro k; induction k with
  | zero => intro C e f; simp; exists 0
  | succ k ih =>
    intro C e f
    rw [show e + 3 * (k + 1) = (e + 3 * k) + 3 from by ring,
        show f + (k + 1) = (f + k) + 1 from by ring]
    apply stepStar_trans (drain_step C (e + 3 * k) (f + k))
    exact ih C e f

-- fold_chain: (2, 0, c+k, d, 0, f) →* (2, 0, c, d+2*k, 0, f+k)
theorem fold_chain : ∀ k, ∀ c d f, ⟨2, 0, c + k, d, 0, f⟩ [fm]⊢* ⟨(2 : ℕ), 0, c, d + 2 * k, 0, f + k⟩ := by
  intro k; induction k with
  | zero => intro c d f; simp; exists 0
  | succ k ih =>
    intro c d f
    rw [show c + (k + 1) = (c + k) + 1 from by ring]
    step fm
    rw [show (c + k) + 1 = c + k + 1 from by ring]
    step fm
    apply stepStar_trans (ih c (d + 2) (f + 1))
    ring_nf; finish

-- Main transition: (0, 2, 0, 3k+1, 0, 2k+1) →⁺ (0, 2, 0, 6k+4, 0, 4k+3)
theorem main_trans (k : ℕ) :
    ⟨0, 2, 0, 3 * k + 1, 0, 2 * k + 1⟩ [fm]⊢⁺ ⟨(0 : ℕ), 2, 0, 6 * k + 4, 0, 4 * k + 3⟩ := by
  -- Phase 1 (head): 6 steps via R4/R1/R2 repeated twice
  rw [show 3 * k + 1 = (3 * k) + 1 from by ring,
      show 2 * k + 1 = (2 * k) + 1 from by ring]
  apply step_stepStar_stepPlus (by (try unfold fm); (try simp only); rfl)
  simp only [Nat.succ_eq_add_one, Nat.reduceAdd]
  step fm
  step fm
  step fm
  step fm
  step fm
  -- Now at (0, 0, 0, 3k+1, 0, 2k+1)
  -- Phase 2 (R4 chain): (0, 0, 0, 3k+1, 0, 2k+1) →* (0, 0, 3k+1, 0, 3k+1, 2k+1)
  apply stepStar_trans (r4_chain (3 * k + 1) 0 0 (2 * k + 1))
  simp only [Nat.zero_add]
  -- Phase 3 (drain): (0, 0, 3k+1, 0, 3k+1, 2k+1) →* (0, 0, 3k+1, 0, 1, k+1) → (2, 0, 3k+1, 0, 0, k)
  apply stepStar_trans
  · have h := drain_chain k (3 * k + 1) 1 (k + 1)
    rw [show 1 + 3 * k = 3 * k + 1 from by ring,
        show (k + 1) + k = 2 * k + 1 from by ring] at h
    exact h
  -- Now at (0, 0, 3k+1, 0, 1, k+1)
  rw [show (k : ℕ) + 1 = k + 1 from rfl]
  step fm  -- R5: (2, 0, 3k+1, 0, 0, k)
  -- Phase 4 (fold): (2, 0, 3k+1, 0, 0, k) →* (2, 0, 0, 2*(3k+1), 0, k+(3k+1))
  apply stepStar_trans
  · have h := fold_chain (3 * k + 1) 0 0 k
    simp only [Nat.zero_add] at h
    exact h
  -- Phase 5 (tail): (2, 0, 0, 2*(3k+1), 0, k+(3k+1)) → → (0, 2, 0, 6k+4, 0, 4k+3)
  rw [show 2 * (3 * k + 1) = (6 * k + 2) from by ring,
      show k + (3 * k + 1) = (4 * k + 1) from by ring]
  step fm
  rw [show 6 * k + 2 + 1 = (6 * k + 3) from by ring,
      show 4 * k + 1 + 1 = (4 * k + 2) from by ring]
  step fm
  rw [show 6 * k + 3 + 1 = 6 * k + 4 from by ring,
      show 4 * k + 2 + 1 = 4 * k + 3 from by ring]
  finish

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨0, 2, 0, 4, 0, 3⟩) (by execute fm 10)
  apply progress_nonhalt_simple (fm := fm) (A := ℕ)
    (fun k ↦ ⟨0, 2, 0, 3 * k + 1, 0, 2 * k + 1⟩) 1
  intro k
  refine ⟨2 * k + 1, ?_⟩
  show ⟨0, 2, 0, 3 * k + 1, 0, 2 * k + 1⟩ [fm]⊢⁺ ⟨(0 : ℕ), 2, 0, 3 * (2 * k + 1) + 1, 0, 2 * (2 * k + 1) + 1⟩
  rw [show 3 * (2 * k + 1) + 1 = 6 * k + 4 from by ring,
      show 2 * (2 * k + 1) + 1 = 4 * k + 3 from by ring]
  exact main_trans k

end Sz22_2003_unofficial_254
