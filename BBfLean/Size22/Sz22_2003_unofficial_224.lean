import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #224: [105/2, 20/99, 1/75, 33/7, 1/3]

Vector representation:
```
-1  1  1  1  0
 2 -2  1  0 -1
 0 -1 -2  0  0
 0  1  0 -1  1
 0 -1  0  0  0
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_224

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b+1, c+1, d+1, e⟩
  | ⟨a, b+2, c, d, e+1⟩ => some ⟨a+2, b, c+1, d, e⟩
  | ⟨a, b+1, c+2, d, e⟩ => some ⟨a, b, c, d, e⟩
  | ⟨a, b, c, d+1, e⟩ => some ⟨a, b+1, c, d, e+1⟩
  | ⟨a, b+1, c, d, e⟩ => some ⟨a, b, c, d, e⟩
  | _ => none

-- R4 then R3: (0, 0, c+2, d+1, e) ->* (0, 0, c, d, e+1)
theorem r4r3_pair (c d e : ℕ) : ⟨0, 0, c+2, d+1, e⟩ [fm]⊢* ⟨(0 : ℕ), 0, c, d, e+1⟩ := by
  step fm; step fm; finish

-- Phase 1 even: (0, 0, 2k, d+k, e) ->* (0, 0, 0, d, e+k)
theorem drain_even : ∀ k d e, ⟨0, 0, 2*k, d+k, e⟩ [fm]⊢* ⟨(0 : ℕ), 0, 0, d, e+k⟩ := by
  intro k; induction k with
  | zero => intro d e; exists 0
  | succ k ih =>
    intro d e
    rw [show 2 * (k + 1) = 2 * k + 2 from by ring,
        show d + (k + 1) = (d + k) + 1 from by ring]
    apply stepStar_trans (r4r3_pair (2*k) (d+k) e)
    have h := ih d (e + 1)
    rw [show e + 1 + k = e + (k + 1) from by ring] at h
    exact h

-- Phase 1 odd: (0, 0, 2k+1, d+k, e) ->* (0, 0, 1, d, e+k)
theorem drain_odd : ∀ k d e, ⟨0, 0, 2*k+1, d+k, e⟩ [fm]⊢* ⟨(0 : ℕ), 0, 1, d, e+k⟩ := by
  intro k; induction k with
  | zero => intro d e; exists 0
  | succ k ih =>
    intro d e
    rw [show 2 * (k + 1) + 1 = (2 * k + 1) + 2 from by ring,
        show d + (k + 1) = (d + k) + 1 from by ring]
    apply stepStar_trans (r4r3_pair (2*k+1) (d+k) e)
    have h := ih d (e + 1)
    rw [show e + 1 + k = e + (k + 1) from by ring] at h
    exact h

-- R2,R1,R1 cycle: (0, 2, c, d, e+k) ->* (0, 2, c+3k, d+2k, e)
theorem r2r1r1_cycle : ∀ k c d e, ⟨0, 2, c, d, e+k⟩ [fm]⊢* ⟨(0 : ℕ), 2, c+3*k, d+2*k, e⟩ := by
  intro k; induction k with
  | zero => intro c d e; exists 0
  | succ k ih =>
    intro c d e
    rw [show e + (k + 1) = (e + k) + 1 from by ring]
    step fm; step fm; step fm
    apply stepStar_trans (ih _ _ _)
    ring_nf; finish

-- R3 pair cleanup: (0, 2, c+4, d, 0) ->* (0, 0, c, d, 0)
theorem r3_cleanup (c d : ℕ) : ⟨0, 2, c+4, d, 0⟩ [fm]⊢* ⟨(0 : ℕ), 0, c, d, 0⟩ := by
  rw [show c + 4 = c + 2 + 2 from by ring, show (2 : ℕ) = 1 + 1 from by ring]
  step fm; step fm; finish

-- Even transition: (0, 0, 2k, 2k+2, 0) ⊢⁺ (0, 0, 3k+2, 3k+4, 0)
theorem trans_even (k : ℕ) : ⟨0, 0, 2*k, 2*k+2, 0⟩ [fm]⊢⁺ ⟨(0 : ℕ), 0, 3*k+2, 3*k+4, 0⟩ := by
  -- Phase 1: (0, 0, 2k, (k+2)+k, 0) ->* (0, 0, 0, k+2, k)
  apply stepStar_stepPlus_stepPlus
  · rw [show 2 * k + 2 = (k + 2) + k from by ring]
    exact drain_even k (k+2) 0
  rw [show (0 : ℕ) + k = k from by ring]
  -- Phase 2: two R4 steps: (0, 0, 0, k+2, k) -> (0, 2, 0, k, k+2)
  rw [show k + 2 = k + 1 + 1 from by ring]
  apply step_stepStar_stepPlus
  · show fm ⟨0, 0, 0, (k + 1) + 1, k⟩ = some ⟨0, 1, 0, k + 1, k + 1⟩; simp [fm]
  rw [show k + 1 = k + 1 from rfl]
  step fm
  -- Now at (0, 2, 0, k, k+2). Need to show k+1+1 = 0+(k+2)
  -- Phase 3: k+2 R2,R1,R1 iterations
  apply stepStar_trans (c₂ := ⟨0, 2, 3*(k+2), k+2*(k+2), 0⟩)
  · have h := r2r1r1_cycle (k+2) 0 k 0
    rw [show (0 : ℕ) + (k + 2) = k + 2 from by ring,
        show 0 + 3 * (k + 2) = 3 * (k + 2) from by ring] at h
    rw [show k + 1 + 1 = k + 2 from by ring]
    exact h
  -- Phase 4: two R3 steps
  rw [show 3 * (k + 2) = (3 * k + 2) + 4 from by ring,
      show k + 2 * (k + 2) = 3 * k + 4 from by ring]
  exact r3_cleanup (3*k+2) (3*k+4)

-- Odd transition: (0, 0, 2k+1, 2k+3, 0) ⊢⁺ (0, 0, 3k+3, 3k+5, 0)
theorem trans_odd (k : ℕ) : ⟨0, 0, 2*k+1, 2*k+3, 0⟩ [fm]⊢⁺ ⟨(0 : ℕ), 0, 3*k+3, 3*k+5, 0⟩ := by
  -- Phase 1: (0, 0, 2k+1, (k+3)+k, 0) ->* (0, 0, 1, k+3, k)
  apply stepStar_stepPlus_stepPlus
  · rw [show 2 * k + 3 = (k + 3) + k from by ring]
    exact drain_odd k (k+3) 0
  rw [show (0 : ℕ) + k = k from by ring]
  -- Phase 2: two R4 steps: (0, 0, 1, k+3, k) -> (0, 2, 1, k+1, k+2)
  rw [show k + 3 = k + 2 + 1 from by ring]
  apply step_stepStar_stepPlus
  · show fm ⟨0, 0, 1, (k + 2) + 1, k⟩ = some ⟨0, 1, 1, k + 2, k + 1⟩; simp [fm]
  rw [show k + 2 = k + 1 + 1 from by ring]
  step fm
  -- Now at (0, 2, 1, k+1, k+2). Need k+1+1 = 0+(k+2)
  -- Phase 3: k+2 R2,R1,R1 iterations
  apply stepStar_trans (c₂ := ⟨0, 2, 1+3*(k+2), (k+1)+2*(k+2), 0⟩)
  · have h := r2r1r1_cycle (k+2) 1 (k+1) 0
    rw [show (0 : ℕ) + (k + 2) = k + 2 from by ring] at h
    rw [show k + 1 + 1 = k + 2 from by ring]
    exact h
  -- Phase 4: two R3 steps
  rw [show 1 + 3 * (k + 2) = (3 * k + 3) + 4 from by ring,
      show (k + 1) + 2 * (k + 2) = 3 * k + 5 from by ring]
  exact r3_cleanup (3*k+3) (3*k+5)

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨0, 0, 0, 2, 0⟩) (by execute fm 7)
  apply progress_nonhalt_simple (fm := fm) (A := ℕ) (fun c ↦ ⟨0, 0, c, c+2, 0⟩) 0
  intro c
  rcases Nat.even_or_odd c with ⟨k, hk⟩ | ⟨k, hk⟩
  · subst hk
    rcases k with _ | k
    · exists 2; execute fm 10
    · exists 3*(k+1)+2
      simp only [show (k + 1) + (k + 1) = 2 * (k + 1) from by ring,
                  show 3 * (k + 1) + 2 + 2 = 3 * (k + 1) + 4 from by ring]
      exact trans_even (k+1)
  · subst hk
    exists 3*k+3
    simp only [show 2 * k + 1 + 2 = 2 * k + 3 from by ring,
                show 3 * k + 3 + 2 = 3 * k + 5 from by ring]
    exact trans_odd k

end Sz22_2003_unofficial_224
