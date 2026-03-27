import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #422: [27/10, 55/21, 2/3, 7/11, 63/2]

Vector representation:
```
-1  3 -1  0  0
 0 -1  1 -1  1
 1 -1  0  0  0
 0  0  0  1 -1
-1  2  0  1  0
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_422

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a+1, b, c+1, d, e⟩ => some ⟨a, b+3, c, d, e⟩
  | ⟨a, b+1, c, d+1, e⟩ => some ⟨a, b, c+1, d, e+1⟩
  | ⟨a, b+1, c, d, e⟩ => some ⟨a+1, b, c, d, e⟩
  | ⟨a, b, c, d, e+1⟩ => some ⟨a, b, c, d+1, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b+2, c, d+1, e⟩
  | _ => none

-- R2 then R1 pair: (a+1, b+2, 0, d+1, e) ->* (a, b+4, 0, d, e+1)
private theorem r2r1_step (a b d e : ℕ) :
    ⟨a+1, b+2, 0, d+1, e⟩ [fm]⊢* ⟨a, b+4, 0, d, e+1⟩ := by
  step fm; step fm; ring_nf; finish

-- Iterate R2,R1 pairs j times starting with b+2
-- (a+j, b+2, 0, j, e) ->* (a, b+2+2*j, 0, 0, e+j)
private theorem r2r1_chain (j : ℕ) : ∀ a b e,
    ⟨a+j, b+2, 0, j, e⟩ [fm]⊢* ⟨a, b+2+2*j, 0, 0, e+j⟩ := by
  induction j with
  | zero => intro a b e; exists 0
  | succ j ih =>
    intro a b e
    rw [show a + (j + 1) = (a + j) + 1 from by ring,
        show (j : ℕ) + 1 = j + 1 from rfl]
    apply stepStar_trans (r2r1_step _ _ _ _)
    rw [show (b + 4 : ℕ) = (b + 2) + 2 from by ring]
    apply stepStar_trans (ih a (b + 2) (e + 1))
    rw [show (b + 2) + 2 + 2 * j = b + 2 + 2 * (j + 1) from by ring,
        show (e + 1) + j = e + (j + 1) from by ring]
    finish

-- R3 chain: transfer b to a
private theorem r3_chain (j : ℕ) : ∀ a b e,
    ⟨a, b+j, 0, 0, e⟩ [fm]⊢* ⟨a+j, b, 0, 0, e⟩ := by
  induction j with
  | zero => intro a b e; exists 0
  | succ j ih =>
    intro a b e
    rw [show b + (j + 1) = (b + j) + 1 from by ring]
    step fm
    apply stepStar_trans (ih _ _ _)
    rw [show (a + 1) + j = a + (j + 1) from by ring]
    finish

-- R4 chain: transfer e to d
private theorem r4_chain (j : ℕ) : ∀ a d e,
    ⟨a, 0, 0, d, e+j⟩ [fm]⊢* ⟨a, 0, 0, d+j, e⟩ := by
  induction j with
  | zero => intro a d e; exists 0
  | succ j ih =>
    intro a d e
    rw [show e + (j + 1) = (e + j) + 1 from by ring]
    step fm
    apply stepStar_trans (ih _ _ _)
    rw [show (d + 1) + j = d + (j + 1) from by ring]
    finish

-- Main transition: (n+k+3, 0, 0, k+1, 0) ⊢⁺ (n+2*k+6, 0, 0, k+2, 0)
theorem main_trans (n k : ℕ) :
    ⟨n+k+3, 0, 0, k+1, 0⟩ [fm]⊢⁺ ⟨n+2*k+6, 0, 0, k+2, 0⟩ := by
  -- Phase 1: R5 step
  -- (n+k+3, 0, 0, k+1, 0) -> (n+k+2, 2, 0, k+2, 0)
  apply step_stepStar_stepPlus
  · show fm ⟨n + k + 3, 0, 0, k + 1, 0⟩ = some ⟨n + k + 2, 2, 0, k + 2, 0⟩
    simp only [fm]
  -- Phase 2: R2,R1 chain (k+2) times
  -- (n+k+2, 2, 0, k+2, 0) ->* (n, 2k+6, 0, 0, k+2)
  apply stepStar_trans
  · have h := r2r1_chain (k + 2) n 0 0
    rw [show n + (k + 2) = n + k + 2 from by ring,
        show (0 : ℕ) + 2 = 2 from by ring] at h
    exact h
  -- Phase 3: R3 chain (2k+6) times
  -- (n, 2k+6, 0, 0, k+2) ->* (n+2k+6, 0, 0, 0, k+2)
  apply stepStar_trans
  · have h := r3_chain (0 + 2 + 2 * (k + 2)) n 0 (0 + (k + 2))
    rw [show (0 : ℕ) + (0 + 2 + 2 * (k + 2)) = 0 + 2 + 2 * (k + 2) from by ring,
        show n + (0 + 2 + 2 * (k + 2)) = n + 2 * k + 6 from by ring] at h
    exact h
  -- Phase 4: R4 chain (k+2) times
  -- (n+2k+6, 0, 0, 0, k+2) ->* (n+2k+6, 0, 0, k+2, 0)
  have h := r4_chain (k + 2) (n + 2 * k + 6) 0 0
  simp only [Nat.zero_add] at h ⊢
  exact h

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨3, 0, 0, 1, 0⟩) (by execute fm 8)
  apply progress_nonhalt_simple (fm := fm) (A := ℕ × ℕ)
    (fun p ↦ ⟨p.1 + p.2 + 3, 0, 0, p.2 + 1, 0⟩) ⟨0, 0⟩
  intro ⟨n, k⟩
  refine ⟨⟨n + k + 2, k + 1⟩, ?_⟩
  show ⟨n + k + 3, 0, 0, k + 1, 0⟩ [fm]⊢⁺ ⟨(n + k + 2) + (k + 1) + 3, 0, 0, (k + 1) + 1, 0⟩
  rw [show (n + k + 2) + (k + 1) + 3 = n + 2 * k + 6 from by ring,
      show (k + 1) + 1 = k + 2 from by ring]
  exact main_trans n k

end Sz22_2003_unofficial_422
