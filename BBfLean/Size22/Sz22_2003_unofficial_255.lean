import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #255: [14/15, 1/22, 507/2, 55/13, 4/77]

Vector representation:
```
 1 -1 -1  1  0  0
-1  0  0  0 -1  0
-1  1  0  0  0  2
 0  0  1  0  1 -1
 2  0  0 -1 -1  0
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_255

def Q := ℕ × ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a, b+1, c+1, d, e, f⟩ => some ⟨a+1, b, c, d+1, e, f⟩
  | ⟨a+1, b, c, d, e+1, f⟩ => some ⟨a, b, c, d, e, f⟩
  | ⟨a+1, b, c, d, e, f⟩ => some ⟨a, b+1, c, d, e, f+2⟩
  | ⟨a, b, c, d, e, f+1⟩ => some ⟨a, b, c+1, d, e+1, f⟩
  | ⟨a, b, c, d+1, e+1, f⟩ => some ⟨a+2, b, c, d, e, f⟩
  | _ => none

-- Head: one R4,R1,R2 triple absorbs one unit of b
theorem head : ∀ b d f, ⟨0, b+1, 0, d, 0, f+1⟩ [fm]⊢* ⟨(0 : ℕ), b, 0, d+1, 0, f⟩ := by
  intro b d f; step fm; step fm; step fm; finish

-- R4 chain: f -> c,e
theorem r4_chain : ∀ k c d e, ⟨0, 0, c, d, e, k⟩ [fm]⊢* ⟨(0 : ℕ), 0, c+k, d, e+k, 0⟩ := by
  intro k; induction k with
  | zero => intro c d e; simp; exists 0
  | succ k ih =>
    intro c d e
    rw [show (c : ℕ) + (k + 1) = (c + k) + 1 from by ring,
        show (e : ℕ) + (k + 1) = (e + k) + 1 from by ring]
    step fm
    apply stepStar_trans (ih _ _ _)
    ring_nf; finish

-- R5+R2+R2 chain: each triple consumes 1 from d and 3 from e
theorem r5r2r2_chain : ∀ k c d,
    ⟨0, 0, c, d+k+1, 3*k+1, 0⟩ [fm]⊢* ⟨(2 : ℕ), 0, c, d, 0, 0⟩ := by
  intro k; induction k with
  | zero =>
    intro c d
    simp
    step fm
    finish
  | succ k ih =>
    intro c d
    rw [show d + (k + 1) + 1 = (d + 1) + k + 1 from by ring,
        show 3 * (k + 1) + 1 = (3 * k + 1) + 1 + 1 + 1 from by ring]
    step fm; step fm; step fm
    rw [show d + 1 + k = d + k + 1 from by ring]
    exact ih _ _

-- Fold: R3,R1 loop + 2 final R3's
theorem fold_loop : ∀ k d f, ⟨2, 0, k, d, 0, f⟩ [fm]⊢* ⟨(2 : ℕ), 0, 0, d+k, 0, f+2*k⟩ := by
  intro k; induction k with
  | zero => intro d f; simp; exists 0
  | succ k ih =>
    intro d f
    rw [show (d : ℕ) + (k + 1) = (d + 1) + k from by ring,
        show (f : ℕ) + 2 * (k + 1) = (f + 2) + 2 * k from by ring]
    step fm; step fm
    apply stepStar_trans (ih _ _)
    ring_nf; finish

-- Fold tail: (2, 0, 0, D, 0, F) ->* (0, 2, 0, D, 0, F+4)
theorem fold_tail : ∀ d f, ⟨2, 0, 0, d, 0, f⟩ [fm]⊢* ⟨(0 : ℕ), 2, 0, d, 0, f+4⟩ := by
  intro d f; step fm; step fm; finish

-- Main transition: (0, 2, 0, 2m+1, 0, 3m+6) ->⁺ (0, 2, 0, 4m+5, 0, 6m+12)
theorem main_trans (m : ℕ) :
    ⟨0, 2, 0, 2*m+1, 0, 3*m+6⟩ [fm]⊢⁺ ⟨(0 : ℕ), 2, 0, 4*m+5, 0, 6*m+12⟩ := by
  -- Phase 1: Head (absorb b=2 via two R4,R1,R2 triples)
  -- (0, 2, 0, 2m+1, 0, 3m+6) ->* (0, 0, 0, 2m+3, 0, 3m+4) [first gives stepPlus]
  rw [show (3 : ℕ) * m + 6 = (3 * m + 4) + 1 + 1 from by ring]
  apply step_stepStar_stepPlus
  · show fm ⟨0, 2, 0, 2 * m + 1, 0, (3 * m + 4) + 1 + 1⟩ = some ⟨0, 2, 1, 2 * m + 1, 1, (3 * m + 4) + 1⟩
    simp [fm]
  step fm; step fm
  -- now at (0, 1, 0, 2m+2, 0, 3m+5)
  apply stepStar_trans (head 0 (2*m+2) (3*m+4))
  -- now at (0, 0, 0, 2m+3, 0, 3m+4)
  -- Phase 2: R4 chain (3m+4 steps)
  apply stepStar_trans (c₂ := ⟨0, 0, 3*m+4, 2*m+3, 3*m+4, 0⟩)
  · have h := r4_chain (3*m+4) 0 (2*m+3) 0
    simp only [Nat.zero_add] at h; exact h
  -- Phase 3: R5+R2+R2 chain
  -- We have (0, 0, 3m+4, 2m+3, 3m+4, 0)
  -- 3m+4 = 3*(m+1) + 1, and d = 2m+3 = (m+1) + (m+1) + 1
  apply stepStar_trans (c₂ := ⟨2, 0, 3*m+4, m+1, 0, 0⟩)
  · have h := r5r2r2_chain (m+1) (3*m+4) (m+1)
    rw [show (m : ℕ) + 1 + (m + 1) + 1 = 2 * m + 3 from by ring,
        show 3 * (m + 1) + 1 = 3 * m + 4 from by ring] at h
    exact h
  -- Phase 4: Fold
  -- (2, 0, 3m+4, m+1, 0, 0) ->* (2, 0, 0, 4m+5, 0, 6m+8)
  apply stepStar_trans (c₂ := ⟨2, 0, 0, 4*m+5, 0, 6*m+8⟩)
  · have h := fold_loop (3*m+4) (m+1) 0
    simp only [Nat.zero_add] at h
    rw [show (m : ℕ) + 1 + (3 * m + 4) = 4 * m + 5 from by ring,
        show 2 * (3 * m + 4) = 6 * m + 8 from by ring] at h
    exact h
  -- Phase 5: Fold tail
  -- (2, 0, 0, 4m+5, 0, 6m+8) ->* (0, 2, 0, 4m+5, 0, 6m+12)
  · exact fold_tail (4*m+5) (6*m+8)

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨0, 2, 0, 1, 0, 6⟩) (by execute fm 10)
  apply progress_nonhalt_simple (fm := fm) (A := ℕ)
    (fun m ↦ ⟨0, 2, 0, 2*m+1, 0, 3*m+6⟩) 0
  intro m
  refine ⟨2*m+2, ?_⟩
  show ⟨0, 2, 0, 2*m+1, 0, 3*m+6⟩ [fm]⊢⁺ ⟨(0 : ℕ), 2, 0, 2*(2*m+2)+1, 0, 3*(2*m+2)+6⟩
  rw [show 2 * (2 * m + 2) + 1 = 4 * m + 5 from by ring,
      show 3 * (2 * m + 2) + 6 = 6 * m + 12 from by ring]
  exact main_trans m

end Sz22_2003_unofficial_255
