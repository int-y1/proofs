import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #492: [28/15, 3/22, 25/2, 11/7, 242/5]

Vector representation:
```
 2 -1 -1  1  0
-1  1  0  0 -1
-1  0  2  0  0
 0  0  0 -1  1
 1  0 -1  0  2
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_492

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a, b+1, c+1, d, e⟩ => some ⟨a+2, b, c, d+1, e⟩
  | ⟨a+1, b, c, d, e+1⟩ => some ⟨a, b+1, c, d, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b, c+2, d, e⟩
  | ⟨a, b, c, d+1, e⟩ => some ⟨a, b, c, d, e+1⟩
  | ⟨a, b, c+1, d, e⟩ => some ⟨a+1, b, c, d, e+2⟩
  | _ => none

-- Phase 1: R3 chain, convert a to c (b=0, e=0)
theorem a_to_c : ∀ k a c d, ⟨a+k, 0, c, d, 0⟩ [fm]⊢* ⟨a, 0, c+2*k, d, 0⟩ := by
  intro k; induction' k with k h <;> intro a c d
  · exists 0
  rw [← Nat.add_assoc]
  step fm
  apply stepStar_trans (h _ _ _)
  ring_nf; finish

-- Phase 2: R4 chain, convert d to e (a=0)
theorem d_to_e : ∀ k c d e, ⟨0, 0, c, d+k, e⟩ [fm]⊢* ⟨0, 0, c, d, e+k⟩ := by
  intro k; induction' k with k h <;> intro c d e
  · exists 0
  rw [← Nat.add_assoc]
  step fm
  apply stepStar_trans (h _ _ _)
  ring_nf; finish

-- Phase 5: R1+R2 interleaved chain
-- From (j, 1, c+k, j, e+k) to (j+k, 1, c, j+k, e) via k rounds of R1+R2
theorem r1r2_chain : ∀ k j c e, ⟨j, 1, c+k, j, e+k⟩ [fm]⊢* ⟨j+k, 1, c, j+k, e⟩ := by
  intro k; induction' k with k h <;> intro j c e
  · simp; exists 0
  rw [show c + (k + 1) = (c + k) + 1 from by ring,
      show e + (k + 1) = (e + k) + 1 from by ring]
  step fm  -- R1: (j+2, 0, c+k, j+1, e+k+1)
  step fm  -- R2: (j+1, 1, c+k, j+1, e+k)
  apply stepStar_trans (h _ _ _)
  ring_nf; finish

-- Main transition: C(n) ⊢⁺ C(n+1)
-- C(n) = (2*n+5, 0, n*n+2*n, 2*n+4, 0)
-- C(n+1) = (2*n+7, 0, n*n+4*n+3, 2*n+6, 0)
theorem main_trans (n : ℕ) :
    ⟨2*n+5, 0, n*n+2*n, 2*n+4, 0⟩ [fm]⊢⁺ ⟨2*n+7, 0, n*n+4*n+3, 2*n+6, 0⟩ := by
  -- Phase 1: R3 x (2n+5), a->0, c gains 2*(2n+5)
  -- (2n+5, 0, n²+2n, 2n+4, 0) ->* (0, 0, n²+6n+10, 2n+4, 0)
  -- Note: n²+2n + 2*(2n+5) = n²+6n+10 = (n+1)²+4(n+1)+5 = n²+6n+10
  -- Actually (n+1)² + 1 + 4n + 4 ... let me just use: n*n+6*n+10
  apply step_stepStar_stepPlus
  · -- First R3 step to get ⊢⁺
    show fm ⟨2 * n + 5, 0, n * n + 2 * n, 2 * n + 4, 0⟩ = some ⟨2 * n + 4, 0, n * n + 2 * n + 2, 2 * n + 4, 0⟩
    simp [fm]
  -- Remaining R3 steps
  apply stepStar_trans (c₂ := ⟨0, 0, n*n+6*n+10, 2*n+4, 0⟩)
  · have h := a_to_c (2*n+4) 0 (n*n+2*n+2) (2*n+4)
    simp only [Nat.zero_add, (by ring : n * n + 2 * n + 2 + 2 * (2 * n + 4) = n * n + 6 * n + 10)] at h
    exact h
  -- Phase 2: R4 x (2n+4), d->0, e gains 2n+4
  -- (0, 0, n²+6n+10, 2n+4, 0) ->* (0, 0, n²+6n+10, 0, 2n+4)
  apply stepStar_trans (c₂ := ⟨0, 0, n*n+6*n+10, 0, 2*n+4⟩)
  · have h := d_to_e (2*n+4) (n*n+6*n+10) 0 0
    simp only [Nat.zero_add] at h; exact h
  -- Phase 3: R5 step
  -- (0, 0, n²+6n+10, 0, 2n+4) -> (1, 0, n²+6n+9, 0, 2n+6)
  step fm
  -- Phase 4: R2 step
  -- (1, 0, n²+6n+9, 0, 2n+6) -> (0, 1, n²+6n+9, 0, 2n+5)
  step fm
  -- Phase 5: R1+R2 chain x (2n+5)
  -- (0, 1, n²+6n+9, 0, 2n+5) ->* (2n+5, 1, n²+4n+4, 2n+5, 0)
  -- Note: n²+6n+9 = (n²+4n+4) + (2n+5) and 2n+5 = 0 + (2n+5)
  apply stepStar_trans (c₂ := ⟨2*n+5, 1, n*n+4*n+4, 2*n+5, 0⟩)
  · have h := r1r2_chain (2*n+5) 0 (n*n+4*n+4) 0
    simp only [(by ring : n * n + 4 * n + 4 + (2 * n + 5) = n * n + 6 * n + 9),
               (by ring : 0 + (2 * n + 5) = 2 * n + 5)] at h
    exact h
  -- Phase 6: Final R1 step
  -- (2n+5, 1, n²+4n+4, 2n+5, 0) -> (2n+7, 0, n²+4n+3, 2n+6, 0)
  -- Note: n²+4n+4 = (n²+4n+3)+1
  rw [show n * n + 4 * n + 4 = (n * n + 4 * n + 3) + 1 from by ring]
  step fm
  ring_nf; finish

theorem nonhalt : ¬halts fm c₀ := by
  -- Bootstrap: c₀ = (1,0,0,0,0) reaches C(0) = (5,0,0,4,0) in 20 steps
  apply stepStar_not_halts_not_halts (c₂ := ⟨5, 0, 0, 4, 0⟩) (by execute fm 20)
  apply progress_nonhalt_simple (fm := fm) (A := ℕ)
    (fun n ↦ ⟨2*n+5, 0, n*n+2*n, 2*n+4, 0⟩) 0
  intro n; exists n + 1
  show ⟨2*n+5, 0, n*n+2*n, 2*n+4, 0⟩ [fm]⊢⁺ ⟨2*(n+1)+5, 0, (n+1)*(n+1)+2*(n+1), 2*(n+1)+4, 0⟩
  simp only [(by ring : 2 * (n + 1) + 5 = 2 * n + 7),
             (by ring : (n + 1) * (n + 1) + 2 * (n + 1) = n * n + 4 * n + 3),
             (by ring : 2 * (n + 1) + 4 = 2 * n + 6)]
  exact main_trans n

end Sz22_2003_unofficial_492
