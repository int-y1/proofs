import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #412: [25/63, 1/605, 18/5, 11/3, 35/2]

Vector representation:
```
 0 -2  2 -1  0
 0  0 -1  0 -2
 1  2 -1  0  0
 0 -1  0  0  1
-1  0  1  1  0
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_412

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a, b+2, c, d+1, e⟩ => some ⟨a, b, c+2, d, e⟩
  | ⟨a, b, c+1, d, e+2⟩ => some ⟨a, b, c, d, e⟩
  | ⟨a, b, c+1, d, e⟩ => some ⟨a+1, b+2, c, d, e⟩
  | ⟨a, b+1, c, d, e⟩ => some ⟨a, b, c, d, e+1⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b, c+1, d+1, e⟩
  | _ => none

-- R5/R2 pairs: consume a and e, build d
theorem r5r2_chain : ∀ k, ∀ a d e,
    ⟨a+k, 0, 0, d, e+2*k⟩ [fm]⊢* ⟨a, 0, 0, d+k, e⟩ := by
  intro k; induction k with
  | zero => intro a d e; exists 0
  | succ k ih =>
    intro a d e
    rw [show a + (k + 1) = (a + k) + 1 from by ring,
        show e + 2 * (k + 1) = (e + 2 * k) + 2 from by ring]
    step fm; step fm
    apply stepStar_trans (ih _ _ _)
    ring_nf; finish

-- Interleaved R1 and R3 steps
theorem r1r3_chain : ∀ k, ∀ a c,
    ⟨a, 2, c, k+1, 0⟩ [fm]⊢* ⟨a+k, 0, c+k+2, 0, 0⟩ := by
  intro k; induction k with
  | zero => intro a c; step fm; ring_nf; finish
  | succ k ih =>
    intro a c
    rw [show k + 1 + 1 = (k + 1) + 1 from by ring]
    step fm; step fm
    apply stepStar_trans (ih _ _)
    ring_nf; finish

-- R3 chain: consume c, build a and b
theorem r3_chain : ∀ k, ∀ a b,
    ⟨a, b, k, 0, 0⟩ [fm]⊢* ⟨a+k, b+2*k, 0, 0, 0⟩ := by
  intro k; induction k with
  | zero => intro a b; exists 0
  | succ k ih =>
    intro a b
    step fm
    apply stepStar_trans (ih _ _)
    ring_nf; finish

-- R4 chain: convert b to e
theorem r4_chain : ∀ k, ∀ a e,
    ⟨a, k, 0, 0, e⟩ [fm]⊢* ⟨a, 0, 0, 0, e+k⟩ := by
  intro k; induction k with
  | zero => intro a e; exists 0
  | succ k ih =>
    intro a e
    step fm
    apply stepStar_trans (ih _ _)
    ring_nf; finish

-- Main transition: C(m,n) = (m+2n+1, 0, 0, 0, 4n) ⊢⁺ C(m+2n, n+1)
theorem main_trans (m n : ℕ) :
    ⟨m+2*n+1, 0, 0, 0, 4*n⟩ [fm]⊢⁺ ⟨m+2*n+(2*(n+1))+1, 0, 0, 0, 4*(n+1)⟩ := by
  -- Phase A1: 2n R5/R2 pairs
  -- (m+2n+1, 0, 0, 0, 4n) ->* (m+1, 0, 0, 2n, 0)
  apply stepStar_stepPlus_stepPlus
  · have h := r5r2_chain (2*n) (m+1) 0 0
    rw [show m + 1 + 2 * n = m + 2 * n + 1 from by ring,
        show 0 + 2 * (2 * n) = 4 * n from by ring,
        show 0 + 2 * n = 2 * n from by ring] at h
    exact h
  -- Phase A2+A3: R5 then R3
  -- (m+1, 0, 0, 2n, 0) -> (m, 0, 1, 2n+1, 0) -> (m+1, 2, 0, 2n+1, 0)
  apply step_stepStar_stepPlus
  · show fm ⟨m + 1, 0, 0, 2 * n, 0⟩ = some ⟨m, 0, 1, 2 * n + 1, 0⟩; rfl
  apply stepStar_trans
  · show ⟨m, 0, 1, 2 * n + 1, 0⟩ [fm]⊢* ⟨m + 1, 2, 0, 2 * n + 1, 0⟩
    step fm; finish
  -- Phase B: r1r3_chain with k = 2n
  -- (m+1, 2, 0, 2n+1, 0) ->* (m+2n+1, 0, 2n+2, 0, 0)
  apply stepStar_trans
  · have h := r1r3_chain (2*n) (m+1) 0
    rw [show 2 * n + 1 = 2 * n + 1 from rfl,
        show m + 1 + 2 * n = m + 2 * n + 1 from by ring,
        show 0 + 2 * n + 2 = 2 * n + 2 from by ring] at h
    exact h
  -- Phase C: R3 chain consuming 2n+2
  -- (m+2n+1, 0, 2n+2, 0, 0) ->* (m+4n+3, 4n+4, 0, 0, 0)
  apply stepStar_trans
  · have h := r3_chain (2*n+2) (m+2*n+1) 0
    rw [show m + 2 * n + 1 + (2 * n + 2) = m + 4 * n + 3 from by ring,
        show 0 + 2 * (2 * n + 2) = 4 * n + 4 from by ring] at h
    exact h
  -- Phase D: R4 chain converting b to e
  -- (m+4n+3, 4n+4, 0, 0, 0) ->* (m+4n+3, 0, 0, 0, 4n+4)
  rw [show m + 4 * n + 3 = m + 2 * n + (2 * (n + 1)) + 1 from by ring,
      show (4 : ℕ) * n + 4 = 4 * (n + 1) from by ring]
  have h := r4_chain (4*(n+1)) (m+2*n+(2*(n+1))+1) 0
  simp only [Nat.zero_add] at h
  exact h

theorem nonhalt : ¬halts fm c₀ := by
  show ¬halts fm ⟨1, 0, 0, 0, 0⟩
  apply progress_nonhalt_simple (fm := fm) (A := ℕ × ℕ)
    (fun ⟨m, n⟩ ↦ ⟨m+2*n+1, 0, 0, 0, 4*n⟩) ⟨0, 0⟩
  intro ⟨m, n⟩
  exact ⟨⟨m+2*n, n+1⟩, main_trans m n⟩

end Sz22_2003_unofficial_412
