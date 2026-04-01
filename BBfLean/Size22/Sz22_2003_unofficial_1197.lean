import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #1197: [5/6, 49/3, 99/35, 4/11, 15/2]

Vector representation:
```
-1 -1  1  0  0
 0 -1  0  2  0
 0  2 -1 -1  1
 2  0  0  0 -1
-1  1  1  0  0
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_1197

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a+1, b+1, c, d, e⟩ => some ⟨a, b, c+1, d, e⟩
  | ⟨a, b+1, c, d, e⟩ => some ⟨a, b, c, d+2, e⟩
  | ⟨a, b, c+1, d+1, e⟩ => some ⟨a, b+2, c, d, e+1⟩
  | ⟨a, b, c, d, e+1⟩ => some ⟨a+2, b, c, d, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b+1, c+1, d, e⟩
  | _ => none

-- R4 chain: convert e to a.
theorem r4_chain : ∀ k, ⟨a, 0, 0, d, e + k⟩ [fm]⊢* ⟨a + 2 * k, 0, 0, d, e⟩ := by
  intro k; induction' k with k ih generalizing a e
  · exists 0
  · rw [show e + (k + 1) = e + k + 1 from by ring]
    step fm
    apply stepStar_trans (ih (a := a + 2) (e := e))
    ring_nf; finish

-- Phase 2: R3,R1,R1 chain.
theorem r3r1r1_chain : ∀ k, ∀ a c d e,
    (⟨2 * k + a, 0, c + 1, (d + k) + 1, e⟩ : Q) [fm]⊢* ⟨a, 0, (c + k) + 1, d + 1, e + k⟩ := by
  intro k; induction' k with k ih <;> intro a c d e
  · rw [show 2 * 0 + a = a from by ring,
        show e + 0 = e from by ring]
    exists 0
  · rw [show 2 * (k + 1) + a = (2 * k + a + 1) + 1 from by ring,
        show (d + (k + 1)) + 1 = ((d + k) + 1) + 1 from by ring]
    step fm  -- R3
    step fm  -- R1
    step fm  -- R1
    rw [show (d + k) + 1 = (d + k) + 1 from rfl]
    apply stepStar_trans (ih a (c + 1) d (e + 1))
    ring_nf; finish

-- Phase 3: R3,R2,R2 chain.
theorem r3r2r2_chain : ∀ k, ∀ c d e,
    (⟨0, 0, c + k, d + 1, e⟩ : Q) [fm]⊢* ⟨0, 0, c, d + 3 * k + 1, e + k⟩ := by
  intro k; induction' k with k ih <;> intro c d e
  · exists 0
  · rw [show c + (k + 1) = (c + k) + 1 from by ring]
    step fm  -- R3
    step fm  -- R2
    step fm  -- R2
    rw [show d + 2 + 2 = (d + 3) + 1 from by ring]
    apply stepStar_trans (ih c (d + 3) (e + 1))
    ring_nf; finish

-- Main transition
theorem main_transition (N D : ℕ) :
    (⟨2 * (N + 1), 0, 0, D + N + 1, 0⟩ : Q) [fm]⊢⁺ ⟨2 * (2 * N + 2), 0, 0, D + 3 * N + 7, 0⟩ := by
  rw [show 2 * (N + 1) = (2 * N + 1) + 1 from by ring]
  step fm  -- R5
  step fm  -- R1
  -- Now at: (2*N, 0, 2, D+N+1, 0)
  -- Phase 2: need (2*N+0, 0, 1+1, (D+N)+1, 0) form
  -- = (2*N, 0, c+1, (d+N)+1, 0) with c=1, d=D
  -- (2*N, 0, 2, D+N+1, 0) - need to match r3r1r1_chain form
  -- r3r1r1_chain N 0 1 D 0: (2*N+0, 0, 1+1, (D+N)+1, 0) ⊢* (0, 0, (1+N)+1, D+1, 0+N)
  rw [show D + N + 1 = (D + N) + 1 from by ring]
  apply stepStar_trans (r3r1r1_chain N 0 1 D 0)
  -- After: (0, 0, (1+N)+1, D+1, 0+N)
  rw [show 1 + N + 1 = 0 + (N + 2) from by ring,
      show 0 + N = N from by ring]
  apply stepStar_trans (r3r2r2_chain (N + 2) 0 D N)
  -- After: (0, 0, 0, D+3*(N+2)+1, N+(N+2))
  rw [show D + 3 * (N + 2) + 1 = D + 3 * N + 7 from by ring,
      show N + (N + 2) = 0 + (2 * N + 2) from by ring]
  apply stepStar_trans (r4_chain (2 * N + 2) (a := 0) (d := D + 3 * N + 7) (e := 0))
  ring_nf; finish

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := (⟨2, 0, 0, 5, 0⟩ : Q))
  · execute fm 6
  apply progress_nonhalt (fm := fm)
    (P := fun q ↦ ∃ N D, q = ⟨2 * (N + 1), 0, 0, D + N + 1, 0⟩)
  · intro c ⟨N, D, hq⟩; subst hq
    exact ⟨⟨2 * (2 * N + 2), 0, 0, D + 3 * N + 7, 0⟩,
      ⟨2 * N + 1, D + N + 5, by ring_nf⟩, main_transition N D⟩
  · exact ⟨0, 4, by ring_nf⟩
