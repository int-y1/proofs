import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #518: [28/15, 3/22, 65/2, 143/7, 33/13]

Vector representation:
```
 2 -1 -1  1  0  0
-1  1  0  0 -1  0
-1  0  1  0  0  1
 0  0  0 -1  1  1
 0  1  0  0  1 -1
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_518

def Q := ℕ × ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a, b+1, c+1, d, e, f⟩ => some ⟨a+2, b, c, d+1, e, f⟩
  | ⟨a+1, b, c, d, e+1, f⟩ => some ⟨a, b+1, c, d, e, f⟩
  | ⟨a+1, b, c, d, e, f⟩ => some ⟨a, b, c+1, d, e, f+1⟩
  | ⟨a, b, c, d+1, e, f⟩ => some ⟨a, b, c, d, e+1, f+1⟩
  | ⟨a, b, c, d, e, f+1⟩ => some ⟨a, b+1, c, d, e+1, f⟩
  | _ => none

-- R3 repeated: (a+k, 0, c, d, 0, f) →* (a, 0, c+k, d, 0, f+k)
theorem r3_chain : ∀ k, ∀ a c d f, (⟨a+k, 0, c, d, 0, f⟩ : Q) [fm]⊢* ⟨a, 0, c+k, d, 0, f+k⟩ := by
  intro k; induction' k with k ih <;> intro a c d f
  · exists 0
  rw [show a + (k+1) = (a+k) + 1 from by ring]
  step fm
  apply stepStar_trans (ih _ _ _ _)
  ring_nf; finish

-- R4 repeated: (0, 0, c, d+k, e, f) →* (0, 0, c, d, e+k, f+k)
theorem r4_chain : ∀ k, ∀ c d e f, (⟨0, 0, c, d+k, e, f⟩ : Q) [fm]⊢* ⟨0, 0, c, d, e+k, f+k⟩ := by
  intro k; induction' k with k ih <;> intro c d e f
  · exists 0
  rw [show d + (k+1) = (d+k) + 1 from by ring]
  step fm
  apply stepStar_trans (ih _ _ _ _)
  ring_nf; finish

-- R1R2 chain: (K, 1, C+1, K, E+C, F) →* (K+C+2, 0, 0, K+C+1, E, F)
theorem r1r2_phase : ∀ C, ∀ K E F, (⟨K, 1, C+1, K, E+C, F⟩ : Q) [fm]⊢* ⟨K+C+2, 0, 0, K+C+1, E, F⟩ := by
  intro C; induction' C with C ih <;> intro K E F
  · step fm; finish
  rw [show E + (C + 1) = (E + C) + 1 from by ring]
  step fm; step fm
  apply stepStar_trans (ih (K+1) E F)
  ring_nf; finish

-- R2 drain: (a+k, b, 0, d, k, f) →* (a, b+k, 0, d, 0, f)
theorem r2_drain : ∀ k, ∀ a b d f, (⟨a+k, b, 0, d, k, f⟩ : Q) [fm]⊢* ⟨a, b+k, 0, d, 0, f⟩ := by
  intro k; induction' k with k ih <;> intro a b d f
  · exists 0
  rw [show a + (k+1) = (a+k) + 1 from by ring]
  step fm
  apply stepStar_trans (ih _ _ _ _)
  ring_nf; finish

-- R3R1 interleaved: (A+1, B+K, 0, D, 0, F) →* (A+1+K, B, 0, D+K, 0, F+K)
theorem r3r1_chain : ∀ K, ∀ A B D F, (⟨A+1, B+K, 0, D, 0, F⟩ : Q) [fm]⊢* ⟨A+1+K, B, 0, D+K, 0, F+K⟩ := by
  intro K; induction' K with K ih <;> intro A B D F
  · exists 0
  rw [show B + (K+1) = (B+K) + 1 from by ring]
  step fm; step fm
  apply stepStar_trans (ih _ _ _ _)
  ring_nf; finish

-- Combined phases 1-3: drain a and d, do R5
-- (n+2, 0, 0, 2*(n+1), 0, F) →* (0, 1, n+2, 0, 2*n+3, F+3*n+3)
theorem phases_123 (n F : ℕ) :
    (⟨n+2, 0, 0, 2*(n+1), 0, F⟩ : Q) [fm]⊢* ⟨0, 1, n+2, 0, 2*n+3, F+3*n+3⟩ := by
  -- Phase 1: R3 chain
  rw [show n + 2 = 0 + (n + 2) from by ring]
  apply stepStar_trans (r3_chain (n+2) 0 0 (2*(n+1)) F)
  -- Phase 2: R4 chain
  rw [show 2 * (n + 1) = 0 + (2 * (n + 1)) from by ring]
  apply stepStar_trans (r4_chain (2*(n+1)) (0+(n+2)) 0 0 (F+(n+2)))
  -- Phase 3: R5 step
  rw [show F + (n + 2) + 2 * (n + 1) = (F + 3 * n + 3) + 1 from by ring,
      show 2 * (n + 1) = (2 * n + 2) + 0 from by ring]
  apply stepStar_trans (step_stepStar (by unfold fm; simp; ring_nf; rfl))
  ring_nf; finish

-- Combined phases 4-6: R1R2 chain, R2 drain, R3R1 chain
-- (0, 1, n+2, 0, 2*n+3, G) →⁺ (n+3, 0, 0, 2*(n+2), 0, G+n+2)
theorem phases_456 (n G : ℕ) :
    (⟨0, 1, n+2, 0, 2*n+3, G⟩ : Q) [fm]⊢⁺ ⟨n+3, 0, 0, 2*(n+2), 0, G+n+2⟩ := by
  -- Phase 4: first R1 step then rest as ⊢*
  rw [show n + 2 = (n+1) + 1 from by ring,
      show 2 * n + 3 = (n+2) + (n+1) from by ring]
  -- Take one R1 step to establish ⊢⁺
  step fm
  -- Now need: (2, 0, n+1, 1, (n+2)+(n+1), G) →* target
  -- Continue R1R2 phase (minus the first R1) via R2 then r1r2_phase
  step fm
  -- After R2: (1, 1, n+1, 1, n+2+(n+1)-1, G) = (1, 1, n+1, 1, (n+2)+n, G)
  -- Use r1r2_phase with K=1, C=n, E=n+2
  apply stepStar_trans (r1r2_phase n 1 (n+2) G)
  -- State: (1+n+2, 0, 0, 1+n+1, n+2, G) = (n+3, 0, 0, n+2, n+2, G)
  -- Phase 5: R2 drain
  rw [show 1 + n + 2 = 1 + (n+2) from by ring,
      show 1 + n + 1 = n + 2 from by ring]
  apply stepStar_trans (r2_drain (n+2) 1 0 (n+2) G)
  -- State: (1, n+2, 0, n+2, 0, G)
  -- Phase 6: R3R1 chain
  rw [show (1 : ℕ) = 0 + 1 from by ring,
      show 0 + (n+2) = 0 + (n+2) from rfl]
  apply stepStar_trans (r3r1_chain (n+2) 0 0 (n+2) G)
  rw [show 0 + 1 + (n+2) = n + 3 from by ring,
      show n+2+(n+2) = 2*(n+2) from by ring]
  finish

-- Main transition: C(n) →⁺ C(n+1)
theorem main_transition (n : ℕ) :
    (⟨n+2, 0, 0, 2*(n+1), 0, (n+1)*(2*n+1)⟩ : Q) [fm]⊢⁺
    ⟨n+3, 0, 0, 2*(n+2), 0, (n+2)*(2*n+3)⟩ := by
  apply stepStar_stepPlus_stepPlus (phases_123 n ((n+1)*(2*n+1)))
  have : (n+2)*(2*n+3) = (n+1)*(2*n+1) + 3*n + 3 + (n+2) := by ring
  rw [this]
  exact phases_456 n ((n+1)*(2*n+1) + 3*n + 3)

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨2, 0, 0, 2, 0, 1⟩)
  · execute fm 6
  apply progress_nonhalt_simple (fm := fm) (A := ℕ)
    (fun n ↦ ⟨n+2, 0, 0, 2*(n+1), 0, (n+1)*(2*n+1)⟩) 0
  intro n; exists n+1
  exact main_transition n

end Sz22_2003_unofficial_518
