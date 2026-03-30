import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #963: [4/15, 33/14, 5/2, 7/11, 132/5]

Vector representation:
```
 2 -1 -1  0  0
-1  1  0 -1  1
-1  0  1  0  0
 0  0  0  1 -1
 2  1 -1  0  1
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_963

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a, b+1, c+1, d, e⟩ => some ⟨a+2, b, c, d, e⟩
  | ⟨a+1, b, c, d+1, e⟩ => some ⟨a, b+1, c, d, e+1⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b, c+1, d, e⟩
  | ⟨a, b, c, d, e+1⟩ => some ⟨a, b, c, d+1, e⟩
  | ⟨a, b, c+1, d, e⟩ => some ⟨a+2, b+1, c, d, e+1⟩
  | _ => none

-- R1R2 chain: k rounds of (R1, R2) from (a, 1, c+k, k, e)
-- Each round: R1 (b>=1,c>=1) then R2 (a>=1,d>=1)
-- Result: (a+k, 1, c, 0, e+k)
theorem r1r2_chain : ∀ k, ∀ a c e,
    ⟨a, 1, c + k, k, e⟩ [fm]⊢* ⟨a + k, 1, c, 0, e + k⟩ := by
  intro k; induction' k with k ih <;> intro a c e
  · ring_nf; finish
  · rw [show c + (k + 1) = (c + k) + 1 from by ring,
        show (k : ℕ) + 1 = k + 1 from rfl]
    step fm; step fm
    apply stepStar_trans (ih (a + 1) c (e + 1)); ring_nf; finish

-- R3 drain: (k, 0, c, 0, e) ⊢* (0, 0, c+k, 0, e)
theorem r3_drain : ∀ k, ∀ c e,
    ⟨k, 0, c, 0, e⟩ [fm]⊢* ⟨0, 0, c + k, 0, e⟩ := by
  intro k; induction' k with k ih <;> intro c e
  · ring_nf; finish
  · step fm; apply stepStar_trans (ih (c + 1) e); ring_nf; finish

-- R4 drain: (0, 0, c, d, k) ⊢* (0, 0, c, d+k, 0)
theorem r4_drain : ∀ k, ∀ c d,
    ⟨0, 0, c, d, k⟩ [fm]⊢* ⟨0, 0, c, d + k, 0⟩ := by
  intro k; induction' k with k ih <;> intro c d
  · ring_nf; finish
  · rw [show (k : ℕ) + 1 = k + 1 from rfl]
    step fm; apply stepStar_trans (ih c (d + 1)); ring_nf; finish

-- Main transition: (0, 0, 2n+3, n+1, 0) ⊢⁺ (0, 0, 2n+5, n+2, 0)
-- Canonical state parameterized by n: (0, 0, 2*(n+1)+1, n+1, 0) = (0, 0, 2n+3, n+1, 0)
-- for n >= 0, so the first canonical state is n=0 giving (0, 0, 3, 1, 0)
theorem main_trans (n : ℕ) :
    ⟨0, 0, 2 * n + 3, n + 1, 0⟩ [fm]⊢⁺
    ⟨0, 0, 2 * n + 5, n + 2, 0⟩ := by
  -- Phase 1: R5 step
  have h1 : ⟨0, 0, 2 * n + 3, n + 1, 0⟩ [fm]⊢⁺
      ⟨2, 1, 2 * n + 2, n + 1, 1⟩ := by
    rw [show 2 * n + 3 = (2 * n + 2) + 1 from by ring]
    apply step_stepPlus
    show fm ⟨0, 0, (2 * n + 2) + 1, n + 1, 0⟩ = some ⟨2, 1, 2 * n + 2, n + 1, 1⟩
    unfold fm; simp only
  -- Phase 2: R1R2 chain (n+1 rounds)
  have h2 : ⟨2, 1, 2 * n + 2, n + 1, 1⟩ [fm]⊢*
      ⟨n + 3, 1, n + 1, 0, n + 2⟩ := by
    have := r1r2_chain (n + 1) 2 (n + 1) 1
    rw [show (n + 1) + (n + 1) = 2 * n + 2 from by ring,
        show 2 + (n + 1) = n + 3 from by ring,
        show 1 + (n + 1) = n + 2 from by ring] at this
    exact this
  -- Phase 3: Final R1 (b=1, c=n+1 >= 1)
  have h3 : ⟨n + 3, 1, n + 1, 0, n + 2⟩ [fm]⊢*
      ⟨n + 5, 0, n, 0, n + 2⟩ := by
    rw [show n + 1 = n + 1 from rfl]
    step fm; finish
  -- Phase 4: R3 drain (a = n+5)
  have h4 : ⟨n + 5, 0, n, 0, n + 2⟩ [fm]⊢*
      ⟨0, 0, 2 * n + 5, 0, n + 2⟩ := by
    have := r3_drain (n + 5) n (n + 2)
    rw [show n + (n + 5) = 2 * n + 5 from by ring] at this
    exact this
  -- Phase 5: R4 drain (e = n+2)
  have h5 : ⟨0, 0, 2 * n + 5, 0, n + 2⟩ [fm]⊢*
      ⟨0, 0, 2 * n + 5, n + 2, 0⟩ := by
    have := r4_drain (n + 2) (2 * n + 5) 0
    rw [show 0 + (n + 2) = n + 2 from by ring] at this
    exact this
  -- Compose all phases
  exact stepPlus_stepStar_stepPlus h1
    (stepStar_trans h2 (stepStar_trans h3 (stepStar_trans h4 h5)))

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨0, 0, 3, 1, 0⟩) (by execute fm 8)
  apply progress_nonhalt_simple (fm := fm) (A := ℕ)
    (fun n ↦ ⟨0, 0, 2 * n + 3, n + 1, 0⟩) 0
  intro n
  refine ⟨n + 1, ?_⟩
  show ⟨0, 0, 2 * n + 3, n + 1, 0⟩ [fm]⊢⁺
    ⟨0, 0, 2 * (n + 1) + 3, (n + 1) + 1, 0⟩
  rw [show 2 * (n + 1) + 3 = 2 * n + 5 from by ring,
      show (n + 1) + 1 = n + 2 from by ring]
  exact main_trans n
