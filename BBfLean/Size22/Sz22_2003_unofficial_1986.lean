import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #1986: [99/35, 4/5, 5/6, 7/11, 175/2]

Vector representation:
```
 0  2 -1 -1  1
 2  0 -1  0  0
-1 -1  1  0  0
 0  0  0  1 -1
-1  0  2  1  0
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_1986

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a, b, c+1, d+1, e⟩ => some ⟨a, b+2, c, d, e+1⟩
  | ⟨a, b, c+1, d, e⟩ => some ⟨a+2, b, c, d, e⟩
  | ⟨a+1, b+1, c, d, e⟩ => some ⟨a, b, c+1, d, e⟩
  | ⟨a, b, c, d, e+1⟩ => some ⟨a, b, c, d+1, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b, c+2, d+1, e⟩
  | _ => none

-- R3+R1 chain: k rounds
theorem r3r1_chain : ∀ k, ∀ a b d e,
    ⟨a + 1 + k, b + 1, 0, d + k, e⟩ [fm]⊢* ⟨a + 1, b + 1 + k, 0, d, e + k⟩ := by
  intro k; induction' k with k ih <;> intro a b d e
  · exists 0
  · rw [show a + 1 + (k + 1) = (a + 1 + k) + 1 from by omega,
        show d + (k + 1) = (d + k) + 1 from by omega]
    step fm
    step fm
    rw [show b + 2 = (b + 1) + 1 from by omega]
    apply stepStar_trans (ih a (b + 1) d (e + 1))
    ring_nf; finish

-- R3+R2 drain
theorem r3r2_drain : ∀ k, ∀ a b e,
    ⟨a + 1, b + k, 0, 0, e⟩ [fm]⊢* ⟨a + 1 + k, b, 0, 0, e⟩ := by
  intro k; induction' k with k ih <;> intro a b e
  · exists 0
  · rw [show b + (k + 1) = (b + k) + 1 from by omega]
    step fm
    step fm
    rw [show a + 2 = (a + 1) + 1 from by omega]
    apply stepStar_trans (ih (a + 1) b e)
    ring_nf; finish

-- R4 chain
theorem r4_chain : ∀ k, ∀ a d,
    ⟨a, 0, 0, d, k⟩ [fm]⊢* ⟨a, 0, 0, d + k, 0⟩ := by
  intro k; induction' k with k ih <;> intro a d
  · exists 0
  · step fm
    apply stepStar_trans (ih a (d + 1))
    ring_nf; finish

-- Composed transition from (3n+3, 4, 0, n, 2) to (3n+7, 0, 0, n+2, 0)
theorem phases (n : ℕ) :
    ⟨3 * n + 3, 4, 0, n, 2⟩ [fm]⊢* ⟨3 * n + 7, 0, 0, n + 2, 0⟩ := by
  -- Phase 1: R3+R1 chain, n rounds
  -- (3n+3, 4, 0, n, 2) = ((2n+2)+1+n, 3+1, 0, 0+n, 2) →* ((2n+2)+1, 3+1+n, 0, 0, 2+n)
  have h1 := r3r1_chain n (2 * n + 2) 3 0 2
  rw [show (2 * n + 2) + 1 + n = 3 * n + 3 from by omega,
      show 3 + 1 = 4 from by omega,
      show 0 + n = n from by omega] at h1
  apply stepStar_trans h1
  -- Now at ((2n+2)+1, 3+1+n, 0, 0, 2+n) = (2n+3, n+4, 0, 0, n+2)
  -- Phase 2: R3+R2 drain, n+4 rounds
  have h2 := r3r2_drain (n + 4) (2 * n + 2) 0 (n + 2)
  rw [show 0 + (n + 4) = n + 4 from by omega,
      show (2 * n + 2) + 1 = 2 * n + 3 from by omega] at h2
  -- h2 uses (2n+3, n+4, 0, 0, n+2) but goal has ((2n+2)+1, 3+1+n, 0, 0, 2+n)
  rw [show (2 * n + 2) + 1 = 2 * n + 3 from by omega,
      show 3 + 1 + n = n + 4 from by omega,
      show 2 + n = n + 2 from by omega]
  apply stepStar_trans h2
  -- Now at (3n+7, 0, 0, 0, n+2)
  rw [show (2 * n + 2) + 1 + (n + 4) = 3 * n + 7 from by omega] at *
  -- Phase 3: R4 chain, n+2 steps
  have h3 := r4_chain (n + 2) (3 * n + 7) 0
  rw [show 0 + (n + 2) = n + 2 from by omega] at h3
  exact h3

-- Main transition
theorem main_trans (n : ℕ) :
    ⟨3 * n + 4, 0, 0, n + 1, 0⟩ [fm]⊢⁺ ⟨3 * n + 7, 0, 0, n + 2, 0⟩ := by
  -- R5: (3n+4, 0, 0, n+1, 0) -> (3n+3, 0, 2, n+2, 0)
  step fm
  -- Two R1: (3n+3, 0, 2, n+2, 0) -> (3n+3, 4, 0, n, 2)
  rw [show n + 1 + 1 = n + 2 from by omega]
  step fm
  step fm
  exact phases n

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨4, 0, 0, 1, 0⟩) (by execute fm 8)
  apply progress_nonhalt_simple (fm := fm) (A := ℕ)
    (fun n ↦ ⟨3 * n + 4, 0, 0, n + 1, 0⟩) 0
  intro n; exists n + 1
  show ⟨3 * n + 4, 0, 0, n + 1, 0⟩ [fm]⊢⁺ ⟨3 * (n + 1) + 4, 0, 0, (n + 1) + 1, 0⟩
  rw [show 3 * (n + 1) + 4 = 3 * n + 7 from by ring,
      show (n + 1) + 1 = n + 2 from by ring]
  exact main_trans n

end Sz22_2003_unofficial_1986
