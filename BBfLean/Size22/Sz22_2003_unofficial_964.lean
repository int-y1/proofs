import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #964: [4/15, 33/14, 5/2, 7/11, 198/5]

Vector representation:
```
 2 -1 -1  0  0
-1  1  0 -1  1
-1  0  1  0  0
 0  0  0  1 -1
 1  2 -1  0  1
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_964

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a, b+1, c+1, d, e⟩ => some ⟨a+2, b, c, d, e⟩
  | ⟨a+1, b, c, d+1, e⟩ => some ⟨a, b+1, c, d, e+1⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b, c+1, d, e⟩
  | ⟨a, b, c, d, e+1⟩ => some ⟨a, b, c, d+1, e⟩
  | ⟨a, b, c+1, d, e⟩ => some ⟨a+1, b+2, c, d, e+1⟩
  | _ => none

-- R2R1 chain: k rounds of (R2, R1)
-- Each round: R2 (a+1,0,c+1,d+1,e) -> (a,1,c+1,d,e+1), R1 -> (a+2,0,c,d,e+1)
-- Net per round: a+1, c-1, d-1, e+1
theorem r2r1_chain : ∀ k, ∀ a c e,
    ⟨a + 1, 0, c + k, k, e⟩ [fm]⊢* ⟨a + k + 1, 0, c, 0, e + k⟩ := by
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

-- Main transition: (0, 0, 2n+5, 0, n+2) ⊢⁺ (0, 0, 2n+7, 0, n+3)
theorem main_trans (n : ℕ) :
    ⟨0, 0, 2 * n + 5, 0, n + 2⟩ [fm]⊢⁺
    ⟨0, 0, 2 * n + 7, 0, n + 3⟩ := by
  -- Phase 1: R4 drain e to d
  have h1 : ⟨0, 0, 2 * n + 5, 0, n + 2⟩ [fm]⊢*
      ⟨0, 0, 2 * n + 5, n + 2, 0⟩ := by
    have := r4_drain (n + 2) (2 * n + 5) 0
    rw [show 0 + (n + 2) = n + 2 from by ring] at this
    exact this
  -- Phase 2: R5 step
  have h2 : ⟨0, 0, 2 * n + 5, n + 2, 0⟩ [fm]⊢⁺
      ⟨1, 2, 2 * n + 4, n + 2, 1⟩ := by
    rw [show 2 * n + 5 = (2 * n + 4) + 1 from by ring]
    apply step_stepPlus
    show fm ⟨0, 0, (2 * n + 4) + 1, n + 2, 0⟩ = some ⟨1, 2, 2 * n + 4, n + 2, 1⟩
    unfold fm; simp only
  -- Phase 3: Two R1 steps (b goes 2 -> 1 -> 0)
  have h3 : ⟨1, 2, 2 * n + 4, n + 2, 1⟩ [fm]⊢*
      ⟨5, 0, 2 * n + 2, n + 2, 1⟩ := by
    rw [show 2 * n + 4 = (2 * n + 3) + 1 from by ring,
        show (2 : ℕ) = 1 + 1 from rfl]
    step fm
    rw [show 2 * n + 3 = (2 * n + 2) + 1 from by ring]
    step fm; finish
  -- Phase 4: R2R1 chain (n+2 rounds)
  have h4 : ⟨5, 0, 2 * n + 2, n + 2, 1⟩ [fm]⊢*
      ⟨n + 7, 0, n, 0, n + 3⟩ := by
    have := r2r1_chain (n + 2) 4 n 1
    rw [show 4 + 1 = 5 from by ring,
        show n + (n + 2) = 2 * n + 2 from by ring,
        show 4 + (n + 2) + 1 = n + 7 from by ring,
        show 1 + (n + 2) = n + 3 from by ring] at this
    exact this
  -- Phase 5: R3 drain
  have h5 : ⟨n + 7, 0, n, 0, n + 3⟩ [fm]⊢*
      ⟨0, 0, 2 * n + 7, 0, n + 3⟩ := by
    have := r3_drain (n + 7) n (n + 3)
    rw [show n + (n + 7) = 2 * n + 7 from by ring] at this
    exact this
  -- Compose all phases
  exact stepStar_stepPlus_stepPlus h1
    (stepPlus_stepStar_stepPlus h2
      (stepStar_trans h3 (stepStar_trans h4 h5)))

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨0, 0, 5, 0, 2⟩) (by execute fm 21)
  apply progress_nonhalt_simple (fm := fm) (A := ℕ)
    (fun n ↦ ⟨0, 0, 2 * n + 5, 0, n + 2⟩) 0
  intro n
  refine ⟨n + 1, ?_⟩
  show ⟨0, 0, 2 * n + 5, 0, n + 2⟩ [fm]⊢⁺
    ⟨0, 0, 2 * (n + 1) + 5, 0, (n + 1) + 2⟩
  rw [show 2 * (n + 1) + 5 = 2 * n + 7 from by ring,
      show (n + 1) + 2 = n + 3 from by ring]
  exact main_trans n
