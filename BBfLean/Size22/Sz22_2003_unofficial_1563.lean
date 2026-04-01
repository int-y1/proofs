import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #1563: [7/45, 22/5, 275/14, 3/11, 35/2]

Vector representation:
```
 0 -2 -1  1  0
 1  0 -1  0  1
-1  0  2 -1  1
 0  1  0  0 -1
-1  0  1  1  0
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_1563

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a, b+2, c+1, d, e⟩ => some ⟨a, b, c, d+1, e⟩
  | ⟨a, b, c+1, d, e⟩ => some ⟨a+1, b, c, d, e+1⟩
  | ⟨a+1, b, c, d+1, e⟩ => some ⟨a, b, c+2, d, e+1⟩
  | ⟨a, b, c, d, e+1⟩ => some ⟨a, b+1, c, d, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b, c+1, d+1, e⟩
  | _ => none

-- R4: transfer e to b
theorem e_to_b : ∀ k b, ⟨a, b, 0, 0, e + k⟩ [fm]⊢* ⟨a, b + k, 0, 0, e⟩ := by
  intro k; induction' k with k ih
  · intro b; exists 0
  · intro b; rw [Nat.add_succ]; step fm
    apply stepStar_trans (ih (b + 1)); ring_nf; finish

-- Middle drain: (j+1, 4j+2, 0, d+2, e) ⊢* (0, 0, 1, d+j+2, e+j+1)
theorem middle_drain : ∀ j, ∀ d e, ⟨j + 1, 4 * j + 2, 0, d + 2, e⟩ [fm]⊢*
    ⟨0, 0, 1, d + j + 2, e + j + 1⟩ := by
  intro j; induction' j with j ih
  · intro d e; step fm; step fm; ring_nf; finish
  · intro d e
    rw [show j + 1 + 1 = (j + 1) + 1 from by ring,
        show 4 * (j + 1) + 2 = (4 * j + 4) + 2 from by ring,
        show d + 2 = (d + 1) + 1 from by ring]
    step fm
    rw [show (4 * j + 4 + 2 : ℕ) = (4 * j + 4) + 2 from by ring]
    step fm
    rw [show (4 * j + 4 : ℕ) = (4 * j + 2) + 2 from by ring]
    step fm
    rw [show d + 1 + 1 + 1 = (d + 1) + 2 from by ring]
    apply stepStar_trans (ih (d + 1) (e + 1))
    rw [show d + 1 + j + 2 = d + (j + 1) + 2 from by ring,
        show e + 1 + j + 1 = e + (j + 1) + 1 from by ring]; finish

-- R2R2R3 chain: (a, 0, 2, k+1, e) ⊢* (a+k+1, 0, 2, 0, e+3k+3)
theorem r2r2r3_chain : ∀ k, ∀ a e, ⟨a, 0, 2, k + 1, e⟩ [fm]⊢*
    ⟨a + k + 1, 0, 2, 0, e + 3 * k + 3⟩ := by
  intro k; induction' k with k ih
  · intro a e; step fm; step fm; step fm; ring_nf; finish
  · intro a e
    rw [show k + 1 + 1 = (k + 1) + 1 from by ring]
    step fm; step fm; step fm
    apply stepStar_trans (ih (a + 1) (e + 3))
    ring_nf; finish

-- All phases after e_to_b: (n+1, 4n+2, 0, 2, 0) ⊢* (n+3, 0, 0, 0, 4n+8)
theorem rest_phases (n : ℕ) :
    ⟨n + 1, 4 * n + 2, 0, 2, 0⟩ [fm]⊢* ⟨n + 3, 0, 0, 0, 4 * n + 8⟩ := by
  -- middle_drain
  rw [show (2 : ℕ) = 0 + 2 from by ring]
  apply stepStar_trans (middle_drain n 0 0)
  rw [show 0 + n + 2 = n + 2 from by ring,
      show 0 + n + 1 = n + 1 from by ring]
  -- R2
  step fm
  -- R3
  step fm
  -- r2r2r3_chain
  rw [show n + 2 = (n + 1) + 1 from by ring]
  apply stepStar_trans (r2r2r3_chain n 0 (n + 3))
  ring_nf
  -- final R2R2
  step fm; step fm; ring_nf; finish

-- Main transition: (n+2, 0, 0, 0, 4n+4) ⊢⁺ (n+3, 0, 0, 0, 4n+8)
theorem main_trans (n : ℕ) :
    ⟨n + 2, 0, 0, 0, 4 * n + 4⟩ [fm]⊢⁺ ⟨n + 3, 0, 0, 0, 4 * n + 8⟩ := by
  -- Phase 1: e_to_b
  rw [show (0 : ℕ) = 0 + 0 from by ring,
      show 4 * n + 4 = 0 + (4 * n + 4) from by ring]
  apply stepStar_stepPlus_stepPlus (e_to_b (4 * n + 4) 0 (a := n + 2) (e := 0))
  rw [show 0 + (4 * n + 4) = 4 * n + 4 from by ring]
  -- Phase 2: R5
  rw [show n + 2 = (n + 1) + 1 from by ring]
  step fm
  -- Phase 3: R1
  rw [show 4 * n + 4 = (4 * n + 2) + 2 from by ring]
  step fm
  exact rest_phases n

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨2, 0, 0, 0, 4⟩) (by execute fm 5)
  apply progress_nonhalt_simple (fm := fm) (A := ℕ)
    (fun n ↦ ⟨n + 2, 0, 0, 0, 4 * n + 4⟩) 0
  intro n; exact ⟨n + 1, main_trans n⟩

end Sz22_2003_unofficial_1563
