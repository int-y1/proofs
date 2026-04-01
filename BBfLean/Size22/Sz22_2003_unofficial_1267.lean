import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #1267: [5/6, 99/35, 4/5, 7/11, 175/2]

Vector representation:
```
-1 -1  1  0  0
 0  2 -1 -1  1
 2  0 -1  0  0
 0  0  0  1 -1
-1  0  2  1  0
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_1267

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a+1, b+1, c, d, e⟩ => some ⟨a, b, c+1, d, e⟩
  | ⟨a, b, c+1, d+1, e⟩ => some ⟨a, b+2, c, d, e+1⟩
  | ⟨a, b, c+1, d, e⟩ => some ⟨a+2, b, c, d, e⟩
  | ⟨a, b, c, d, e+1⟩ => some ⟨a, b, c, d+1, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b, c+2, d+1, e⟩
  | _ => none

-- R4 chain: move e to d.
theorem e_to_d : ∀ k d e, ⟨a, (0 : ℕ), (0 : ℕ), d, e + k⟩ [fm]⊢* ⟨a, (0 : ℕ), (0 : ℕ), d + k, e⟩ := by
  intro k; induction' k with k ih
  · intro d e; exists 0
  · intro d e
    rw [show e + (k + 1) = (e + k) + 1 from by ring]
    step fm
    apply stepStar_trans (ih (d + 1) e)
    ring_nf; finish

-- R3 chain: drain c into a (doubled).
theorem r3_chain : ∀ k a c, ⟨a, (0 : ℕ), c + k, (0 : ℕ), e⟩ [fm]⊢* ⟨a + 2 * k, (0 : ℕ), c, (0 : ℕ), e⟩ := by
  intro k; induction' k with k ih
  · intro a c; exists 0
  · intro a c
    rw [show c + (k + 1) = (c + k) + 1 from by ring]
    step fm
    apply stepStar_trans (ih (a + 2) c)
    ring_nf; finish

-- R2,R1,R1 chain: k rounds.
-- Each round: (a+2, 0, c+1, d+1, e) -> (a, 0, c+2, d, e+1)
theorem r2r1r1_chain : ∀ k a c d e, ⟨a + 2 * k, (0 : ℕ), c + 1, d + k, e⟩ [fm]⊢* ⟨a, (0 : ℕ), c + k + 1, d, e + k⟩ := by
  intro k; induction' k with k ih
  · intro a c d e; simp; exists 0
  · intro a c d e
    rw [show a + 2 * (k + 1) = (a + 2) + 2 * k from by ring,
        show d + (k + 1) = (d + 1) + k from by ring]
    apply stepStar_trans (ih (a + 2) c (d + 1) e)
    rw [show c + k + 1 = (c + k) + 1 from by ring]
    execute fm 3

-- Wrapper for phase 2 with matching types.
theorem phase2_core (n : ℕ) :
    ⟨n + 2 * (n + 3), (0 : ℕ), 1 + 1, 0 + (n + 3), (0 : ℕ)⟩ [fm]⊢*
    ⟨n, (0 : ℕ), n + 5, (0 : ℕ), n + 3⟩ := by
  apply stepStar_trans (r2r1r1_chain (n + 3) n 1 0 0)
  ring_nf; finish

-- Phase 2: (3*n+6, 0, 2, n+3, 0) ->* (n, 0, n+5, 0, n+3)
theorem phase2 (n : ℕ) :
    ⟨3 * n + 6, (0 : ℕ), 2, n + 3, (0 : ℕ)⟩ [fm]⊢*
    ⟨n, (0 : ℕ), n + 5, (0 : ℕ), n + 3⟩ := by
  have h := phase2_core n
  rw [show n + 2 * (n + 3) = 3 * n + 6 from by ring,
      show (1 : ℕ) + 1 = 2 from rfl,
      show 0 + (n + 3) = n + 3 from by ring] at h
  exact h

-- Phase 3: R3 chain. (n, 0, n+5, 0, n+3) ->* (3*n+10, 0, 0, 0, n+3)
theorem phase3 (n : ℕ) :
    ⟨n, (0 : ℕ), n + 5, (0 : ℕ), n + 3⟩ [fm]⊢*
    ⟨3 * n + 10, (0 : ℕ), (0 : ℕ), (0 : ℕ), n + 3⟩ := by
  rw [show n + 5 = 0 + (n + 5) from by ring]
  apply stepStar_trans (r3_chain (n + 5) n 0 (e := n + 3))
  ring_nf; finish

-- Phase 4: R4 chain. (3*n+10, 0, 0, 0, n+3) ->* (3*n+10, 0, 0, n+3, 0)
theorem phase4 (n : ℕ) :
    ⟨3 * n + 10, (0 : ℕ), (0 : ℕ), (0 : ℕ), n + 3⟩ [fm]⊢*
    ⟨3 * n + 10, (0 : ℕ), (0 : ℕ), n + 3, (0 : ℕ)⟩ := by
  rw [show n + 3 = 0 + (n + 3) from by ring]
  exact e_to_d (n + 3) 0 0 (a := 3 * n + 10)

-- Main transition: (3*n+7, 0, 0, n+2, 0) ->+ (3*n+10, 0, 0, n+3, 0)
theorem main_transition (n : ℕ) :
    ⟨3 * n + 7, (0 : ℕ), (0 : ℕ), n + 2, (0 : ℕ)⟩ [fm]⊢⁺
    ⟨3 * n + 10, (0 : ℕ), (0 : ℕ), n + 3, (0 : ℕ)⟩ := by
  rw [show 3 * n + 7 = (3 * n + 6) + 1 from by ring]
  apply step_stepStar_stepPlus
    (show (⟨(3 * n + 6) + 1, (0 : ℕ), (0 : ℕ), n + 2, (0 : ℕ)⟩ : Q) [fm]⊢
         ⟨3 * n + 6, (0 : ℕ), 2, n + 3, (0 : ℕ)⟩ from by simp [fm])
  apply stepStar_trans (phase2 n)
  apply stepStar_trans (phase3 n)
  exact phase4 n

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨7, 0, 0, 2, 0⟩) (by execute fm 21)
  apply progress_nonhalt_simple (fm := fm) (A := ℕ)
    (fun n ↦ ⟨3 * n + 7, 0, 0, n + 2, 0⟩) 0
  intro n; exists n + 1
  show ⟨3 * n + 7, (0 : ℕ), (0 : ℕ), n + 2, (0 : ℕ)⟩ [fm]⊢⁺
       ⟨3 * (n + 1) + 7, (0 : ℕ), (0 : ℕ), (n + 1) + 2, (0 : ℕ)⟩
  rw [show 3 * (n + 1) + 7 = 3 * n + 10 from by ring,
      show (n + 1) + 2 = n + 3 from by ring]
  exact main_transition n

end Sz22_2003_unofficial_1267
