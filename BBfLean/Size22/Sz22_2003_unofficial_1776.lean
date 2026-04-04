import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #1776: [9/10, 343/2, 22/21, 5/11, 10/7]

Vector representation:
```
-1  2 -1  0  0
-1  0  0  3  0
 1 -1  0 -1  1
 0  0  1  0 -1
 1  0  1 -1  0
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_1776

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a+1, b, c+1, d, e⟩ => some ⟨a, b+2, c, d, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b, c, d+3, e⟩
  | ⟨a, b+1, c, d+1, e⟩ => some ⟨a+1, b, c, d, e+1⟩
  | ⟨a, b, c, d, e+1⟩ => some ⟨a, b, c+1, d, e⟩
  | ⟨a, b, c, d+1, e⟩ => some ⟨a+1, b, c+1, d, e⟩
  | _ => none

-- R4 repeated: (0, 0, c, d, k) →* (0, 0, c+k, d, 0). a=0, b=0 so R1,R2,R3 don't fire.
-- With c free and k induction.
theorem e_to_c : ∀ k, ∀ c d, ⟨(0 : ℕ), 0, c, d, k⟩ [fm]⊢* ⟨0, 0, c + k, d, 0⟩ := by
  intro k; induction' k with k ih <;> intro c d
  · exists 0
  · step fm  -- R4: (0, 0, c+1, d, k)
    apply stepStar_trans (ih (c + 1) d)
    ring_nf; finish

-- R3/R1 interleaving: (0, B+1, k, D+k, E) →* (0, B+1+k, 0, D, E+k)
theorem r3r1_chain : ∀ k, ∀ B D E, ⟨(0 : ℕ), B + 1, k, D + k, E⟩ [fm]⊢* ⟨0, B + 1 + k, 0, D, E + k⟩ := by
  intro k; induction' k with k ih <;> intro B D E
  · exists 0
  · rw [show D + (k + 1) = (D + k) + 1 from by ring]
    step fm; step fm
    apply stepStar_trans (ih (B + 1) D (E + 1))
    ring_nf; finish

-- R3/R2 alternation: (0, k+1, 0, D+1, E) →* (0, 0, 0, D+2*k+3, E+k+1)
theorem r3r2_chain : ∀ k, ∀ D E, ⟨(0 : ℕ), k + 1, 0, D + 1, E⟩ [fm]⊢* ⟨0, 0, 0, D + 2 * k + 3, E + k + 1⟩ := by
  intro k; induction' k with k ih <;> intro D E
  · step fm; step fm; ring_nf; finish
  · step fm; step fm
    rw [show D + 3 = (D + 2) + 1 from by ring]
    apply stepStar_trans (ih (D + 2) (E + 1))
    ring_nf; finish

-- Full chain: (0, 0, 0, e+n+3, e) →* (0, 0, 0, 2*e+n+6, 2*e+2)
theorem full_chain (n e : ℕ) : ⟨(0 : ℕ), 0, 0, e + n + 3, e⟩ [fm]⊢* ⟨0, 0, 0, 2 * e + n + 6, 2 * e + 2⟩ := by
  -- Phase 1: e_to_c
  apply stepStar_trans (e_to_c e 0 (e + n + 3))
  -- Goal: (0, 0, 0+e, e+n+3, 0) ⊢* target
  -- Phase 2: R5+R1
  rw [show (0 : ℕ) + e = e from Nat.zero_add e,
      show e + n + 3 = (e + n + 2) + 1 from by ring]
  step fm; step fm
  -- at (0, 2, e, e+n+2, 0)
  -- Phase 3: R3/R1 chain
  rw [show e + n + 2 = (n + 2) + e from by ring]
  apply stepStar_trans (r3r1_chain e 1 (n + 2) 0)
  -- at (0, 1+1+e, 0, n+2, 0+e)
  -- Phase 4: R3/R2 chain
  rw [show (1 : ℕ) + 1 + e = (e + 1) + 1 from by ring,
      show n + 2 = (n + 1) + 1 from by ring,
      show (0 : ℕ) + e = e from Nat.zero_add e]
  apply stepStar_trans (r3r2_chain (e + 1) (n + 1) e)
  ring_nf; finish

-- Convert to ⊢⁺
theorem main_trans (n e : ℕ) : ⟨(0 : ℕ), 0, 0, e + n + 3, e⟩ [fm]⊢⁺ ⟨0, 0, 0, 2 * e + n + 6, 2 * e + 2⟩ := by
  apply stepStar_stepPlus (full_chain n e)
  intro h
  have h4 : e + n + 3 = 2 * e + n + 6 := congr_arg (·.2.2.2.1) h
  omega

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨0, 0, 0, 3, 0⟩) (by execute fm 1)
  apply progress_nonhalt (fm := fm)
    (P := fun q ↦ ∃ n e, q = ⟨0, 0, 0, e + n + 3, e⟩)
  · intro c ⟨n, e, hq⟩; subst hq
    refine ⟨⟨0, 0, 0, 2 * e + n + 6, 2 * e + 2⟩, ⟨n + 1, 2 * e + 2, ?_⟩, main_trans n e⟩
    congr 1; ring_nf
  · exact ⟨0, 0, rfl⟩
