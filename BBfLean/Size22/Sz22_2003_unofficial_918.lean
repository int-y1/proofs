import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #918: [4/15, 33/14, 125/2, 7/11, 21/5]

Vector representation:
```
 2 -1 -1  0  0
-1  1  0 -1  1
-1  0  3  0  0
 0  0  0  1 -1
 0  1 -1  1  0
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_918

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a, b+1, c+1, d, e⟩ => some ⟨a+2, b, c, d, e⟩
  | ⟨a+1, b, c, d+1, e⟩ => some ⟨a, b+1, c, d, e+1⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b, c+3, d, e⟩
  | ⟨a, b, c, d, e+1⟩ => some ⟨a, b, c, d+1, e⟩
  | ⟨a, b, c+1, d, e⟩ => some ⟨a, b+1, c, d+1, e⟩
  | _ => none

-- Phase 1: R4 chain - transfer e to d
theorem R4_chain : ∀ K, ∀ C D E, ⟨(0 : ℕ), (0 : ℕ), C, D, E + K⟩ [fm]⊢* ⟨0, 0, C, D + K, E⟩ := by
  intro K; induction K with
  | zero => intro C D E; simp; exists 0
  | succ K ih =>
    intro C D E
    rw [show E + (K + 1) = (E + K) + 1 from by ring]
    step fm
    apply stepStar_trans (ih C (D + 1) E); ring_nf; finish

-- Phase 3: R1R2 chain
-- Each pair: R1 then R2
-- (A, 1, C+K, D+K, E) ⊢* (A+K, 1, C, D, E+K)
theorem R1R2_chain : ∀ K, ∀ A C D E, ⟨A, (1 : ℕ), C + K, D + K, E⟩ [fm]⊢* ⟨A + K, 1, C, D, E + K⟩ := by
  intro K; induction K with
  | zero => intro A C D E; simp; exists 0
  | succ K ih =>
    intro A C D E
    rw [show C + (K + 1) = (C + K) + 1 from by ring,
        show D + (K + 1) = (D + K) + 1 from by ring]
    step fm; step fm
    apply stepStar_trans (ih (A + 1) C D (E + 1)); ring_nf; finish

-- Phase 4: R3 chain - drain a, increase c by 3 each
theorem R3_chain : ∀ K, ∀ C E, ⟨K, (0 : ℕ), C, (0 : ℕ), E⟩ [fm]⊢* ⟨0, 0, C + 3 * K, 0, E⟩ := by
  intro K; induction K with
  | zero => intro C E; simp; exists 0
  | succ K ih =>
    intro C E
    step fm
    apply stepStar_trans (ih (C + 3) E); ring_nf; finish

-- Full cycle: from (0, 0, e*e+5*e+3, 0, e) to (0, 0, (e+1)^2+5*(e+1)+3, 0, e+1)
-- Phase 1: R4 x e: (0,0,C,0,e) -> (0,0,C,e,0) where C=e²+5e+3
-- Phase 2: R5: (0,0,C,e,0) -> (0,1,C-1,e+1,0)   [need C>=1, e=0 for R4 to not fire]
--   Actually: a=0, so R4 fires only if e>=1. R5 fires if c>=1 and a=0,b=0,e=0.
--   After R4 chain, e=0, so R4 won't fire. a=0, b=0, so R1,R2,R3 won't fire. e=0 so R4 won't fire.
--   c=C>=3>=1, so R5 fires. Good.
-- Phase 3: R1R2 x (e+1): (0,1,C-1,e+1,0) -> (e+1,1,C-e-2,0,e+1)
-- Phase 3b: Final R1: (e+1,1,C-e-2,0,e+1)
--   b=1>=1, C-e-2=e²+4e+1>=1 for e>=0. So R1 fires:
--   (e+1,1,(e²+4e)+1,0,e+1) -> (e+3,0,e²+4e,0,e+1)
-- Phase 4: R3 x (e+3): (e+3,0,e²+4e,0,e+1) -> (0,0,e²+4e+3(e+3),0,e+1)
--   = (0,0,e²+7e+9,0,e+1) = (0,0,(e+1)²+5(e+1)+3,0,e+1)

theorem main_transition (e : ℕ) :
    ⟨(0 : ℕ), 0, e * e + 5 * e + 3, 0, e⟩ [fm]⊢⁺
    ⟨0, 0, (e + 1) * (e + 1) + 5 * (e + 1) + 3, 0, e + 1⟩ := by
  -- Phase 1: R4 chain: (0,0,C,0,e) -> (0,0,C,e,0)
  have h1 : ⟨(0 : ℕ), 0, e * e + 5 * e + 3, 0, e⟩ [fm]⊢*
      ⟨0, 0, e * e + 5 * e + 3, e, 0⟩ := by
    have := R4_chain e (e * e + 5 * e + 3) 0 0
    simp at this; exact this
  -- Phase 2: R5 step
  have h2 : ⟨(0 : ℕ), 0, e * e + 5 * e + 3, e, 0⟩ [fm]⊢*
      ⟨0, 1, e * e + 5 * e + 2, e + 1, 0⟩ := by
    rw [show e * e + 5 * e + 3 = (e * e + 5 * e + 2) + 1 from by ring]
    exact step_stepStar (by simp [fm])
  -- Phase 3: R1R2 chain with K=e+1
  have h3 : ⟨(0 : ℕ), 1, e * e + 5 * e + 2, e + 1, 0⟩ [fm]⊢*
      ⟨e + 1, 1, e * e + 4 * e + 1, 0, e + 1⟩ := by
    have := R1R2_chain (e + 1) 0 (e * e + 4 * e + 1) 0 0
    simp at this
    rw [show e * e + 4 * e + 1 + (e + 1) = e * e + 5 * e + 2 from by ring] at this
    exact this
  -- Phase 3b: Final R1
  have h3b : ⟨e + 1, (1 : ℕ), e * e + 4 * e + 1, (0 : ℕ), e + 1⟩ [fm]⊢*
      ⟨e + 3, 0, e * e + 4 * e, 0, e + 1⟩ := by
    rw [show e * e + 4 * e + 1 = (e * e + 4 * e) + 1 from by ring]
    exact step_stepStar (by simp [fm])
  -- Phase 4: R3 chain
  have h4 : ⟨e + 3, (0 : ℕ), e * e + 4 * e, (0 : ℕ), e + 1⟩ [fm]⊢*
      ⟨0, 0, (e + 1) * (e + 1) + 5 * (e + 1) + 3, 0, e + 1⟩ := by
    have := R3_chain (e + 3) (e * e + 4 * e) (e + 1)
    rw [show e * e + 4 * e + 3 * (e + 3) = (e + 1) * (e + 1) + 5 * (e + 1) + 3 from by ring] at this
    exact this
  -- Compose: h1(⊢*) + h2(⊢*,has step) + h3(⊢*) + h3b(⊢*) + h4(⊢*)
  -- Make h2 into ⊢⁺ by using the explicit R5 step
  have h2' : ⟨(0 : ℕ), 0, e * e + 5 * e + 3, e, 0⟩ [fm]⊢⁺
      ⟨0, 1, e * e + 5 * e + 2, e + 1, 0⟩ := by
    rw [show e * e + 5 * e + 3 = (e * e + 5 * e + 2) + 1 from by ring]
    exact step_stepPlus (by simp [fm])
  -- h1(⊢*) + h2'(⊢⁺) = ⊢⁺
  have hab : ⟨(0 : ℕ), 0, e * e + 5 * e + 3, 0, e⟩ [fm]⊢⁺
      ⟨0, 1, e * e + 5 * e + 2, e + 1, 0⟩ := stepStar_stepPlus_stepPlus h1 h2'
  -- h3(⊢*) + h3b(⊢*) + h4(⊢*) = ⊢*
  have hcd : ⟨(0 : ℕ), 1, e * e + 5 * e + 2, e + 1, 0⟩ [fm]⊢*
      ⟨0, 0, (e + 1) * (e + 1) + 5 * (e + 1) + 3, 0, e + 1⟩ :=
    stepStar_trans h3 (stepStar_trans h3b h4)
  exact stepPlus_stepStar_stepPlus hab hcd

theorem nonhalt : ¬halts fm c₀ := by
  -- Bootstrap: (1,0,0,0,0) ⊢* (0,0,3,0,0) in 1 step
  -- (0,0,3,0,0) is the canonical state for e=0: 0²+5·0+3 = 3
  apply stepStar_not_halts_not_halts (c₂ := ⟨0, 0, 3, 0, 0⟩) (by execute fm 1)
  apply progress_nonhalt_simple (fm := fm) (A := ℕ)
    (fun e ↦ ⟨0, 0, e * e + 5 * e + 3, 0, e⟩) 0
  intro e; exact ⟨e + 1, main_transition e⟩

end Sz22_2003_unofficial_918
