import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #240: [11/105, 3/22, 20/3, 7/2, 99/7]

Vector representation:
```
 0 -1 -1 -1  1
-1  1  0  0 -1
 2 -1  1  0  0
-1  0  0  1  0
 0  2  0 -1  1
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_240

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a, b+1, c+1, d+1, e⟩ => some ⟨a, b, c, d, e+1⟩
  | ⟨a+1, b, c, d, e+1⟩ => some ⟨a, b+1, c, d, e⟩
  | ⟨a, b+1, c, d, e⟩ => some ⟨a+2, b, c+1, d, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b, c, d+1, e⟩
  | ⟨a, b, c, d+1, e⟩ => some ⟨a, b+2, c, d, e+1⟩
  | _ => none

-- Helper: R3 fires when a=0, b>=1, d=0
theorem r3_step (b c e : ℕ) : ⟨0, b+1, c, 0, e⟩ [fm]⊢ ⟨2, b, c+1, 0, e⟩ := by
  simp only [fm]

-- Helper: R2 fires when a>=1, e>=1, d=0
theorem r2_step (a b c e : ℕ) : ⟨a+1, b, c, 0, e+1⟩ [fm]⊢ ⟨a, b+1, c, 0, e⟩ := by
  simp only [fm]

-- Drain: R5+R1+R1 repeated k times
theorem drain : ∀ k C D E,
    ⟨0, 0, C + 2 * k, D + 3 * k, E⟩ [fm]⊢* ⟨(0 : ℕ), 0, C, D, E + 3 * k⟩ := by
  intro k; induction k with
  | zero => intro C D E; simp; exists 0
  | succ k ih =>
    intro C D E
    rw [show D + 3 * (k + 1) = (D + 3 * k + 2) + 1 from by ring]
    step fm
    rw [show (2 : ℕ) = 1 + 1 from by ring,
        show C + 2 * (k + 1) = (C + 2 * k + 1) + 1 from by ring,
        show D + 3 * k + 2 = (D + 3 * k + 1) + 1 from by ring]
    step fm
    rw [show (1 : ℕ) = 0 + 1 from by ring,
        show C + 2 * k + 1 = (C + 2 * k) + 1 from by ring,
        show D + 3 * k + 1 = (D + 3 * k) + 1 from by ring]
    step fm
    apply stepStar_trans (ih C D (E + 1 + 1 + 1))
    ring_nf; finish

-- R3 chain: (A+1, B+1, C, 0, 0) ->* (A+2B+3, 0, C+B+1, 0, 0)
theorem r3_chain : ∀ B A C,
    ⟨A + 1, B + 1, C, 0, 0⟩ [fm]⊢* ⟨A + 2 * B + 3, (0 : ℕ), C + B + 1, 0, 0⟩ := by
  intro B; induction B with
  | zero =>
    intro A C; step fm; ring_nf; finish
  | succ B ih =>
    intro A C
    rw [show B + 1 + 1 = (B + 1) + 1 from by ring]
    step fm
    rw [show A + 1 + 2 = (A + 2) + 1 from by ring]
    apply stepStar_trans (ih (A + 2) (C + 1))
    ring_nf; finish

-- R4 chain: (A, 0, C, D, 0) ->* (0, 0, C, D+A, 0)
theorem r4_chain : ∀ A C D,
    ⟨A, 0, C, D, 0⟩ [fm]⊢* ⟨(0 : ℕ), 0, C, D + A, 0⟩ := by
  intro A; induction A with
  | zero => intro C D; simp; exists 0
  | succ A ih =>
    intro C D; step fm
    apply stepStar_trans (ih C (D + 1))
    ring_nf; finish

-- Generalized pump: (0, B+2, C, 0, 2M+1) ->* (2M+2B+5, 0, C+2M+B+3, 0, 0)
theorem pump_gen : ∀ M B C,
    ⟨0, B + 2, C, 0, 2 * M + 1⟩ [fm]⊢* ⟨2 * M + 2 * B + 5, (0 : ℕ), C + 2 * M + B + 3, 0, 0⟩ := by
  intro M; induction M with
  | zero =>
    intro B C; simp
    -- (0, B+2, C, 0, 1): R3
    rw [show B + 2 = (B + 1) + 1 from by ring]
    apply stepStar_trans (step_stepStar (r3_step (B + 1) C 1))
    -- (2, B+1, C+1, 0, 1): R2
    rw [show (2 : ℕ) = 1 + 1 from by ring,
        show (1 : ℕ) = 0 + 1 from by ring]
    apply stepStar_trans (step_stepStar (r2_step 1 (B + 1) (C + 1) 0))
    -- (1, B+2, C+1, 0, 0): r3_chain
    rw [show (1 : ℕ) = 0 + 1 from by ring,
        show B + 2 = (B + 1) + 1 from by ring]
    apply stepStar_trans (r3_chain (B + 1) 0 (C + 1))
    ring_nf; finish
  | succ M ih =>
    intro B C
    -- (0, B+2, C, 0, 2(M+1)+1) = (0, B+2, C, 0, 2M+3)
    -- R3
    rw [show 2 * (M + 1) + 1 = 2 * M + 3 from by ring,
        show B + 2 = (B + 1) + 1 from by ring]
    apply stepStar_trans (step_stepStar (r3_step (B + 1) C (2 * M + 3)))
    -- (2, B+1, C+1, 0, 2M+3): R2
    rw [show (2 : ℕ) = 1 + 1 from by ring,
        show 2 * M + 3 = (2 * M + 2) + 1 from by ring]
    apply stepStar_trans (step_stepStar (r2_step 1 (B + 1) (C + 1) (2 * M + 2)))
    -- (1, B+2, C+1, 0, 2M+2): R2
    rw [show (1 : ℕ) = 0 + 1 from by ring,
        show 2 * M + 2 = (2 * M + 1) + 1 from by ring]
    apply stepStar_trans (step_stepStar (r2_step 0 (B + 2) (C + 1) (2 * M + 1)))
    -- (0, B+3, C+1, 0, 2M+1) = (0, (B+1)+2, C+1, 0, 2M+1)
    rw [show B + 3 = (B + 1) + 2 from by ring]
    apply stepStar_trans (ih (B + 1) (C + 1))
    ring_nf; finish

-- Even to odd transition
theorem even_to_odd (k : ℕ) :
    ⟨0, 0, 2*k*k+4*k, 6*k+1, 0⟩ [fm]⊢⁺ ⟨(0 : ℕ), 0, 2*k*k+6*k+3, 6*k+5, 0⟩ := by
  rw [show 2*k*k+4*k = 2*k*k + 2*(2*k) from by ring,
      show 6*k+1 = 1 + 3*(2*k) from by ring]
  apply stepStar_stepPlus_stepPlus (drain (2*k) (2*k*k) 1 0)
  rw [show (1 : ℕ) = 0 + 1 from by ring,
      show 0 + 3 * (2 * k) = 6*k from by ring]
  step fm
  rw [show (2 : ℕ) = 0 + 2 from by ring,
      show 6*k+1 = 2*(3*k) + 1 from by ring]
  apply stepStar_trans (pump_gen (3*k) 0 (2*k*k))
  apply stepStar_trans (r4_chain (2*(3*k)+2*0+5) (2*k*k+2*(3*k)+0+3) 0)
  ring_nf; finish

-- Odd to even transition
theorem odd_to_even (k : ℕ) :
    ⟨0, 0, 2*k*k+6*k+3, 6*k+5, 0⟩ [fm]⊢⁺ ⟨(0 : ℕ), 0, 2*k*k+8*k+6, 6*k+7, 0⟩ := by
  -- drain 2k+1 rounds
  rw [show 2*k*k+6*k+3 = (2*k*k+2*k+1) + 2*(2*k+1) from by ring,
      show 6*k+5 = 2 + 3*(2*k+1) from by ring]
  apply stepStar_stepPlus_stepPlus (drain (2*k+1) (2*k*k+2*k+1) 2 0)
  -- (0, 0, 2k²+2k+1, 2, 6k+3)
  rw [show (2 : ℕ) = (1 : ℕ) + 1 from by ring,
      show 0 + 3 * (2 * k + 1) = 6*k+3 from by ring]
  -- R5
  step fm
  -- (0, 2, 2k²+2k+1, 1, 6k+4)
  rw [show (2 : ℕ) = 1 + 1 from by ring,
      show 2*k*k+2*k+1 = (2*k*k+2*k) + 1 from by ring,
      show (1 : ℕ) = 0 + 1 from by ring,
      show 6*k+4 = (6*k+3) + 1 from by ring]
  -- R1
  step fm
  -- (0, 1, 2k²+2k, 0, 6k+5): use r3_step
  -- After step fm the state is (0, 0+1, 2*k*k+2*k, 0, 6*k+3+1+1)
  -- R3 via r3_step
  apply stepStar_trans (step_stepStar (r3_step 0 (2*k*k+2*k) (6*k+3+1+1)))
  -- (2, 0, 2k²+2k+1, 0, 6k+5): R2 via r2_step
  rw [show (2 : ℕ) = 1 + 1 from by ring,
      show 6*k+3+1+1 = (6*k+3+1) + 1 from by ring]
  apply stepStar_trans (step_stepStar (r2_step 1 0 (2*k*k+2*k+1) (6*k+3+1)))
  -- (1, 1, 2k²+2k+1, 0, 6k+4): R2 via r2_step
  rw [show (1 : ℕ) = 0 + 1 from by ring,
      show 6*k+3+1 = (6*k+3) + 1 from by ring]
  apply stepStar_trans (step_stepStar (r2_step 0 1 (2*k*k+2*k+1) (6*k+3)))
  -- (0, 2, 2k²+2k+1, 0, 6k+3) = (0, 0+2, 2k²+2k+1, 0, 2*(3k+1)+1)
  rw [show (2 : ℕ) = 0 + 2 from by ring,
      show 6*k+3 = 2*(3*k+1) + 1 from by ring]
  apply stepStar_trans (pump_gen (3*k+1) 0 (2*k*k+2*k+1))
  apply stepStar_trans (r4_chain (2*(3*k+1)+2*0+5) (2*k*k+2*k+1+2*(3*k+1)+0+3) 0)
  ring_nf; finish

-- Combined: state k -> state k+1
theorem main_trans (k : ℕ) :
    ⟨0, 0, 2*k*k+4*k, 6*k+1, 0⟩ [fm]⊢⁺ ⟨(0 : ℕ), 0, 2*(k+1)*(k+1)+4*(k+1), 6*(k+1)+1, 0⟩ := by
  apply stepPlus_trans (even_to_odd k)
  rw [show 2*(k+1)*(k+1)+4*(k+1) = 2*k*k+8*k+6 from by ring,
      show 6*(k+1)+1 = 6*k+7 from by ring]
  exact odd_to_even k

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨0, 0, 0, 1, 0⟩) (by execute fm 1)
  apply progress_nonhalt_simple (fm := fm) (A := ℕ)
    (fun k ↦ ⟨0, 0, 2*k*k+4*k, 6*k+1, 0⟩) 0
  intro k
  exact ⟨k + 1, main_trans k⟩

end Sz22_2003_unofficial_240
