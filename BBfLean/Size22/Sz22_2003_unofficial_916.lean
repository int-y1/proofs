import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #916: [4/15, 3/98, 275/2, 7/5, 10/11]

Vector representation:
```
 2 -1 -1  0  0
-1  1  0 -2  0
-1  0  2  0  1
 0  0 -1  1  0
 1  0  1  0 -1
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_916

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a, b+1, c+1, d, e⟩ => some ⟨a+2, b, c, d, e⟩
  | ⟨a+1, b, c, d+2, e⟩ => some ⟨a, b+1, c, d, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b, c+2, d, e+1⟩
  | ⟨a, b, c+1, d, e⟩ => some ⟨a, b, c, d+1, e⟩
  | ⟨a, b, c, d, e+1⟩ => some ⟨a+1, b, c+1, d, e⟩
  | _ => none

-- R3 chain with d=0
theorem R3_chain_d0 : ∀ K, ∀ C E, ⟨K, (0 : ℕ), C, (0 : ℕ), E⟩ [fm]⊢* ⟨0, 0, C + 2 * K, 0, E + K⟩ := by
  intro K; induction K with
  | zero => intro C E; simp; exists 0
  | succ K ih =>
    intro C E; step fm
    apply stepStar_trans (ih (C + 2) (E + 1)); ring_nf; finish

-- R3 chain with d=1
theorem R3_chain_d1 : ∀ K, ∀ C E, ⟨K, (0 : ℕ), C, (1 : ℕ), E⟩ [fm]⊢* ⟨0, 0, C + 2 * K, 1, E + K⟩ := by
  intro K; induction K with
  | zero => intro C E; simp; exists 0
  | succ K ih =>
    intro C E
    have : ⟨K + 1, (0 : ℕ), C, (1 : ℕ), E⟩ [fm]⊢ ⟨K, 0, C + 2, 1, E + 1⟩ := by simp [fm]
    apply stepStar_trans (step_stepStar this)
    apply stepStar_trans (ih (C + 2) (E + 1)); ring_nf; finish

-- R4 chain
theorem R4_chain : ∀ K, ∀ D E, ⟨(0 : ℕ), (0 : ℕ), K, D, E⟩ [fm]⊢* ⟨0, 0, 0, D + K, E⟩ := by
  intro K; induction K with
  | zero => intro D E; simp; exists 0
  | succ K ih =>
    intro D E; step fm
    apply stepStar_trans (ih (D + 1) E); ring_nf; finish

-- Inner loop: R5,R1,R2,R2,R2 per round
theorem inner_loop : ∀ J, ∀ B D F, ⟨(0 : ℕ), B + 1, 0, D + 6 * J, F + J⟩ [fm]⊢*
    ⟨0, B + 1 + 2 * J, 0, D, F⟩ := by
  intro J; induction J with
  | zero => intro B D F; simp; exists 0
  | succ J ih =>
    intro B D F
    rw [show D + 6 * (J + 1) = ((((D + 6 * J) + 2) + 2) + 2) from by ring,
        show F + (J + 1) = (F + J) + 1 from by ring]
    step fm; step fm; step fm; step fm; step fm
    rw [show B + 2 + 1 = (B + 2) + 1 from by ring]
    apply stepStar_trans (ih (B + 2) D F); ring_nf; finish

-- Tail chain d=0: R3,R1,R1 per round, reducing b by 2
theorem tail_chain_d0 : ∀ J, ∀ A E, ⟨A + 1, 2 * J + 1, (0 : ℕ), (0 : ℕ), E⟩ [fm]⊢*
    ⟨A + 3 * J + 1, 1, 0, 0, E + J⟩ := by
  intro J; induction J with
  | zero => intro A E; simp; exists 0
  | succ J ih =>
    intro A E
    rw [show 2 * (J + 1) + 1 = (2 * J + 1) + 2 from by ring]
    step fm; step fm; step fm
    rw [show A + 4 = (A + 3) + 1 from by ring]
    apply stepStar_trans (ih (A + 3) (E + 1)); ring_nf; finish

-- Tail chain d=1 even b: R3,R1,R1 per round
theorem tail_chain_d1 : ∀ J, ∀ A E, ⟨A + 1, 2 * J, (0 : ℕ), (1 : ℕ), E⟩ [fm]⊢*
    ⟨A + 3 * J + 1, 0, 0, 1, E + J⟩ := by
  intro J; induction J with
  | zero => intro A E; simp; exists 0
  | succ J ih =>
    intro A E
    rw [show 2 * (J + 1) = (2 * J) + 2 from by ring]
    have h1 : ⟨A + 1, (2 * J) + 2, (0 : ℕ), (1 : ℕ), E⟩ [fm]⊢
        ⟨A, (2 * J) + 2, 2, 1, E + 1⟩ := by simp [fm]
    apply stepStar_trans (step_stepStar h1)
    have h2 : ⟨A, (2 * J) + 2, (2 : ℕ), (1 : ℕ), E + 1⟩ [fm]⊢
        ⟨A + 2, (2 * J) + 1, 1, 1, E + 1⟩ := by
      show ⟨A, ((2 * J) + 1) + 1, 1 + 1, 1, E + 1⟩ [fm]⊢ ⟨A + 2, (2 * J) + 1, 1, 1, E + 1⟩
      simp [fm]
    apply stepStar_trans (step_stepStar h2)
    have h3 : ⟨A + 2, (2 * J) + 1, (1 : ℕ), (1 : ℕ), E + 1⟩ [fm]⊢
        ⟨A + 4, 2 * J, 0, 1, E + 1⟩ := by
      show ⟨A + 2, (2 * J) + 1, 0 + 1, 1, E + 1⟩ [fm]⊢ ⟨A + 2 + 2, 2 * J, 0, 1, E + 1⟩
      simp [fm]
    apply stepStar_trans (step_stepStar h3)
    rw [show A + 4 = (A + 3) + 1 from by ring]
    apply stepStar_trans (ih (A + 3) (E + 1)); ring_nf; finish

-- Tail chain d=1 odd b: R3,R1,R1 per round
theorem tail_chain_d1_odd : ∀ J, ∀ A E, ⟨A + 1, 2 * J + 1, (0 : ℕ), (1 : ℕ), E⟩ [fm]⊢*
    ⟨A + 3 * J + 1, 1, 0, 1, E + J⟩ := by
  intro J; induction J with
  | zero => intro A E; simp; exists 0
  | succ J ih =>
    intro A E
    rw [show 2 * (J + 1) + 1 = (2 * J + 1) + 2 from by ring]
    have h1 : ⟨A + 1, (2 * J + 1) + 2, (0 : ℕ), (1 : ℕ), E⟩ [fm]⊢
        ⟨A, (2 * J + 1) + 2, 2, 1, E + 1⟩ := by simp [fm]
    apply stepStar_trans (step_stepStar h1)
    have h2 : ⟨A, (2 * J + 1) + 2, (2 : ℕ), (1 : ℕ), E + 1⟩ [fm]⊢
        ⟨A + 2, (2 * J + 1) + 1, 1, 1, E + 1⟩ := by
      show ⟨A, ((2 * J + 1) + 1) + 1, 1 + 1, 1, E + 1⟩ [fm]⊢
          ⟨A + 2, (2 * J + 1) + 1, 1, 1, E + 1⟩; simp [fm]
    apply stepStar_trans (step_stepStar h2)
    have h3 : ⟨A + 2, (2 * J + 1) + 1, (1 : ℕ), (1 : ℕ), E + 1⟩ [fm]⊢
        ⟨A + 4, 2 * J + 1, 0, 1, E + 1⟩ := by
      show ⟨A + 2, ((2 * J + 1)) + 1, 0 + 1, 1, E + 1⟩ [fm]⊢
          ⟨A + 2 + 2, 2 * J + 1, 0, 1, E + 1⟩; simp [fm]
    apply stepStar_trans (step_stepStar h3)
    rw [show A + 4 = (A + 3) + 1 from by ring]
    apply stepStar_trans (ih (A + 3) (E + 1)); ring_nf; finish

-- Finish tail d=0: R3,R1,R3,R3_chain,R4_chain
theorem finish_d0 : ∀ A E, ⟨A + 1, (1 : ℕ), (0 : ℕ), (0 : ℕ), E⟩ [fm]⊢*
    ⟨0, 0, 0, 2 * A + 5, E + A + 3⟩ := by
  intro A E
  -- R3: -> (A, 1, 2, 0, E+1)
  have h1 : ⟨A + 1, (1 : ℕ), (0 : ℕ), (0 : ℕ), E⟩ [fm]⊢
      ⟨A, 1, 2, 0, E + 1⟩ := by simp [fm]
  apply stepStar_trans (step_stepStar h1)
  -- R1: -> (A+2, 0, 1, 0, E+1)
  have h2 : ⟨A, (1 : ℕ), (2 : ℕ), (0 : ℕ), E + 1⟩ [fm]⊢
      ⟨A + 2, 0, 1, 0, E + 1⟩ := by
    show ⟨A, 0 + 1, 1 + 1, 0, E + 1⟩ [fm]⊢ ⟨A + 2, 0, 1, 0, E + 1⟩; simp [fm]
  apply stepStar_trans (step_stepStar h2)
  -- R3: -> (A+1, 0, 3, 0, E+2)
  have h3 : ⟨A + 2, (0 : ℕ), (1 : ℕ), (0 : ℕ), E + 1⟩ [fm]⊢
      ⟨A + 1, 0, 3, 0, E + 2⟩ := by
    rw [show A + 2 = (A + 1) + 1 from by ring]; simp [fm]
  apply stepStar_trans (step_stepStar h3)
  -- R3 chain d0
  apply stepStar_trans (R3_chain_d0 (A + 1) 3 (E + 2))
  rw [show 3 + 2 * (A + 1) = 2 * A + 5 from by ring,
      show E + 2 + (A + 1) = E + A + 3 from by ring]
  -- R4 chain
  apply stepStar_trans (R4_chain (2 * A + 5) 0 (E + A + 3))
  ring_nf; finish

-- Finish tail d=1 with b=1: R3,R1,R3,R3_chain,R4_chain
theorem finish_d1_b1 : ∀ A E, ⟨A + 1, (1 : ℕ), (0 : ℕ), (1 : ℕ), E⟩ [fm]⊢*
    ⟨0, 0, 0, 2 * A + 6, E + A + 3⟩ := by
  intro A E
  -- R3: -> (A, 1, 2, 1, E+1)
  have h1 : ⟨A + 1, (1 : ℕ), (0 : ℕ), (1 : ℕ), E⟩ [fm]⊢
      ⟨A, 1, 2, 1, E + 1⟩ := by simp [fm]
  apply stepStar_trans (step_stepStar h1)
  -- R1: -> (A+2, 0, 1, 1, E+1)
  have h2 : ⟨A, (1 : ℕ), (2 : ℕ), (1 : ℕ), E + 1⟩ [fm]⊢
      ⟨A + 2, 0, 1, 1, E + 1⟩ := by
    show ⟨A, 0 + 1, 1 + 1, 1, E + 1⟩ [fm]⊢ ⟨A + 2, 0, 1, 1, E + 1⟩; simp [fm]
  apply stepStar_trans (step_stepStar h2)
  -- R3: -> (A+1, 0, 3, 1, E+2)
  have h3 : ⟨A + 2, (0 : ℕ), (1 : ℕ), (1 : ℕ), E + 1⟩ [fm]⊢
      ⟨A + 1, 0, 3, 1, E + 2⟩ := by
    rw [show A + 2 = (A + 1) + 1 from by ring]; simp [fm]
  apply stepStar_trans (step_stepStar h3)
  -- R3 chain d1
  apply stepStar_trans (R3_chain_d1 (A + 1) 3 (E + 2))
  rw [show 3 + 2 * (A + 1) = 2 * A + 5 from by ring,
      show E + 2 + (A + 1) = E + A + 3 from by ring]
  -- R4 chain
  apply stepStar_trans (R4_chain (2 * A + 5) 1 (E + A + 3))
  rw [show 1 + (2 * A + 5) = 2 * A + 6 from by ring]; finish

-- Finish tail d=1 with b=0: R3,R3_chain,R4_chain
theorem finish_d1_b0 : ∀ A E, ⟨A + 1, (0 : ℕ), (0 : ℕ), (1 : ℕ), E⟩ [fm]⊢*
    ⟨0, 0, 0, 2 * A + 3, E + A + 1⟩ := by
  intro A E
  -- R3: -> (A, 0, 2, 1, E+1)
  have h1 : ⟨A + 1, (0 : ℕ), (0 : ℕ), (1 : ℕ), E⟩ [fm]⊢
      ⟨A, 0, 2, 1, E + 1⟩ := by simp [fm]
  apply stepStar_trans (step_stepStar h1)
  -- R3 chain d1
  apply stepStar_trans (R3_chain_d1 A 2 (E + 1))
  rw [show 2 + 2 * A = 2 * A + 2 from by ring,
      show E + 1 + A = E + A + 1 from by ring]
  -- R4 chain
  apply stepStar_trans (R4_chain (2 * A + 2) 1 (E + A + 1))
  rw [show 1 + (2 * A + 2) = 2 * A + 3 from by ring]; finish

-- T1: (0,0,0,6K+6, F+K+2) ⊢⁺ (0,0,0,6K+9, F+4K+5)
theorem trans_T1 (K F : ℕ) :
    ⟨(0 : ℕ), 0, 0, 6 * K + 6, F + K + 2⟩ [fm]⊢⁺ ⟨0, 0, 0, 6 * K + 9, F + 4 * K + 5⟩ := by
  -- Opening: 5 steps -> (0, 2, 0, 6K, F+K+1)
  rw [show 6 * K + 6 = (6 * K + 4) + 2 from by ring,
      show F + K + 2 = (F + K + 1) + 1 from by ring]
  step fm; step fm; step fm
  rw [show 6 * K + 4 = (6 * K + 2) + 2 from by ring]
  step fm
  rw [show 6 * K + 2 = (6 * K) + 2 from by ring]
  step fm
  -- Inner loop: (0, 2, 0, 6K, F+K+1) = (0, 1+1, 0, 0+6*K, (F+1)+K)
  rw [show (2 : ℕ) = 1 + 1 from by ring,
      show (6 * K : ℕ) = 0 + 6 * K from by ring,
      show F + K + 1 = (F + 1) + K from by ring]
  apply stepStar_trans (inner_loop K 1 0 (F + 1))
  -- After: (0, 2K+2, 0, 0, F+1)
  -- R5, R1: -> (3, 2K+1, 0, 0, F)
  rw [show 1 + 1 + 2 * K = (2 * K + 1) + 1 from by ring]
  have hR5 : ⟨(0 : ℕ), (2 * K + 1) + 1, 0, (0 : ℕ), F + 1⟩ [fm]⊢
      ⟨1, (2 * K + 1) + 1, 1, 0, F⟩ := by simp [fm]
  apply stepStar_trans (step_stepStar hR5)
  have hR1 : ⟨(1 : ℕ), (2 * K + 1) + 1, (1 : ℕ), (0 : ℕ), F⟩ [fm]⊢
      ⟨3, 2 * K + 1, 0, 0, F⟩ := by
    show ⟨1, (2 * K + 1) + 1, 0 + 1, 0, F⟩ [fm]⊢ ⟨1 + 2, 2 * K + 1, 0, 0, F⟩; simp [fm]
  apply stepStar_trans (step_stepStar hR1)
  -- Tail chain d0: (3, 2K+1, 0, 0, F) = (2+1, 2*K+1, 0, 0, F)
  rw [show (3 : ℕ) = 2 + 1 from by ring]
  apply stepStar_trans (tail_chain_d0 K 2 F)
  -- After: (3K+3, 1, 0, 0, F+K)
  rw [show 2 + 3 * K + 1 = (3 * K + 2) + 1 from by ring]
  -- Finish d0
  apply stepStar_trans (finish_d0 (3 * K + 2) (F + K))
  rw [show 2 * (3 * K + 2) + 5 = 6 * K + 9 from by ring,
      show F + K + (3 * K + 2) + 3 = F + 4 * K + 5 from by ring]; ring_nf; finish

-- T2: (0,0,0,6K+9, F+K+2) ⊢⁺ (0,0,0,6K+11, F+4K+6)
theorem trans_T2 (K F : ℕ) :
    ⟨(0 : ℕ), 0, 0, 6 * K + 9, F + K + 2⟩ [fm]⊢⁺ ⟨0, 0, 0, 6 * K + 11, F + 4 * K + 6⟩ := by
  -- Opening: 5 steps -> (0, 2, 0, 6K+3, F+K+1)
  rw [show 6 * K + 9 = (6 * K + 7) + 2 from by ring,
      show F + K + 2 = (F + K + 1) + 1 from by ring]
  step fm; step fm; step fm
  rw [show 6 * K + 7 = (6 * K + 5) + 2 from by ring]
  step fm
  rw [show 6 * K + 5 = (6 * K + 3) + 2 from by ring]
  step fm
  -- Inner loop: (0, 2, 0, 6K+3, F+K+1) = (0, 1+1, 0, 3+6*K, (F+1)+K)
  rw [show (2 : ℕ) = 1 + 1 from by ring,
      show 6 * K + 3 = 3 + 6 * K from by ring,
      show F + K + 1 = (F + 1) + K from by ring]
  apply stepStar_trans (inner_loop K 1 3 (F + 1))
  -- After: (0, 2K+2, 0, 3, F+1)
  -- Boundary D=3: R5, R1, R2
  rw [show 1 + 1 + 2 * K = (2 * K + 1) + 1 from by ring,
      show (3 : ℕ) = 1 + 2 from by ring]
  have hR5 : ⟨(0 : ℕ), (2 * K + 1) + 1, 0, (1 : ℕ) + 2, F + 1⟩ [fm]⊢
      ⟨1, (2 * K + 1) + 1, 1, 1 + 2, F⟩ := by simp [fm]
  apply stepStar_trans (step_stepStar hR5)
  have hR1 : ⟨(1 : ℕ), (2 * K + 1) + 1, (1 : ℕ), (1 : ℕ) + 2, F⟩ [fm]⊢
      ⟨3, 2 * K + 1, 0, 1 + 2, F⟩ := by
    show ⟨1, (2 * K + 1) + 1, 0 + 1, 1 + 2, F⟩ [fm]⊢ ⟨1 + 2, 2 * K + 1, 0, 1 + 2, F⟩; simp [fm]
  apply stepStar_trans (step_stepStar hR1)
  have hR2 : ⟨(3 : ℕ), 2 * K + 1, (0 : ℕ), (1 : ℕ) + 2, F⟩ [fm]⊢
      ⟨2, 2 * K + 2, 0, 1, F⟩ := by
    show ⟨2 + 1, 2 * K + 1, 0, 1 + 2, F⟩ [fm]⊢ ⟨2, (2 * K + 1) + 1, 0, 1, F⟩; simp [fm]
  apply stepStar_trans (step_stepStar hR2)
  -- (2, 2K+2, 0, 1, F): R3,R1,R1 -> (5, 2K, 0, 1, F+1)
  have h1 : ⟨(2 : ℕ), 2 * K + 2, (0 : ℕ), (1 : ℕ), F⟩ [fm]⊢
      ⟨1, 2 * K + 2, 2, 1, F + 1⟩ := by
    show ⟨1 + 1, 2 * K + 2, 0, 1, F⟩ [fm]⊢ ⟨1, 2 * K + 2, 0 + 2, 1, F + 1⟩; simp [fm]
  apply stepStar_trans (step_stepStar h1)
  have h2 : ⟨(1 : ℕ), 2 * K + 2, (2 : ℕ), (1 : ℕ), F + 1⟩ [fm]⊢
      ⟨3, 2 * K + 1, 1, 1, F + 1⟩ := by
    show ⟨1, (2 * K + 1) + 1, 1 + 1, 1, F + 1⟩ [fm]⊢ ⟨1 + 2, 2 * K + 1, 1, 1, F + 1⟩; simp [fm]
  apply stepStar_trans (step_stepStar h2)
  have h3 : ⟨(3 : ℕ), 2 * K + 1, (1 : ℕ), (1 : ℕ), F + 1⟩ [fm]⊢
      ⟨5, 2 * K, 0, 1, F + 1⟩ := by
    show ⟨3, (2 * K) + 1, 0 + 1, 1, F + 1⟩ [fm]⊢ ⟨3 + 2, 2 * K, 0, 1, F + 1⟩; simp [fm]
  apply stepStar_trans (step_stepStar h3)
  -- Tail chain d1 even: (5, 2K, 0, 1, F+1) = (4+1, 2*K, 0, 1, F+1)
  rw [show (5 : ℕ) = 4 + 1 from by ring]
  apply stepStar_trans (tail_chain_d1 K 4 (F + 1))
  -- After: (3K+5, 0, 0, 1, F+K+1) = ((3K+4)+1, 0, 0, 1, F+K+1)
  rw [show 4 + 3 * K + 1 = (3 * K + 4) + 1 from by ring,
      show F + 1 + K = F + K + 1 from by ring]
  -- Finish d1 b0
  apply stepStar_trans (finish_d1_b0 (3 * K + 4) (F + K + 1))
  rw [show 2 * (3 * K + 4) + 3 = 6 * K + 11 from by ring,
      show F + K + 1 + (3 * K + 4) + 1 = F + 4 * K + 6 from by ring]; finish

-- T3: (0,0,0,6K+11, F+K+2) ⊢⁺ (0,0,0,6K+12, F+4K+7)
theorem trans_T3 (K F : ℕ) :
    ⟨(0 : ℕ), 0, 0, 6 * K + 11, F + K + 2⟩ [fm]⊢⁺ ⟨0, 0, 0, 6 * K + 12, F + 4 * K + 7⟩ := by
  -- Opening: 5 steps -> (0, 2, 0, 6K+5, F+K+1)
  rw [show 6 * K + 11 = (6 * K + 9) + 2 from by ring,
      show F + K + 2 = (F + K + 1) + 1 from by ring]
  step fm; step fm; step fm
  rw [show 6 * K + 9 = (6 * K + 7) + 2 from by ring]
  step fm
  rw [show 6 * K + 7 = (6 * K + 5) + 2 from by ring]
  step fm
  -- Inner loop: (0, 2, 0, 6K+5, F+K+1) = (0, 1+1, 0, 5+6*K, (F+1)+K)
  rw [show (2 : ℕ) = 1 + 1 from by ring,
      show 6 * K + 5 = 5 + 6 * K from by ring,
      show F + K + 1 = (F + 1) + K from by ring]
  apply stepStar_trans (inner_loop K 1 5 (F + 1))
  -- After: (0, 2K+2, 0, 5, F+1)
  -- Boundary D=5: R5, R1, R2, R2
  rw [show 1 + 1 + 2 * K = (2 * K + 1) + 1 from by ring,
      show (5 : ℕ) = 1 + 2 + 2 from by ring]
  have hR5 : ⟨(0 : ℕ), (2 * K + 1) + 1, 0, (1 : ℕ) + 2 + 2, F + 1⟩ [fm]⊢
      ⟨1, (2 * K + 1) + 1, 1, 1 + 2 + 2, F⟩ := by simp [fm]
  apply stepStar_trans (step_stepStar hR5)
  have hR1 : ⟨(1 : ℕ), (2 * K + 1) + 1, (1 : ℕ), (1 : ℕ) + 2 + 2, F⟩ [fm]⊢
      ⟨3, 2 * K + 1, 0, 1 + 2 + 2, F⟩ := by
    show ⟨1, (2 * K + 1) + 1, 0 + 1, 1 + 2 + 2, F⟩ [fm]⊢ ⟨1 + 2, 2 * K + 1, 0, 1 + 2 + 2, F⟩
    simp [fm]
  apply stepStar_trans (step_stepStar hR1)
  have hR2a : ⟨(3 : ℕ), 2 * K + 1, (0 : ℕ), (1 : ℕ) + 2 + 2, F⟩ [fm]⊢
      ⟨2, 2 * K + 2, 0, 1 + 2, F⟩ := by
    show ⟨2 + 1, 2 * K + 1, 0, (1 + 2) + 2, F⟩ [fm]⊢ ⟨2, (2 * K + 1) + 1, 0, 1 + 2, F⟩; simp [fm]
  apply stepStar_trans (step_stepStar hR2a)
  have hR2b : ⟨(2 : ℕ), 2 * K + 2, (0 : ℕ), (1 : ℕ) + 2, F⟩ [fm]⊢
      ⟨1, 2 * K + 3, 0, 1, F⟩ := by
    show ⟨1 + 1, 2 * K + 2, 0, 1 + 2, F⟩ [fm]⊢ ⟨1, (2 * K + 2) + 1, 0, 1, F⟩; simp [fm]
  apply stepStar_trans (step_stepStar hR2b)
  -- (1, 2K+3, 0, 1, F): R3 -> (0, 2K+3, 2, 1, F+1)
  have h1 : ⟨(1 : ℕ), 2 * K + 3, (0 : ℕ), (1 : ℕ), F⟩ [fm]⊢
      ⟨0, 2 * K + 3, 2, 1, F + 1⟩ := by
    show ⟨0 + 1, 2 * K + 3, 0, 1, F⟩ [fm]⊢ ⟨0, 2 * K + 3, 0 + 2, 1, F + 1⟩; simp [fm]
  apply stepStar_trans (step_stepStar h1)
  -- R1: -> (2, 2K+2, 1, 1, F+1)
  have h2 : ⟨(0 : ℕ), 2 * K + 3, (2 : ℕ), (1 : ℕ), F + 1⟩ [fm]⊢
      ⟨2, 2 * K + 2, 1, 1, F + 1⟩ := by
    show ⟨0, (2 * K + 2) + 1, 1 + 1, 1, F + 1⟩ [fm]⊢ ⟨0 + 2, 2 * K + 2, 1, 1, F + 1⟩; simp [fm]
  apply stepStar_trans (step_stepStar h2)
  -- R1: -> (4, 2K+1, 0, 1, F+1)
  have h3 : ⟨(2 : ℕ), 2 * K + 2, (1 : ℕ), (1 : ℕ), F + 1⟩ [fm]⊢
      ⟨4, 2 * K + 1, 0, 1, F + 1⟩ := by
    show ⟨2, (2 * K + 1) + 1, 0 + 1, 1, F + 1⟩ [fm]⊢ ⟨2 + 2, 2 * K + 1, 0, 1, F + 1⟩; simp [fm]
  apply stepStar_trans (step_stepStar h3)
  -- Tail chain d1 odd: (4, 2K+1, 0, 1, F+1) = (3+1, 2*K+1, 0, 1, F+1)
  rw [show (4 : ℕ) = 3 + 1 from by ring]
  apply stepStar_trans (tail_chain_d1_odd K 3 (F + 1))
  -- After: (3+3K+1, 1, 0, 1, F+1+K) = (3K+4, 1, 0, 1, F+K+1)
  rw [show 3 + 3 * K + 1 = (3 * K + 3) + 1 from by ring,
      show F + 1 + K = F + K + 1 from by ring]
  -- Finish d1 b1
  apply stepStar_trans (finish_d1_b1 (3 * K + 3) (F + K + 1))
  rw [show 2 * (3 * K + 3) + 6 = 6 * K + 12 from by ring,
      show F + K + 1 + (3 * K + 3) + 3 = F + 4 * K + 7 from by ring]; finish

-- Main nonhalt theorem
theorem nonhalt : ¬halts fm c₀ := by
  -- Bootstrap: c₀ = (1,0,0,0,0) ⊢* (0,0,0,6,6)
  apply stepStar_not_halts_not_halts (c₂ := ⟨0, 0, 0, 6, 6⟩) (by execute fm 38)
  -- Use progress_nonhalt with P(q) := ∃ K E, q = (0,0,0,6K+6,E) ∧ E ≥ K+2
  apply progress_nonhalt (fm := fm)
    (P := fun q ↦ ∃ K E, q = ⟨0, 0, 0, 6 * K + 6, E⟩ ∧ E ≥ K + 2)
  · intro q ⟨K, E, hq, hE⟩; subst hq
    obtain ⟨F, rfl⟩ : ∃ F, E = F + K + 2 := ⟨E - K - 2, by omega⟩
    refine ⟨⟨0, 0, 0, 6 * (K + 1) + 6, F + 10 * K + 14⟩,
            ⟨K + 1, F + 10 * K + 14, by ring_nf, by omega⟩, ?_⟩
    -- Compose T1 -> T2 -> T3
    apply stepPlus_trans (trans_T1 K F)
    rw [show F + 4 * K + 5 = (F + 3 * K + 3) + K + 2 from by ring]
    apply stepPlus_trans (trans_T2 K (F + 3 * K + 3))
    rw [show F + 3 * K + 3 + 4 * K + 6 = (F + 6 * K + 7) + K + 2 from by ring]
    apply stepPlus_stepStar_stepPlus (trans_T3 K (F + 6 * K + 7))
    rw [show F + 6 * K + 7 + 4 * K + 7 = F + 10 * K + 14 from by ring,
        show 6 * K + 12 = 6 * (K + 1) + 6 from by ring]; finish
  · exact ⟨0, 6, by ring_nf, by omega⟩

end Sz22_2003_unofficial_916
