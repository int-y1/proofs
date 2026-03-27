import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #295: [15/2, 1/147, 130/33, 77/5, 3/91]

Vector representation:
```
-1  1  1  0  0  0
 0 -1  0 -2  0  0
 1 -1  1  0 -1  1
 0  0 -1  1  1  0
 0  1  0 -1  0 -1
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_295

def Q := ℕ × ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a+1, b, c, d, e, f⟩ => some ⟨a, b+1, c+1, d, e, f⟩
  | ⟨a, b+1, c, d+2, e, f⟩ => some ⟨a, b, c, d, e, f⟩
  | ⟨a, b+1, c, d, e+1, f⟩ => some ⟨a+1, b, c+1, d, e, f+1⟩
  | ⟨a, b, c+1, d, e, f⟩ => some ⟨a, b, c, d+1, e+1, f⟩
  | ⟨a, b, c, d+1, e, f+1⟩ => some ⟨a, b+1, c, d, e, f⟩
  | _ => none

-- Individual step lemmas
private lemma step_r4_00 (c d e f : ℕ) :
    ⟨0, 0, c + 1, d, e, f⟩ [fm]⊢ ⟨0, 0, c, d + 1, e + 1, f⟩ := by
  cases d <;> cases e <;> cases f <;> rfl

private lemma step_r5_00 (d e f : ℕ) :
    ⟨0, 0, 0, d + 1, e, f + 1⟩ [fm]⊢ ⟨0, 1, 0, d, e, f⟩ := by
  cases d <;> rfl

private lemma step_r2_0 (b d e f : ℕ) :
    ⟨0, b + 1, 0, d + 2, e, f⟩ [fm]⊢ ⟨0, b, 0, d, e, f⟩ := rfl

private lemma step_r3_0 (b c e f : ℕ) :
    ⟨0, b + 1, c, 0, e + 1, f⟩ [fm]⊢ ⟨1, b, c + 1, 0, e, f + 1⟩ := rfl

private lemma step_r1 (a b c d e f : ℕ) :
    ⟨a + 1, b, c, d, e, f⟩ [fm]⊢ ⟨a, b + 1, c + 1, d, e, f⟩ := rfl

-- R4 with b>=1: need the match to skip R2 (d<2) and R3 (e=0)
private lemma step_r4_b1_d0_e0 (b c f : ℕ) :
    ⟨0, b + 1, c + 1, 0, 0, f⟩ [fm]⊢ ⟨0, b + 1, c, 1, 1, f⟩ := by rfl

private lemma step_r3_d1 (b c e f : ℕ) :
    ⟨0, b + 1, c, 1, e + 1, f⟩ [fm]⊢ ⟨1, b, c + 1, 1, e, f + 1⟩ := rfl

private lemma step_r4_b1_d1_e0 (b c f : ℕ) :
    ⟨0, b + 1, c + 1, 1, 0, f⟩ [fm]⊢ ⟨0, b + 1, c, 2, 1, f⟩ := rfl

private lemma step_r2_d2 (b c f : ℕ) :
    ⟨0, b + 1, c, 2, 1, f⟩ [fm]⊢ ⟨0, b, c, 0, 1, f⟩ := rfl

-- R4 chain: (0,0,c+k,d,e,f) ⊢* (0,0,c,d+k,e+k,f)
theorem r4_chain (k c d e f : ℕ) :
    ⟨0, 0, c + k, d, e, f⟩ [fm]⊢* ⟨(0 : ℕ), 0, c, d + k, e + k, f⟩ := by
  induction k generalizing c d e with
  | zero => simp; finish
  | succ k ih =>
    rw [show c + (k + 1) = (c + k) + 1 from by ring]
    refine stepStar_trans (step_stepStar (step_r4_00 (c + k) d e f)) ?_
    rw [show d + (k + 1) = (d + 1) + k from by ring,
        show e + (k + 1) = (e + 1) + k from by ring]
    exact ih c (d + 1) (e + 1)

-- R5/R2 drain: (0,0,0,3k+1,e,g+k+1) ⊢* (0,1,0,0,e,g)
theorem r5r2_drain (k e g : ℕ) :
    ⟨0, 0, 0, 3 * k + 1, e, g + k + 1⟩ [fm]⊢* ⟨(0 : ℕ), 1, 0, 0, e, g⟩ := by
  induction k generalizing g with
  | zero =>
    exact step_stepStar (step_r5_00 0 e g)
  | succ k ih =>
    -- State: (0,0,0,3(k+1)+1,e,g+(k+1)+1) = (0,0,0,3k+4,e,g+k+2)
    -- R5: -> (0,1,0,3k+3,e,g+k+1)
    -- 3k+4 = (3k+3)+1, g+k+2 = (g+k+1)+1
    rw [show 3 * (k + 1) + 1 = (3 * k + 3) + 1 from by ring,
        show g + (k + 1) + 1 = (g + k + 1) + 1 from by ring]
    refine stepStar_trans (step_stepStar (step_r5_00 (3 * k + 3) e (g + k + 1))) ?_
    -- (0,1,0,3k+3,e,g+k+1), 3k+3 = (3k+1)+2
    rw [show (3 * k + 3 : ℕ) = (3 * k + 1) + 2 from by ring]
    refine stepStar_trans (step_stepStar (step_r2_0 0 (3 * k + 1) e (g + k + 1))) ?_
    -- (0,0,0,3k+1,e,g+k+1) = (0,0,0,3k+1,e,(g+1)+k)
    -- But ih expects g'+k+1 form. Let g' = g+1: need (g+1)+k+1 = g+k+1+1...
    -- Actually, ih g' gives (0,0,0,3k+1,e,g'+k+1) ⊢* (0,1,0,0,e,g')
    -- We have (0,0,0,3k+1,e,g+k+1). We need g+k+1 = g'+k+1 with g' = g, which works!
    -- Wait, that gives the wrong target. We have g+k+1 and ih expects g'+k+1.
    -- If g' = g, then ih g gives exactly what we have. But target is (0,1,0,0,e,g), which is correct!
    exact ih g

-- R3/R1 bounce: (1,0,c,0,e+k,f) ⊢* (1,0,c+2k,0,e,f+k)
theorem bounce (k c e f : ℕ) :
    ⟨1, 0, c, 0, e + k, f⟩ [fm]⊢* ⟨(1 : ℕ), 0, c + 2 * k, 0, e, f + k⟩ := by
  induction k generalizing c e f with
  | zero => simp; finish
  | succ k ih =>
    rw [show e + (k + 1) = (e + k) + 1 from by ring]
    refine stepStar_trans (step_stepStar (step_r1 0 0 c 0 ((e + k) + 1) f)) ?_
    refine stepStar_trans (step_stepStar (step_r3_0 0 (c + 1) (e + k) f)) ?_
    rw [show c + 2 * (k + 1) = (c + 2) + 2 * k from by ring,
        show f + (k + 1) = (f + 1) + k from by ring]
    exact ih (c + 2) e (f + 1)

-- Tail: (1,0,C+1,0,0,F+1) ⊢* (0,0,C+2,0,1,F+2)
theorem tail (C F : ℕ) :
    ⟨1, 0, C + 1, 0, 0, F + 1⟩ [fm]⊢* ⟨(0 : ℕ), 0, C + 2, 0, 1, F + 2⟩ := by
  refine stepStar_trans (step_stepStar (step_r1 0 0 (C + 1) 0 0 (F + 1))) ?_
  refine stepStar_trans (step_stepStar (step_r4_b1_d0_e0 0 (C + 1) (F + 1))) ?_
  refine stepStar_trans (step_stepStar (step_r3_d1 0 (C + 1) 0 (F + 1))) ?_
  refine stepStar_trans (step_stepStar (step_r1 0 0 (C + 2) 1 0 (F + 2))) ?_
  refine stepStar_trans (step_stepStar (step_r4_b1_d1_e0 0 (C + 2) (F + 2))) ?_
  exact step_stepStar (step_r2_d2 0 (C + 2) (F + 2))

-- Bootstrap
theorem bootstrap : c₀ [fm]⊢* ⟨(0 : ℕ), 0, 1, 0, 1, 1⟩ := by
  unfold c₀; execute fm 6

-- S_n = (0, 0, 3*2^n - 2, 0, 1, 2^(n+1) - 1)
-- To avoid subtraction, parametrize as: S'_n = (0, 0, 3n+1, 0, 1, 2n+1) where n := 2^k - 1
-- Or better: work with p' = 2^n - 1, so 3*2^n - 2 = 3*(p'+1) - 2 = 3p'+1
-- and 2^(n+1) - 1 = 2(p'+1) - 1 = 2p'+1
-- S_n = (0, 0, 3p'+1, 0, 1, 2p'+1) where p' = 2^n - 1

-- Cycle from (0,0,3p+1,0,1,2p+1) to (0,0,6p+4,0,1,4p+3)
theorem cycle_gen (p : ℕ) :
    ⟨0, 0, 3 * p + 1, 0, 1, 2 * p + 1⟩ [fm]⊢⁺
    ⟨(0 : ℕ), 0, 6 * p + 4, 0, 1, 4 * p + 3⟩ := by
  -- Phase 1: R4 chain of 3p+1 steps
  -- First step for stepPlus
  apply step_stepStar_stepPlus (step_r4_00 (3 * p) 0 1 (2 * p + 1))
  -- (0, 0, 3p, 1, 2, 2p+1)
  rw [show (3 * p : ℕ) = 0 + 3 * p from by ring]
  apply stepStar_trans (r4_chain (3 * p) 0 1 2 (2 * p + 1))
  -- (0, 0, 0, 3p+1, 3p+2, 2p+1)
  -- Phase 2: R5/R2 drain with k = p
  -- Need: 3p+1 = 3*p+1 ✓
  -- Need: 2p+1 = g+p+1, so g = p
  rw [show 1 + 3 * p = 3 * p + 1 from by ring,
      show 2 + 3 * p = 3 * p + 2 from by ring,
      show (2 * p + 1 : ℕ) = p + p + 1 from by ring]
  apply stepStar_trans (r5r2_drain p (3 * p + 2) p)
  -- (0, 1, 0, 0, 3p+2, p)
  -- Phase 3: R3 step
  rw [show (3 * p + 2 : ℕ) = (3 * p + 1) + 1 from by ring]
  refine stepStar_trans (step_stepStar (step_r3_0 0 0 (3 * p + 1) p)) ?_
  -- (1, 0, 1, 0, 3p+1, p+1)
  -- Phase 4: Bounce with k = 3p+1 steps
  rw [show (3 * p + 1 : ℕ) = 0 + (3 * p + 1) from by ring]
  apply stepStar_trans (bounce (3 * p + 1) 1 0 (p + 1))
  -- (1, 0, 1+2*(3p+1), 0, 0, (p+1)+(3p+1)) = (1, 0, 6p+3, 0, 0, 4p+2)
  -- Phase 5: Tail
  rw [show 1 + 2 * (3 * p + 1) = (6 * p + 2) + 1 from by ring,
      show p + 1 + (3 * p + 1) = (4 * p + 1) + 1 from by ring]
  apply stepStar_trans (tail (6 * p + 2) (4 * p + 1))
  -- (0, 0, 6p+4, 0, 1, 4p+3)
  finish

-- Now connect to the 2^n parametrization
theorem cycle (n : ℕ) :
    ⟨0, 0, 3 * 2 ^ n - 2, 0, 1, 2 ^ (n + 1) - 1⟩ [fm]⊢⁺
    ⟨(0 : ℕ), 0, 3 * 2 ^ (n + 1) - 2, 0, 1, 2 ^ (n + 2) - 1⟩ := by
  have hp : 2 ^ n ≥ 1 := Nat.one_le_pow n 2 (by omega)
  have h := cycle_gen (2 ^ n - 1)
  rw [show 3 * (2 ^ n - 1) + 1 = 3 * 2 ^ n - 2 from by omega,
      show 2 * (2 ^ n - 1) + 1 = 2 ^ (n + 1) - 1 from by rw [Nat.pow_succ]; omega,
      show 6 * (2 ^ n - 1) + 4 = 3 * 2 ^ (n + 1) - 2 from by rw [Nat.pow_succ]; omega,
      show 4 * (2 ^ n - 1) + 3 = 2 ^ (n + 2) - 1 from by
        rw [show n + 2 = (n + 1) + 1 from rfl, Nat.pow_succ, Nat.pow_succ]; omega]
    at h
  exact h

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts bootstrap
  apply progress_nonhalt_simple (fm := fm) (A := ℕ)
    (fun n ↦ ⟨0, 0, 3 * 2 ^ n - 2, 0, 1, 2 ^ (n + 1) - 1⟩) 0
  intro n
  exact ⟨n + 1, cycle n⟩

end Sz22_2003_unofficial_295
