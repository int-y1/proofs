import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #131: [1/45, 125/77, 98/5, 3/7, 55/2]

Vector representation:
```
 0 -2 -1  0  0
 0  0  3 -1 -1
 1  0 -1  2  0
 0  1  0 -1  0
-1  0  1  0  1
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_131

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a, b+2, c+1, d, e⟩ => some ⟨a, b, c, d, e⟩
  | ⟨a, b, c, d+1, e+1⟩ => some ⟨a, b, c+3, d, e⟩
  | ⟨a, b, c+1, d, e⟩ => some ⟨a+1, b, c, d+2, e⟩
  | ⟨a, b, c, d+1, e⟩ => some ⟨a, b+1, c, d, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b, c+1, d, e+1⟩
  | _ => none

-- Helper: R5 fires when c=0, d=0. Need case split on b to help the match evaluator.
theorem r5_cd0 : ∀ a b e,
    fm ⟨a+1, b, 0, 0, e⟩ = some ⟨a, b, 1, 0, e+1⟩ := by
  intro a b e
  rcases b with _ | _ | b <;> rfl

theorem r5r1_one : ∀ a b e,
    ⟨a+1, b+2, 0, 0, e⟩ [fm]⊢* ⟨a, b, 0, 0, e+1⟩ := by
  intro a b e; step fm; step fm; finish

theorem r5r1_chain : ∀ k a b e,
    ⟨a+k, b+2*k, 0, 0, e⟩ [fm]⊢* ⟨a, b, 0, 0, e+k⟩ := by
  intro k; induction' k with k ih <;> intro a b e
  · exists 0
  rw [show a + (k + 1) = (a + k) + 1 from by ring,
      show b + 2 * (k + 1) = (b + 2 * k) + 2 from by ring]
  apply stepStar_trans (r5r1_one _ _ _)
  apply stepStar_trans (ih _ _ _)
  ring_nf; finish

theorem r5_r3_b0 : ∀ a e,
    ⟨a+1, 0, 0, 0, e⟩ [fm]⊢* ⟨a+1, 0, 0, 2, e+1⟩ := by
  intro a e; step fm; step fm; finish

theorem r5_r3_b1 : ∀ a e,
    ⟨a+1, 1, 0, 0, e⟩ [fm]⊢* ⟨a+1, 1, 0, 2, e+1⟩ := by
  intro a e; step fm; step fm; finish

theorem r2r2r3_step_b0 : ∀ a c e,
    ⟨a, 0, c, 2, e+2⟩ [fm]⊢* ⟨a+1, 0, c+5, 2, e⟩ := by
  intro a c e
  step fm; step fm
  show ⟨a, 0, c + 3 + 3, 0, e⟩ [fm]⊢* _
  rw [show c + 3 + 3 = (c + 5) + 1 from by ring]
  step fm; finish

theorem r2r2r3_step_b1 : ∀ a c e,
    ⟨a, 1, c, 2, e+2⟩ [fm]⊢* ⟨a+1, 1, c+5, 2, e⟩ := by
  intro a c e
  step fm; step fm
  show ⟨a, 1, c + 3 + 3, 0, e⟩ [fm]⊢* _
  rw [show c + 3 + 3 = (c + 5) + 1 from by ring]
  step fm; finish

theorem r2r2r3_chain_b0 : ∀ m a c e,
    ⟨a, 0, c, 2, e+2*m⟩ [fm]⊢* ⟨a+m, 0, c+5*m, 2, e⟩ := by
  intro m; induction' m with m ih <;> intro a c e
  · exists 0
  rw [show e + 2 * (m + 1) = (e + 2 * m) + 2 from by ring]
  apply stepStar_trans (r2r2r3_step_b0 a c (e + 2 * m))
  apply stepStar_trans (ih _ _ _)
  ring_nf; finish

theorem r2r2r3_chain_b1 : ∀ m a c e,
    ⟨a, 1, c, 2, e+2*m⟩ [fm]⊢* ⟨a+m, 1, c+5*m, 2, e⟩ := by
  intro m; induction' m with m ih <;> intro a c e
  · exists 0
  rw [show e + 2 * (m + 1) = (e + 2 * m) + 2 from by ring]
  apply stepStar_trans (r2r2r3_step_b1 a c (e + 2 * m))
  apply stepStar_trans (ih _ _ _)
  ring_nf; finish

theorem r3_chain_b0 : ∀ k a d,
    ⟨a, 0, k, d, 0⟩ [fm]⊢* ⟨a+k, 0, 0, d+2*k, 0⟩ := by
  intro k; induction' k with k ih <;> intro a d
  · exists 0
  show ⟨a, 0, k + 1, d, 0⟩ [fm]⊢* _
  step fm
  apply stepStar_trans (ih _ _)
  ring_nf; finish

theorem r3_chain_b1 : ∀ k a d,
    ⟨a, 1, k, d, 0⟩ [fm]⊢* ⟨a+k, 1, 0, d+2*k, 0⟩ := by
  intro k; induction' k with k ih <;> intro a d
  · exists 0
  show ⟨a, 1, k + 1, d, 0⟩ [fm]⊢* _
  step fm
  apply stepStar_trans (ih _ _)
  ring_nf; finish

theorem r4_chain : ∀ k a b,
    ⟨a, b, 0, k, 0⟩ [fm]⊢* ⟨a, b+k, 0, 0, 0⟩ := by
  intro k; induction' k with k ih <;> intro a b
  · exists 0
  show ⟨a, b, 0, k + 1, 0⟩ [fm]⊢* _
  step fm
  apply stepStar_trans (ih _ _)
  ring_nf; finish

theorem terminal_e1_b0 : ∀ a c,
    ⟨a, 0, c, 2, 1⟩ [fm]⊢* ⟨a+c+3, 0, 0, 2*c+7, 0⟩ := by
  intro a c
  step fm
  show ⟨a, 0, c + 3, 1, 0⟩ [fm]⊢* _
  apply stepStar_trans (r3_chain_b0 (c+3) a 1)
  ring_nf; finish

theorem terminal_e1_b1 : ∀ a c,
    ⟨a, 1, c, 2, 1⟩ [fm]⊢* ⟨a+c+3, 1, 0, 2*c+7, 0⟩ := by
  intro a c
  step fm
  show ⟨a, 1, c + 3, 1, 0⟩ [fm]⊢* _
  apply stepStar_trans (r3_chain_b1 (c+3) a 1)
  ring_nf; finish

theorem terminal_e0_b0 : ∀ a c,
    ⟨a, 0, c+1, 2, 0⟩ [fm]⊢* ⟨a+c+1, 0, 0, 2*c+4, 0⟩ := by
  intro a c
  apply stepStar_trans (r3_chain_b0 (c+1) a 2)
  ring_nf; finish

theorem terminal_e0_b1 : ∀ a c,
    ⟨a, 1, c+1, 2, 0⟩ [fm]⊢* ⟨a+c+1, 1, 0, 2*c+4, 0⟩ := by
  intro a c
  apply stepStar_trans (r3_chain_b1 (c+1) a 2)
  ring_nf; finish

theorem middle_b0_odd (m a : ℕ) :
    ⟨a, 0, 0, 2, 2*m+1⟩ [fm]⊢* ⟨a+6*m+3, 0, 0, 10*m+7, 0⟩ := by
  rw [show 2*m+1 = 1 + 2*m from by ring]
  apply stepStar_trans (r2r2r3_chain_b0 m a 0 1)
  rw [show 0 + 5 * m = 5 * m from by ring]
  apply stepStar_trans (terminal_e1_b0 (a+m) (5*m))
  ring_nf; finish

theorem middle_b0_even_succ (m a : ℕ) :
    ⟨a, 0, 0, 2, 2*(m+1)⟩ [fm]⊢* ⟨a+6*(m+1), 0, 0, 10*(m+1)+2, 0⟩ := by
  rw [show 2*(m+1) = 0 + 2*(m+1) from by ring]
  apply stepStar_trans (r2r2r3_chain_b0 (m+1) a 0 0)
  rw [show 0 + 5 * (m + 1) = (5*m+4) + 1 from by ring]
  apply stepStar_trans (terminal_e0_b0 (a+(m+1)) (5*m+4))
  ring_nf; finish

theorem middle_b1_odd (m a : ℕ) :
    ⟨a, 1, 0, 2, 2*m+1⟩ [fm]⊢* ⟨a+6*m+3, 1, 0, 10*m+7, 0⟩ := by
  rw [show 2*m+1 = 1 + 2*m from by ring]
  apply stepStar_trans (r2r2r3_chain_b1 m a 0 1)
  rw [show 0 + 5 * m = 5 * m from by ring]
  apply stepStar_trans (terminal_e1_b1 (a+m) (5*m))
  ring_nf; finish

theorem middle_b1_even_succ (m a : ℕ) :
    ⟨a, 1, 0, 2, 2*(m+1)⟩ [fm]⊢* ⟨a+6*(m+1), 1, 0, 10*(m+1)+2, 0⟩ := by
  rw [show 2*(m+1) = 0 + 2*(m+1) from by ring]
  apply stepStar_trans (r2r2r3_chain_b1 (m+1) a 0 0)
  rw [show 0 + 5 * (m + 1) = (5*m+4) + 1 from by ring]
  apply stepStar_trans (terminal_e0_b1 (a+(m+1)) (5*m+4))
  ring_nf; finish

-- Whole stepStar part of b0_keven: (a+2j+1, 4j, 0,0,0) →* (a+6j+4, 10j+7, 0,0,0)
-- We split off the first step separately to get stepPlus.
theorem main_star_b0_keven (j a : ℕ) :
    ⟨a+2*j, 4*j, 1, 0, 1⟩ [fm]⊢* ⟨a+6*j+4, 10*j+7, 0, 0, 0⟩ := by
  rcases j with _ | j
  · -- j=0: (a, 0, 1, 0, 1). R3: (a+1, 0, 0, 2, 1).
    simp
    step fm -- R3: (a+1, 0, 0, 2, 1)
    apply stepStar_trans (terminal_e1_b0 (a+1) 0)
    simp
    apply stepStar_trans (r4_chain 7 (a+4) 0)
    ring_nf; finish
  · -- j >= 1: (a+2j+2, 4j+4, 1, 0, 1). R1 fires (b=4j+4 >= 2, c=1 >= 1).
    rw [show a + 2 * (j + 1) = a + 2 * j + 2 from by ring,
        show 4 * (j + 1) = (4 * j + 2) + 2 from by ring]
    step fm -- R1: (a+2j+2, 4j+2, 0, 0, 1)
    -- Now continue with R5/R1 chain for 2j+1 remaining pairs... but c=0, d=0, e=1.
    -- Actually the state is (a+2j+2, 4j+2, 0, 0, 1).
    -- R5/R1 chain from here: drain pairs. But e=1, not 0. R5 fires on (a+2j+2, 4j+2, 0, 0, 1).
    -- Actually our r5r1_chain works with any e.
    rw [show a + 2 * j + 2 = (a + 1) + (2 * j + 1) from by ring,
        show 4 * j + 2 = 0 + 2 * (2 * j + 1) from by ring]
    apply stepStar_trans (r5r1_chain (2*j+1) (a+1) 0 1)
    rw [show 1 + (2 * j + 1) = 2 * j + 2 from by ring]
    apply stepStar_trans (r5_r3_b0 a (2*j+2))
    rw [show 2 * j + 2 + 1 = 2 * (j + 1) + 1 from by ring]
    apply stepStar_trans (middle_b0_odd (j+1) (a+1))
    apply stepStar_trans (r4_chain (10*(j+1)+7) (a+1+6*(j+1)+3) 0)
    ring_nf; finish

theorem main_trans_b0_keven (j a : ℕ) :
    ⟨a+2*j+1, 4*j, 0, 0, 0⟩ [fm]⊢⁺ ⟨a+6*j+4, 10*j+7, 0, 0, 0⟩ := by
  apply step_stepStar_stepPlus
  · show fm ⟨(a + 2 * j) + 1, 4 * j, 0, 0, 0⟩ = some ⟨a + 2 * j, 4 * j, 1, 0, 1⟩
    exact r5_cd0 _ _ _
  · exact main_star_b0_keven j a

-- For b0_kodd: (a+2j+2, 4j+2, 0,0,0) → R5 → (a+2j+1, 4j+2, 1, 0, 1)
theorem main_star_b0_kodd (j a : ℕ) :
    ⟨a+2*j+1, 4*j+2, 1, 0, 1⟩ [fm]⊢* ⟨a+6*j+7, 10*j+12, 0, 0, 0⟩ := by
  -- R1: b=4j+2 >= 2, c=1 >= 1. R1 fires.
  rw [show 4 * j + 2 = (4 * j) + 2 from by ring]
  step fm -- R1: (a+2j+1, 4j, 0, 0, 1)
  -- Now R5/R1 chain for 2j pairs: (a+2j+1, 4j, 0, 0, 1) → (a+1, 0, 0, 0, 2j+1)
  rw [show a + 2 * j + 1 = (a + 1) + 2 * j from by ring,
      show 4 * j = 0 + 2 * (2 * j) from by ring]
  apply stepStar_trans (r5r1_chain (2*j) (a+1) 0 1)
  rw [show 1 + 2 * j = 2 * j + 1 from by ring]
  apply stepStar_trans (r5_r3_b0 a (2*j+1))
  rw [show 2 * j + 1 + 1 = 2 * (j + 1) from by ring]
  apply stepStar_trans (middle_b0_even_succ j (a+1))
  apply stepStar_trans (r4_chain (10*(j+1)+2) (a+1+6*(j+1)) 0)
  ring_nf; finish

theorem main_trans_b0_kodd (j a : ℕ) :
    ⟨a+2*j+2, 4*j+2, 0, 0, 0⟩ [fm]⊢⁺ ⟨a+6*j+7, 10*j+12, 0, 0, 0⟩ := by
  apply step_stepStar_stepPlus
  · show fm ⟨(a + 2 * j + 1) + 1, 4 * j + 2, 0, 0, 0⟩ = some ⟨a + 2 * j + 1, 4 * j + 2, 1, 0, 1⟩
    exact r5_cd0 _ _ _
  · exact main_star_b0_kodd j a

-- For b1_keven: (a+2j+1, 4j+1, 0,0,0) → R5 → (a+2j, 4j+1, 1, 0, 1)
theorem main_star_b1_keven (j a : ℕ) :
    ⟨a+2*j, 4*j+1, 1, 0, 1⟩ [fm]⊢* ⟨a+6*j+4, 10*j+8, 0, 0, 0⟩ := by
  rcases j with _ | j
  · -- j=0: (a, 1, 1, 0, 1). R3: (a+1, 1, 0, 2, 1).
    simp
    step fm -- R3: (a+1, 1, 0, 2, 1)
    apply stepStar_trans (terminal_e1_b1 (a+1) 0)
    simp
    apply stepStar_trans (r4_chain 7 (a+4) 1)
    ring_nf; finish
  · -- j >= 1: (a+2j+2, 4j+5, 1, 0, 1). R1: b=4j+5 >= 2, c=1 >= 1.
    -- But wait: 4*(j+1)+1 = 4j+5. And the state is (a+2*(j+1), 4*(j+1)+1, 1, 0, 1).
    rw [show a + 2 * (j + 1) = a + 2 * j + 2 from by ring,
        show 4 * (j + 1) + 1 = (4 * j + 3) + 2 from by ring]
    step fm -- R1
    rw [show a + 2 * j + 2 = (a + 1) + (2 * j + 1) from by ring,
        show 4 * j + 3 = 1 + 2 * (2 * j + 1) from by ring]
    apply stepStar_trans (r5r1_chain (2*j+1) (a+1) 1 1)
    rw [show 1 + (2 * j + 1) = 2 * j + 2 from by ring]
    apply stepStar_trans (r5_r3_b1 a (2*j+2))
    rw [show 2 * j + 2 + 1 = 2 * (j + 1) + 1 from by ring]
    apply stepStar_trans (middle_b1_odd (j+1) (a+1))
    apply stepStar_trans (r4_chain (10*(j+1)+7) (a+1+6*(j+1)+3) 1)
    ring_nf; finish

theorem main_trans_b1_keven (j a : ℕ) :
    ⟨a+2*j+1, 4*j+1, 0, 0, 0⟩ [fm]⊢⁺ ⟨a+6*j+4, 10*j+8, 0, 0, 0⟩ := by
  apply step_stepStar_stepPlus
  · show fm ⟨(a + 2 * j) + 1, 4 * j + 1, 0, 0, 0⟩ = some ⟨a + 2 * j, 4 * j + 1, 1, 0, 1⟩
    exact r5_cd0 _ _ _
  · exact main_star_b1_keven j a

-- For b1_kodd: (a+2j+2, 4j+3, 0,0,0) → R5 → (a+2j+1, 4j+3, 1, 0, 1)
theorem main_star_b1_kodd (j a : ℕ) :
    ⟨a+2*j+1, 4*j+3, 1, 0, 1⟩ [fm]⊢* ⟨a+6*j+7, 10*j+13, 0, 0, 0⟩ := by
  -- R1: b=4j+3 >= 2, c=1. R1 fires.
  rw [show 4 * j + 3 = (4 * j + 1) + 2 from by ring]
  step fm -- R1: (a+2j+1, 4j+1, 0, 0, 1)
  rw [show a + 2 * j + 1 = (a + 1) + 2 * j from by ring,
      show 4 * j + 1 = 1 + 2 * (2 * j) from by ring]
  apply stepStar_trans (r5r1_chain (2*j) (a+1) 1 1)
  rw [show 1 + 2 * j = 2 * j + 1 from by ring]
  apply stepStar_trans (r5_r3_b1 a (2*j+1))
  rw [show 2 * j + 1 + 1 = 2 * (j + 1) from by ring]
  apply stepStar_trans (middle_b1_even_succ j (a+1))
  apply stepStar_trans (r4_chain (10*(j+1)+2) (a+1+6*(j+1)) 1)
  ring_nf; finish

theorem main_trans_b1_kodd (j a : ℕ) :
    ⟨a+2*j+2, 4*j+3, 0, 0, 0⟩ [fm]⊢⁺ ⟨a+6*j+7, 10*j+13, 0, 0, 0⟩ := by
  apply step_stepStar_stepPlus
  · show fm ⟨(a + 2 * j + 1) + 1, 4 * j + 3, 0, 0, 0⟩ = some ⟨a + 2 * j + 1, 4 * j + 3, 1, 0, 1⟩
    exact r5_cd0 _ _ _
  · exact main_star_b1_kodd j a

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨4, 7, 0, 0, 0⟩) (by execute fm 13)
  apply progress_nonhalt (fun q ↦ ∃ a b, q = (⟨a, b, 0, 0, 0⟩ : Q) ∧ a ≥ 4 ∧ 2*a > b)
  · intro q ⟨a, b, hq, ha, hab⟩
    subst hq
    rcases Nat.even_or_odd b with ⟨k, hk⟩ | ⟨k, hk⟩
    · -- b = 2k
      rcases Nat.even_or_odd k with ⟨j, hj⟩ | ⟨j, hj⟩
      · -- k = 2j, b = 4j
        have hb : b = 4 * j := by omega
        subst hb
        refine ⟨⟨a - 2*j - 1 + 6*j + 4, 10*j+7, 0, 0, 0⟩,
                ⟨a - 2*j - 1 + 6*j + 4, 10*j+7, rfl, by omega, by omega⟩, ?_⟩
        have h := main_trans_b0_keven j (a - 2*j - 1)
        rw [show a - 2 * j - 1 + 2 * j + 1 = a from by omega] at h
        exact h
      · -- k = 2j+1, b = 4j+2
        have hb : b = 4 * j + 2 := by omega
        subst hb
        refine ⟨⟨a - 2*j - 2 + 6*j + 7, 10*j+12, 0, 0, 0⟩,
                ⟨a - 2*j - 2 + 6*j + 7, 10*j+12, rfl, by omega, by omega⟩, ?_⟩
        have h := main_trans_b0_kodd j (a - 2*j - 2)
        rw [show a - 2 * j - 2 + 2 * j + 2 = a from by omega] at h
        exact h
    · -- b = 2k+1
      rcases Nat.even_or_odd k with ⟨j, hj⟩ | ⟨j, hj⟩
      · -- k = 2j, b = 4j+1
        have hb : b = 4 * j + 1 := by omega
        subst hb
        refine ⟨⟨a - 2*j - 1 + 6*j + 4, 10*j+8, 0, 0, 0⟩,
                ⟨a - 2*j - 1 + 6*j + 4, 10*j+8, rfl, by omega, by omega⟩, ?_⟩
        have h := main_trans_b1_keven j (a - 2*j - 1)
        rw [show a - 2 * j - 1 + 2 * j + 1 = a from by omega] at h
        exact h
      · -- k = 2j+1, b = 4j+3
        have hb : b = 4 * j + 3 := by omega
        subst hb
        refine ⟨⟨a - 2*j - 2 + 6*j + 7, 10*j+13, 0, 0, 0⟩,
                ⟨a - 2*j - 2 + 6*j + 7, 10*j+13, rfl, by omega, by omega⟩, ?_⟩
        have h := main_trans_b1_kodd j (a - 2*j - 2)
        rw [show a - 2 * j - 2 + 2 * j + 2 = a from by omega] at h
        exact h
  · exact ⟨4, 7, rfl, by omega, by omega⟩

end Sz22_2003_unofficial_131
