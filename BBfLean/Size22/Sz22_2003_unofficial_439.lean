import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #439: [27/35, 5/33, 14/3, 11/7, 21/2]

Vector representation:
```
 0  3 -1 -1  0
 0 -1  1  0 -1
 1 -1  0  1  0
 0  0  0 -1  1
-1  1  0  1  0
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_439

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a, b, c+1, d+1, e⟩ => some ⟨a, b+3, c, d, e⟩
  | ⟨a, b+1, c, d, e+1⟩ => some ⟨a, b, c+1, d, e⟩
  | ⟨a, b+1, c, d, e⟩ => some ⟨a+1, b, c, d+1, e⟩
  | ⟨a, b, c, d+1, e⟩ => some ⟨a, b, c, d, e+1⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b+1, c, d+1, e⟩
  | _ => none

-- Rule 4 chain (with b=0, c=0): transfer d to e
private theorem rule4_chain : ∀ j a d e,
    (⟨a, 0, 0, d + j, e⟩ : Q) [fm]⊢* ⟨a, 0, 0, d, e + j⟩ := by
  intro j; induction j with
  | zero => intros; exists 0
  | succ j ih =>
    intro a d e
    rw [show d + (j + 1) = (d + j) + 1 from by ring]
    step fm
    apply stepStar_trans (ih a d (e + 1))
    rw [show (e + 1) + j = e + (j + 1) from by ring]; finish

-- Rule 3 chain: transfer b to a and d
private theorem rule3_chain : ∀ j a d,
    (⟨a, j, 0, d, 0⟩ : Q) [fm]⊢* ⟨a + j, 0, 0, d + j, 0⟩ := by
  intro j; induction j with
  | zero => intros; exists 0
  | succ j ih =>
    intro a d; step fm
    apply stepStar_trans (ih (a + 1) (d + 1))
    rw [show (a + 1) + j = a + (j + 1) from by ring,
        show (d + 1) + j = d + (j + 1) from by ring]; finish

-- Inner step for c = 0: 6 steps
private theorem inner_step_zero : ∀ a e,
    (⟨a + 1, 0, 0, 0, e + 4⟩ : Q) [fm]⊢* ⟨a, 0, 3, 0, e⟩ := by
  intro a e; step fm; step fm; step fm; step fm; step fm; step fm; ring_nf; finish

-- Inner step for c >= 1: 6 steps
private theorem inner_step_succ : ∀ a c e,
    (⟨a + 1, 0, c + 1, 0, e + 4⟩ : Q) [fm]⊢* ⟨a, 0, c + 4, 0, e⟩ := by
  intro a c e; step fm; step fm; step fm; step fm; step fm; step fm; ring_nf; finish

-- Inner chain starting from c = 0: j iterations
private theorem inner_chain : ∀ j a e,
    (⟨a + j, 0, 0, 0, 4 * j + e⟩ : Q) [fm]⊢* ⟨a, 0, 3 * j, 0, e⟩ := by
  intro j; induction j with
  | zero => intro a e; simp; exists 0
  | succ j ih =>
    intro a e
    rw [show a + (j + 1) = (a + 1) + j from by ring,
        show 4 * (j + 1) + e = 4 * j + (e + 4) from by ring]
    apply stepStar_trans (ih (a + 1) (e + 4))
    rcases j with _ | j
    · apply stepStar_trans (inner_step_zero a e); finish
    · rw [show 3 * (j + 1) = (3 * j + 2) + 1 from by ring]
      apply stepStar_trans (inner_step_succ a (3 * j + 2) e)
      rw [show (3 * j + 2) + 4 = 3 * (j + 1 + 1) from by ring]; finish

-- Expand step: rule3, rule1 (2 steps)
private theorem expand_step : ∀ a b c,
    (⟨a, b + 1, c + 1, 0, 0⟩ : Q) [fm]⊢* ⟨a + 1, b + 3, c, 0, 0⟩ := by
  intro a b c; step fm; step fm; ring_nf; finish

-- Expand chain: consume j units of c, b increases by 2j
private theorem expand_chain : ∀ j a b,
    (⟨a, b + 1, j, 0, 0⟩ : Q) [fm]⊢* ⟨a + j, b + 2 * j + 1, 0, 0, 0⟩ := by
  intro j; induction j with
  | zero => intro a b; simp; exists 0
  | succ j ih =>
    intro a b
    apply stepStar_trans (expand_step a b j)
    apply stepStar_trans (ih (a + 1) (b + 2))
    rw [show (a + 1) + j = a + (j + 1) from by ring,
        show (b + 2) + 2 * j + 1 = b + 2 * (j + 1) + 1 from by ring]; finish

-- Full expansion for r=0 case
-- (a+1, 0, c+1, 0, 0) -> rule5,rule1 -> (a, 4, c, 0, 0) -> expand -> rule3 chain
private theorem expansion_0 : ∀ a c,
    (⟨a + 1, 0, c + 1, 0, 0⟩ : Q) [fm]⊢* ⟨a + 3 * c + 4, 0, 0, 2 * c + 4, 0⟩ := by
  intro a c
  step fm; step fm
  apply stepStar_trans (expand_chain c a 3)
  rw [show 3 + 2 * c + 1 = 2 * c + 4 from by ring]
  apply stepStar_trans (rule3_chain (2 * c + 4) (a + c) 0)
  rw [show (a + c) + (2 * c + 4) = a + 3 * c + 4 from by ring,
      show 0 + (2 * c + 4) = 2 * c + 4 from by ring]; finish

-- Expansion init for r=2: 6 intermediate steps
-- (a+1, 0, c+1, 0, 2) -> rule5 -> rule1 -> rule2 -> rule2 -> rule3 -> rule1 -> (a+1, 4, c+1, 0, 0)
private theorem expansion_init_2 : ∀ a c,
    (⟨a + 1, 0, c + 1, 0, 2⟩ : Q) [fm]⊢* ⟨a + 1, 4, c + 1, 0, 0⟩ := by
  intro a c; step fm; step fm; step fm; step fm; step fm; step fm; ring_nf; finish

-- Full expansion for r=2 case
private theorem expansion_2 : ∀ a c,
    (⟨a + 1, 0, c + 1, 0, 2⟩ : Q) [fm]⊢* ⟨a + 3 * c + 8, 0, 0, 2 * c + 6, 0⟩ := by
  intro a c
  apply stepStar_trans (expansion_init_2 a c)
  apply stepStar_trans (expand_chain (c + 1) (a + 1) 3)
  rw [show (a + 1) + (c + 1) = a + c + 2 from by ring,
      show 3 + 2 * (c + 1) + 1 = 2 * c + 6 from by ring]
  apply stepStar_trans (rule3_chain (2 * c + 6) (a + c + 2) 0)
  rw [show (a + c + 2) + (2 * c + 6) = a + 3 * c + 8 from by ring,
      show 0 + (2 * c + 6) = 2 * c + 6 from by ring]; finish

-- Main transition for d ≡ 0 (mod 4): from (a+k+2, 0, 0, 4k+4, 0)
private theorem main_trans_mod0 (k a : ℕ) :
    (⟨a + k + 2, 0, 0, 4 * k + 4, 0⟩ : Q) [fm]⊢⁺ ⟨a + 9 * k + 10, 0, 0, 6 * k + 8, 0⟩ := by
  -- Phase 1: rule4 chain
  apply stepStar_stepPlus_stepPlus
  · rw [show (4 * k + 4 : ℕ) = 0 + (4 * k + 4) from by ring]
    exact rule4_chain (4 * k + 4) (a + k + 2) 0 0
  -- Phase 2: inner chain
  apply stepStar_stepPlus_stepPlus
  · rw [show (a + k + 2 : ℕ) = (a + 1) + (k + 1) from by ring,
        show 0 + (4 * k + 4) = 4 * (k + 1) + 0 from by ring]
    exact inner_chain (k + 1) (a + 1) 0
  -- Phase 3: expansion_0
  rw [show 3 * (k + 1) = (3 * k + 2) + 1 from by ring]
  apply step_stepStar_stepPlus
  · show fm (⟨a + 1, 0, (3 * k + 2) + 1, 0, 0⟩ : Q) = some ⟨a, 1, (3 * k + 2) + 1, 1, 0⟩; rfl
  step fm
  apply stepStar_trans (expand_chain (3 * k + 2) a 3)
  rw [show 3 + 2 * (3 * k + 2) + 1 = 6 * k + 8 from by ring]
  apply stepStar_trans (rule3_chain (6 * k + 8) (a + (3 * k + 2)) 0)
  rw [show (a + (3 * k + 2)) + (6 * k + 8) = a + 9 * k + 10 from by ring,
      show 0 + (6 * k + 8) = 6 * k + 8 from by ring]; finish

-- Main transition for d ≡ 2 (mod 4): from (a+k+2, 0, 0, 4k+6, 0)
private theorem main_trans_mod2 (k a : ℕ) :
    (⟨a + k + 2, 0, 0, 4 * k + 6, 0⟩ : Q) [fm]⊢⁺ ⟨a + 9 * k + 14, 0, 0, 6 * k + 10, 0⟩ := by
  -- Phase 1: rule4 chain
  apply stepStar_stepPlus_stepPlus
  · rw [show (4 * k + 6 : ℕ) = 0 + (4 * k + 6) from by ring]
    exact rule4_chain (4 * k + 6) (a + k + 2) 0 0
  -- Phase 2: inner chain
  apply stepStar_stepPlus_stepPlus
  · rw [show (a + k + 2 : ℕ) = (a + 1) + (k + 1) from by ring,
        show 0 + (4 * k + 6) = 4 * (k + 1) + 2 from by ring]
    exact inner_chain (k + 1) (a + 1) 2
  -- Phase 3: expansion_2
  rw [show 3 * (k + 1) = (3 * k + 2) + 1 from by ring]
  apply step_stepStar_stepPlus
  · show fm (⟨a + 1, 0, (3 * k + 2) + 1, 0, 2⟩ : Q) = some ⟨a, 1, (3 * k + 2) + 1, 1, 2⟩; rfl
  -- rule1: (a, 1, (3k+2)+1, 1, 2) -> (a, 4, 3k+2, 0, 2)
  step fm
  -- rule2, rule2: (a, 4, 3k+2, 0, 2) -> (a, 3, 3k+3, 0, 1) -> (a, 2, 3k+4, 0, 0)
  step fm; step fm
  -- rule3: (a, 2, 3k+4, 0, 0) -> (a+1, 1, 3k+4, 1, 0)
  step fm
  -- rule1: (a+1, 1, 3k+4, 1, 0) -> (a+1, 4, 3k+3, 0, 0)
  step fm
  -- now at (a+1, 4, 3k+3, 0, 0) = (a+1, 3+1, 3k+3, 0, 0)
  apply stepStar_trans (expand_chain (3 * k + 3) (a + 1) 3)
  rw [show (a + 1) + (3 * k + 3) = a + 3 * k + 4 from by ring,
      show 3 + 2 * (3 * k + 3) + 1 = 6 * k + 10 from by ring]
  apply stepStar_trans (rule3_chain (6 * k + 10) (a + 3 * k + 4) 0)
  rw [show (a + 3 * k + 4) + (6 * k + 10) = a + 9 * k + 14 from by ring,
      show 0 + (6 * k + 10) = 6 * k + 10 from by ring]; finish

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨5, 0, 0, 4, 0⟩) (by execute fm 14)
  apply progress_nonhalt (fm := fm)
    (P := fun q ↦ ∃ k a, q = (⟨a + k + 2, 0, 0, 4 * k + 4, 0⟩ : Q) ∨
                          q = (⟨a + k + 2, 0, 0, 4 * k + 6, 0⟩ : Q))
  · intro q ⟨k, a, hq⟩
    rcases hq with hq | hq
    · -- Case d = 4k + 4 (d ≡ 0 mod 4)
      subst hq
      refine ⟨⟨a + 9 * k + 10, 0, 0, 6 * k + 8, 0⟩, ?_, main_trans_mod0 k a⟩
      rcases Nat.even_or_odd k with ⟨m, hm⟩ | ⟨m, hm⟩
      · -- k = 2m: 6k+8 = 12m+8 = 4(3m+1)+4
        exact ⟨3 * m + 1, a + 15 * m + 7, Or.inl (by subst hm; ring_nf)⟩
      · -- k = 2m+1: 6k+8 = 12m+14 = 4(3m+2)+6
        exact ⟨3 * m + 2, a + 15 * m + 15, Or.inr (by subst hm; ring_nf)⟩
    · -- Case d = 4k + 6 (d ≡ 2 mod 4)
      subst hq
      refine ⟨⟨a + 9 * k + 14, 0, 0, 6 * k + 10, 0⟩, ?_, main_trans_mod2 k a⟩
      rcases Nat.even_or_odd k with ⟨m, hm⟩ | ⟨m, hm⟩
      · -- k = 2m: 6k+10 = 12m+10 = 4(3m+1)+6
        exact ⟨3 * m + 1, a + 15 * m + 11, Or.inr (by subst hm; ring_nf)⟩
      · -- k = 2m+1: 6k+10 = 12m+16 = 4(3m+3)+4
        exact ⟨3 * m + 3, a + 15 * m + 18, Or.inl (by subst hm; ring_nf)⟩
  · -- Initial: (5, 0, 0, 4, 0) = (3+0+2, 0, 0, 4*0+4, 0)
    exact ⟨0, 3, Or.inl rfl⟩

end Sz22_2003_unofficial_439
