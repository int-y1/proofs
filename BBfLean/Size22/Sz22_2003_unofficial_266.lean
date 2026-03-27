import BBfLean.FM

/-!
# sz22_2003_unofficial #266: [14/15, 1/847, 54/7, 11/3, 35/2]

Vector representation:
```
 1 -1 -1  1  0
 0  0  0 -1 -2
 1  3  0 -1  0
 0 -1  0  0  1
-1  0  1  1  0
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_266

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a, b+1, c+1, d, e⟩ => some ⟨a+1, b, c, d+1, e⟩
  | ⟨a, b, c, d+1, e+2⟩ => some ⟨a, b, c, d, e⟩
  | ⟨a, b, c, d+1, e⟩ => some ⟨a+1, b+3, c, d, e⟩
  | ⟨a, b+1, c, d, e⟩ => some ⟨a, b, c, d, e+1⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b, c+1, d+1, e⟩
  | _ => none

-- R3 loop (e=0): k steps of rule 3 with c=0
theorem r3_loop_0 : ∀ k a b d,
    ⟨a, b, 0, k + d, 0⟩ [fm]⊢* ⟨a + k, b + 3 * k, 0, d, 0⟩ := by
  intro k; induction k with
  | zero => intros; simp; finish
  | succ k ih =>
    intro a b d
    rw [show (k + 1) + d = (k + d) + 1 from by omega]
    step fm
    apply stepStar_trans (ih (a + 1) (b + 3) d)
    rw [show a + 1 + k = a + (k + 1) from by omega,
        show b + 3 + 3 * k = b + 3 * (k + 1) from by omega]
    finish

-- R3 loop (e=1): k steps of rule 3 with c=0
theorem r3_loop_1 : ∀ k a b d,
    ⟨a, b, 0, k + d, 1⟩ [fm]⊢* ⟨a + k, b + 3 * k, 0, d, 1⟩ := by
  intro k; induction k with
  | zero => intros; simp; finish
  | succ k ih =>
    intro a b d
    rw [show (k + 1) + d = (k + d) + 1 from by omega]
    step fm
    apply stepStar_trans (ih (a + 1) (b + 3) d)
    rw [show a + 1 + k = a + (k + 1) from by omega,
        show b + 3 + 3 * k = b + 3 * (k + 1) from by omega]
    finish

-- R4 loop: convert b to e
theorem r4_loop : ∀ k a e,
    ⟨a, k, 0, 0, e⟩ [fm]⊢* ⟨a, 0, 0, 0, e + k⟩ := by
  intro k; induction k with
  | zero => intros; simp; finish
  | succ k ih =>
    intro a e
    show ⟨a, k + 1, 0, 0, e⟩ [fm]⊢* ⟨a, 0, 0, 0, e + (k + 1)⟩
    step fm
    apply stepStar_trans (ih a (e + 1))
    rw [show e + 1 + k = e + (k + 1) from by omega]
    finish

-- R5+R2 loop: k pairs of (R5, R2)
theorem r52_loop : ∀ k a c e,
    ⟨k + a, 0, c, 0, 2 * k + e⟩ [fm]⊢* ⟨a, 0, c + k, 0, e⟩ := by
  intro k; induction k with
  | zero => intros; simp; finish
  | succ k ih =>
    intro a c e
    rw [show (k + 1) + a = (k + a) + 1 from by omega,
        show 2 * (k + 1) + e = (2 * k + e) + 2 from by omega]
    step fm  -- R5
    step fm  -- R2
    apply stepStar_trans (ih a (c + 1) e)
    rw [show c + 1 + k = c + (k + 1) from by omega]
    finish

-- Mixed R1/R3 phase with e=0.
-- From (a, 3, C, D, 0), interleaved R1 bursts and R3 restocks produce
-- (a + 2*C + D, 3 + 2*C + 3*D, 0, 0, 0).
-- Proof by strong induction on C with step size 3.
-- C=0: just R3 loop D times.
-- C=1: R1 once, then R3 loop (D+1) times.
-- C=2: R1 twice, then R3 loop (D+2) times.
-- C+3: R1 x3 (b goes to 0), R3 once (b restocks to 3), recurse with C, D+2.
theorem mixed_0 : ∀ C, ∀ D a,
    ⟨a, 3, C, D, 0⟩ [fm]⊢* ⟨a + 2 * C + D, 3 + 2 * C + 3 * D, 0, 0, 0⟩ := by
  intro C
  induction C using Nat.strongRecOn with
  | _ C ih =>
  intro D a
  match C with
  | 0 =>
    simp only [Nat.mul_zero, Nat.add_zero]
    show ⟨a, 3, 0, D + 0, 0⟩ [fm]⊢* ⟨a + D, 3 + 3 * D, 0, 0, 0⟩
    exact r3_loop_0 D a 3 0
  | 1 =>
    show ⟨a, 3, 1, D, 0⟩ [fm]⊢* ⟨a + 2 + D, 5 + 3 * D, 0, 0, 0⟩
    step fm  -- R1: (a+1, 2, 0, D+1, 0)
    show ⟨a + 1, 2, 0, (D + 1) + 0, 0⟩ [fm]⊢* ⟨a + 2 + D, 5 + 3 * D, 0, 0, 0⟩
    apply stepStar_trans (r3_loop_0 (D + 1) (a + 1) 2 0)
    rw [show a + 1 + (D + 1) = a + 2 + D from by omega,
        show 2 + 3 * (D + 1) = 5 + 3 * D from by omega]
    finish
  | 2 =>
    show ⟨a, 3, 2, D, 0⟩ [fm]⊢* ⟨a + 4 + D, 7 + 3 * D, 0, 0, 0⟩
    step fm; step fm  -- R1 x2: (a+2, 1, 0, D+2, 0)
    show ⟨a + 1 + 1, 1, 0, (D + 2) + 0, 0⟩ [fm]⊢* ⟨a + 4 + D, 7 + 3 * D, 0, 0, 0⟩
    apply stepStar_trans (r3_loop_0 (D + 2) (a + 1 + 1) 1 0)
    rw [show a + 1 + 1 + (D + 2) = a + 4 + D from by omega,
        show 1 + 3 * (D + 2) = 7 + 3 * D from by omega]
    finish
  | (C + 3) =>
    show ⟨a, 3, C + 3, D, 0⟩ [fm]⊢* ⟨a + 2 * (C + 3) + D, 3 + 2 * (C + 3) + 3 * D, 0, 0, 0⟩
    -- R1 x3: (a+3, 0, C, D+3, 0)
    step fm; step fm; step fm
    -- R3 x1 (b=0, c=C, d=D+3, e=0): -> (a+4, 3, C, D+2, 0)
    show ⟨a + 1 + 1 + 1, 0, C, D + 1 + 1 + 1, 0⟩ [fm]⊢*
      ⟨a + 2 * (C + 3) + D, 3 + 2 * (C + 3) + 3 * D, 0, 0, 0⟩
    rw [show D + 1 + 1 + 1 = (D + 2) + 1 from by omega]
    step fm  -- R3
    show ⟨a + 1 + 1 + 1 + 1, 0 + 3, C, D + 2, 0⟩ [fm]⊢*
      ⟨a + 2 * (C + 3) + D, 3 + 2 * (C + 3) + 3 * D, 0, 0, 0⟩
    rw [show a + 1 + 1 + 1 + 1 = a + 4 from by omega, show (0 : ℕ) + 3 = 3 from by omega]
    apply stepStar_trans (ih C (by omega) (D + 2) (a + 4))
    rw [show a + 4 + 2 * C + (D + 2) = a + 2 * (C + 3) + D from by omega,
        show 3 + 2 * C + 3 * (D + 2) = 3 + 2 * (C + 3) + 3 * D from by omega]
    finish

-- Mixed R1/R3 phase with e=1 (same structure)
theorem mixed_1 : ∀ C, ∀ D a,
    ⟨a, 3, C, D, 1⟩ [fm]⊢* ⟨a + 2 * C + D, 3 + 2 * C + 3 * D, 0, 0, 1⟩ := by
  intro C
  induction C using Nat.strongRecOn with
  | _ C ih =>
  intro D a
  match C with
  | 0 =>
    simp only [Nat.mul_zero, Nat.add_zero]
    show ⟨a, 3, 0, D + 0, 1⟩ [fm]⊢* ⟨a + D, 3 + 3 * D, 0, 0, 1⟩
    exact r3_loop_1 D a 3 0
  | 1 =>
    show ⟨a, 3, 1, D, 1⟩ [fm]⊢* ⟨a + 2 + D, 5 + 3 * D, 0, 0, 1⟩
    step fm
    show ⟨a + 1, 2, 0, (D + 1) + 0, 1⟩ [fm]⊢* ⟨a + 2 + D, 5 + 3 * D, 0, 0, 1⟩
    apply stepStar_trans (r3_loop_1 (D + 1) (a + 1) 2 0)
    rw [show a + 1 + (D + 1) = a + 2 + D from by omega,
        show 2 + 3 * (D + 1) = 5 + 3 * D from by omega]
    finish
  | 2 =>
    show ⟨a, 3, 2, D, 1⟩ [fm]⊢* ⟨a + 4 + D, 7 + 3 * D, 0, 0, 1⟩
    step fm; step fm
    show ⟨a + 1 + 1, 1, 0, (D + 2) + 0, 1⟩ [fm]⊢* ⟨a + 4 + D, 7 + 3 * D, 0, 0, 1⟩
    apply stepStar_trans (r3_loop_1 (D + 2) (a + 1 + 1) 1 0)
    rw [show a + 1 + 1 + (D + 2) = a + 4 + D from by omega,
        show 1 + 3 * (D + 2) = 7 + 3 * D from by omega]
    finish
  | (C + 3) =>
    show ⟨a, 3, C + 3, D, 1⟩ [fm]⊢* ⟨a + 2 * (C + 3) + D, 3 + 2 * (C + 3) + 3 * D, 0, 0, 1⟩
    step fm; step fm; step fm
    show ⟨a + 1 + 1 + 1, 0, C, D + 1 + 1 + 1, 1⟩ [fm]⊢*
      ⟨a + 2 * (C + 3) + D, 3 + 2 * (C + 3) + 3 * D, 0, 0, 1⟩
    rw [show D + 1 + 1 + 1 = (D + 2) + 1 from by omega]
    step fm
    show ⟨a + 1 + 1 + 1 + 1, 0 + 3, C, D + 2, 1⟩ [fm]⊢*
      ⟨a + 2 * (C + 3) + D, 3 + 2 * (C + 3) + 3 * D, 0, 0, 1⟩
    rw [show a + 1 + 1 + 1 + 1 = a + 4 from by omega, show (0 : ℕ) + 3 = 3 from by omega]
    apply stepStar_trans (ih C (by omega) (D + 2) (a + 4))
    rw [show a + 4 + 2 * C + (D + 2) = a + 2 * (C + 3) + D from by omega,
        show 3 + 2 * C + 3 * (D + 2) = 3 + 2 * (C + 3) + 3 * D from by omega]
    finish

-- Main cycle: (a, 0, c+1, 1, 0) ->+ (a + 2*c + 1, 0, c + 6, 1, 0)
theorem cycle (a c : ℕ) :
    ⟨a, 0, c + 1, 1, 0⟩ [fm]⊢⁺ ⟨a + 2 * c + 1, 0, c + 6, 1, 0⟩ := by
  -- R3: -> (a+1, 3, c+1, 0, 0)
  step fm
  -- Mixed e=0: -> (a+2c+3, 2c+5, 0, 0, 0)
  apply stepStar_trans (mixed_0 (c + 1) 0 (a + 1))
  rw [show a + 1 + 2 * (c + 1) + 0 = a + 2 * c + 3 from by omega,
      show 3 + 2 * (c + 1) + 3 * 0 = 2 * c + 5 from by omega]
  -- R4 loop: -> (a+2c+3, 0, 0, 0, 2c+5)
  apply stepStar_trans (r4_loop (2 * c + 5) (a + 2 * c + 3) 0)
  rw [show 0 + (2 * c + 5) = 2 * c + 5 from by omega]
  -- R5+R2 loop (c+1 pairs): -> (a+c+2, 0, c+1, 0, 3)
  show ⟨a + 2 * c + 3, 0, 0, 0, 2 * c + 5⟩ [fm]⊢* ⟨a + 2 * c + 1, 0, c + 6, 1, 0⟩
  rw [show a + 2 * c + 3 = (c + 1) + (a + c + 2) from by omega,
      show 2 * c + 5 = 2 * (c + 1) + 3 from by omega]
  apply stepStar_trans (r52_loop (c + 1) (a + c + 2) 0 3)
  rw [show 0 + (c + 1) = c + 1 from by omega]
  -- R5: (a+c+2, 0, c+1, 0, 3) -> (a+c+1, 0, c+2, 1, 3)
  show ⟨a + c + 2, 0, c + 1, 0, 3⟩ [fm]⊢* ⟨a + 2 * c + 1, 0, c + 6, 1, 0⟩
  rw [show a + c + 2 = (a + c + 1) + 1 from by omega]
  step fm  -- R5
  -- R2: (a+c+1, 0, c+2, 1, 3) -> (a+c+1, 0, c+2, 0, 1)
  step fm  -- R2
  -- R5: (a+c+1, 0, c+2, 0, 1) -> (a+c, 0, c+3, 1, 1)
  rw [show a + c + 1 = (a + c) + 1 from by omega]
  step fm  -- R5
  -- R3: (a+c, 0, c+3, 1, 1) -> (a+c+1, 3, c+3, 0, 1)
  step fm  -- R3
  -- Mixed e=1: -> (a+3c+7, 2c+9, 0, 0, 1)
  apply stepStar_trans (mixed_1 (c + 3) 0 (a + c + 1))
  rw [show a + c + 1 + 2 * (c + 3) + 0 = a + 3 * c + 7 from by omega,
      show 3 + 2 * (c + 3) + 3 * 0 = 2 * c + 9 from by omega]
  -- R4 loop: -> (a+3c+7, 0, 0, 0, 2c+10)
  apply stepStar_trans (r4_loop (2 * c + 9) (a + 3 * c + 7) 1)
  rw [show 1 + (2 * c + 9) = 2 * c + 10 from by omega]
  -- R5+R2 loop (c+4 pairs): -> (a+2c+3, 0, c+4, 0, 2)
  show ⟨a + 3 * c + 7, 0, 0, 0, 2 * c + 10⟩ [fm]⊢* ⟨a + 2 * c + 1, 0, c + 6, 1, 0⟩
  rw [show a + 3 * c + 7 = (c + 4) + (a + 2 * c + 3) from by omega,
      show 2 * c + 10 = 2 * (c + 4) + 2 from by omega]
  apply stepStar_trans (r52_loop (c + 4) (a + 2 * c + 3) 0 2)
  rw [show 0 + (c + 4) = c + 4 from by omega]
  -- R5: (a+2c+3, 0, c+4, 0, 2) -> (a+2c+2, 0, c+5, 1, 2)
  show ⟨a + 2 * c + 3, 0, c + 4, 0, 2⟩ [fm]⊢* ⟨a + 2 * c + 1, 0, c + 6, 1, 0⟩
  rw [show a + 2 * c + 3 = (a + 2 * c + 2) + 1 from by omega]
  step fm  -- R5
  -- R2: (a+2c+2, 0, c+5, 1, 2) -> (a+2c+2, 0, c+5, 0, 0)
  step fm  -- R2
  -- R5: (a+2c+2, 0, c+5, 0, 0) -> (a+2c+1, 0, c+6, 1, 0)
  rw [show a + 2 * c + 2 = (a + 2 * c + 1) + 1 from by omega]
  step fm  -- R5
  finish

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨0, 0, 1, 1, 0⟩)
  · execute fm 1
  apply progress_nonhalt (fm := fm)
    (P := fun q ↦ ∃ a c, q = ⟨a, 0, c + 1, 1, 0⟩)
  · intro q ⟨a, c, hq⟩; subst hq
    exact ⟨⟨a + 2 * c + 1, 0, c + 6, 1, 0⟩, ⟨a + 2 * c + 1, c + 5, rfl⟩, cycle a c⟩
  · exact ⟨0, 0, rfl⟩

end Sz22_2003_unofficial_266
