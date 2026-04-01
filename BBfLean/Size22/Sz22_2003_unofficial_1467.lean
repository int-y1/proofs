import BBfLean.FM
import Mathlib.Tactic.Ring
import Mathlib.Tactic.IntervalCases

/-!
# sz22_2003_unofficial #1467: [7/15, 3/847, 250/7, 11/5, 49/2]

Vector representation:
```
 0 -1 -1  1  0
 0  1  0 -1 -2
 1  0  3 -1  0
 0  0 -1  0  1
-1  0  0  2  0
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_1467

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a, b+1, c+1, d, e⟩ => some ⟨a, b, c, d+1, e⟩
  | ⟨a, b, c, d+1, e+2⟩ => some ⟨a, b+1, c, d, e⟩
  | ⟨a, b, c, d+1, e⟩ => some ⟨a+1, b, c+3, d, e⟩
  | ⟨a, b, c+1, d, e⟩ => some ⟨a, b, c, d, e+1⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b, c, d+2, e⟩
  | _ => none

-- Step helpers for symbolic b (c=0 eliminates R1)
private theorem fm_r2 : fm ⟨a, b, 0, d + 1, e + 2⟩ = some ⟨a, b + 1, 0, d, e⟩ := by
  cases b <;> rfl

private theorem fm_r3_e0 : fm ⟨a, b, 0, d + 1, 0⟩ = some ⟨a + 1, b, 3, d, 0⟩ := by
  cases b <;> rfl

private theorem fm_r3_e1 : fm ⟨a, b, 0, d + 1, 1⟩ = some ⟨a + 1, b, 3, d, 1⟩ := by
  cases b <;> rfl

private theorem fm_r5 : fm ⟨a + 1, b, 0, 0, e⟩ = some ⟨a, b, 0, 2, e⟩ := by
  cases b <;> rfl

-- R4 chain: transfer c to e (b=0, d=0)
theorem r4_chain : ∀ k, ⟨a, 0, k, 0, e⟩ [fm]⊢* ⟨a, 0, 0, 0, e + k⟩ := by
  intro k; induction' k with k ih generalizing a e
  · exists 0
  · rw [show (k + 1 : ℕ) = k + 1 from rfl]
    step fm
    apply stepStar_trans (ih (e := e + 1))
    ring_nf; finish

-- R3 chain with e=0 (b=0)
theorem r3_chain_e0 : ∀ k, ⟨a, 0, c, k, 0⟩ [fm]⊢* ⟨a + k, 0, c + 3 * k, 0, 0⟩ := by
  intro k; induction' k with k ih generalizing a c
  · exists 0
  · rw [show (k + 1 : ℕ) = k + 1 from rfl]
    step fm
    apply stepStar_trans (ih (a := a + 1) (c := c + 3))
    ring_nf; finish

-- R3 chain with e=1 (b=0)
theorem r3_chain_e1 : ∀ k, ⟨a, 0, c, k, 1⟩ [fm]⊢* ⟨a + k, 0, c + 3 * k, 0, 1⟩ := by
  intro k; induction' k with k ih generalizing a c
  · exists 0
  · rw [show (k + 1 : ℕ) = k + 1 from rfl]
    step fm
    apply stepStar_trans (ih (a := a + 1) (c := c + 3))
    ring_nf; finish

-- R3+R4 combined with e=0
theorem r3r4_e0 : ∀ D, ⟨a, 0, c, D, 0⟩ [fm]⊢* ⟨a + D, 0, 0, 0, c + 3 * D⟩ := by
  intro D
  exact stepStar_trans (r3_chain_e0 D) (stepStar_trans (r4_chain (c + 3 * D) (e := 0))
    (by ring_nf; finish))

-- R3+R4 combined with e=1
theorem r3r4_e1 : ∀ D, ⟨a, 0, c, D, 1⟩ [fm]⊢* ⟨a + D, 0, 0, 0, 1 + c + 3 * D⟩ := by
  intro D
  exact stepStar_trans (r3_chain_e1 D) (stepStar_trans (r4_chain (c + 3 * D) (e := 1))
    (by ring_nf; finish))

-- One drain round: R2, R2, R5 (3 steps, symbolic b)
theorem drain_round : ⟨a + 1, b, 0, 2, e + 4⟩ [fm]⊢* ⟨a, b + 2, 0, 2, e⟩ := by
  exact stepStar_trans (step_stepStar (show _ [fm]⊢ _ from fm_r2))
    (stepStar_trans (step_stepStar (show _ [fm]⊢ _ from fm_r2))
      (step_stepStar (show _ [fm]⊢ _ from fm_r5)))

-- Iterated drain
theorem drain_iter : ∀ k, ⟨a + k, b, 0, 2, e + 4 * k⟩ [fm]⊢* ⟨a, b + 2 * k, 0, 2, e⟩ := by
  intro k; induction' k with k ih generalizing a b e
  · exists 0
  · rw [show a + (k + 1) = (a + 1) + k from by ring,
        show e + 4 * (k + 1) = (e + 4) + 4 * k from by ring]
    exact stepStar_trans (ih (a := a + 1) (e := e + 4))
      (stepStar_trans (drain_round (a := a) (b := b + 2 * k) (e := e))
        (by ring_nf; finish))

-- Drain end cases (symbolic b)
theorem drain_end_0 : ⟨a, b, 0, 2, 0⟩ [fm]⊢* ⟨a + 1, b, 3, 1, 0⟩ :=
  step_stepStar (show _ [fm]⊢ _ from fm_r3_e0)

theorem drain_end_1 : ⟨a, b, 0, 2, 1⟩ [fm]⊢* ⟨a + 1, b, 3, 1, 1⟩ :=
  step_stepStar (show _ [fm]⊢ _ from fm_r3_e1)

theorem drain_end_2 : ⟨a, b, 0, 2, 2⟩ [fm]⊢* ⟨a + 1, b + 1, 3, 0, 0⟩ :=
  stepStar_trans (step_stepStar (show _ [fm]⊢ _ from fm_r2))
    (step_stepStar (show _ [fm]⊢ _ from fm_r3_e0))

theorem drain_end_3 : ⟨a, b, 0, 2, 3⟩ [fm]⊢* ⟨a + 1, b + 1, 3, 0, 1⟩ :=
  stepStar_trans (step_stepStar (show _ [fm]⊢ _ from fm_r2))
    (step_stepStar (show _ [fm]⊢ _ from fm_r3_e1))

-- Rebuild step with e=0: R1 x3 + R3 (B is concrete after step fm, then R3 uses fm_r3_e0)
theorem rebuild_step_e0 : ⟨a, B + 3, 3, D, 0⟩ [fm]⊢* ⟨a + 1, B, 3, D + 2, 0⟩ := by
  step fm; step fm; step fm
  exact step_stepStar (show _ [fm]⊢ _ from fm_r3_e0)

theorem rebuild_step_e1 : ⟨a, B + 3, 3, D, 1⟩ [fm]⊢* ⟨a + 1, B, 3, D + 2, 1⟩ := by
  step fm; step fm; step fm
  exact step_stepStar (show _ [fm]⊢ _ from fm_r3_e1)

-- Rebuild iteration with e=0
theorem rebuild_iter_e0 : ∀ m, ⟨a, s + 3 * m, 3, D, 0⟩ [fm]⊢* ⟨a + m, s, 3, D + 2 * m, 0⟩ := by
  intro m; induction' m with m ih generalizing a D
  · exists 0
  · rw [show s + 3 * (m + 1) = (s + 3 * m) + 3 from by ring]
    exact stepStar_trans
      (stepStar_trans (rebuild_step_e0 (a := a) (B := s + 3 * m) (D := D))
        (ih (a := a + 1) (D := D + 2)))
      (by ring_nf; finish)

-- Rebuild iteration with e=1
theorem rebuild_iter_e1 : ∀ m, ⟨a, s + 3 * m, 3, D, 1⟩ [fm]⊢* ⟨a + m, s, 3, D + 2 * m, 1⟩ := by
  intro m; induction' m with m ih generalizing a D
  · exists 0
  · rw [show s + 3 * (m + 1) = (s + 3 * m) + 3 from by ring]
    exact stepStar_trans
      (stepStar_trans (rebuild_step_e1 (a := a) (B := s + 3 * m) (D := D))
        (ih (a := a + 1) (D := D + 2)))
      (by ring_nf; finish)

-- Rebuild end cases with e=0
theorem rebuild_end0_e0 : ⟨a, 0, 3, D, 0⟩ [fm]⊢* ⟨a + D, 0, 0, 0, 3 * D + 3⟩ :=
  stepStar_trans (r3r4_e0 D (c := 3)) (by ring_nf; finish)

theorem rebuild_end1_e0 : ⟨a, 1, 3, D, 0⟩ [fm]⊢* ⟨a + D + 1, 0, 0, 0, 3 * D + 5⟩ := by
  step fm
  exact stepStar_trans (r3r4_e0 (D + 1) (a := a) (c := 2)) (by ring_nf; finish)

theorem rebuild_end2_e0 : ⟨a, 2, 3, D, 0⟩ [fm]⊢* ⟨a + D + 2, 0, 0, 0, 3 * D + 7⟩ := by
  step fm; step fm
  exact stepStar_trans (r3r4_e0 (D + 2) (a := a) (c := 1)) (by ring_nf; finish)

-- Rebuild end cases with e=1
theorem rebuild_end0_e1 : ⟨a, 0, 3, D, 1⟩ [fm]⊢* ⟨a + D, 0, 0, 0, 3 * D + 4⟩ :=
  stepStar_trans (r3r4_e1 D (c := 3)) (by ring_nf; finish)

theorem rebuild_end1_e1 : ⟨a, 1, 3, D, 1⟩ [fm]⊢* ⟨a + D + 1, 0, 0, 0, 3 * D + 6⟩ := by
  step fm
  exact stepStar_trans (r3r4_e1 (D + 1) (a := a) (c := 2)) (by ring_nf; finish)

theorem rebuild_end2_e1 : ⟨a, 2, 3, D, 1⟩ [fm]⊢* ⟨a + D + 2, 0, 0, 0, 3 * D + 8⟩ := by
  step fm; step fm
  exact stepStar_trans (r3r4_e1 (D + 2) (a := a) (c := 1)) (by ring_nf; finish)

-- Full rebuild with e=0: (a, B, 3, D, 0) →* (a+B+D, 0, 0, 0, 3D+2B+3)
theorem rebuild_e0 (B : ℕ) : ⟨a, B, 3, D, 0⟩ [fm]⊢* ⟨a + B + D, 0, 0, 0, 3 * D + 2 * B + 3⟩ := by
  obtain ⟨m, s, rfl, hs⟩ : ∃ m s, B = s + 3 * m ∧ s < 3 := ⟨B / 3, B % 3, by omega, by omega⟩
  apply stepStar_trans (rebuild_iter_e0 m)
  interval_cases s
  · exact stepStar_trans (rebuild_end0_e0 (a := a + m) (D := D + 2 * m)) (by ring_nf; finish)
  · exact stepStar_trans (rebuild_end1_e0 (a := a + m) (D := D + 2 * m)) (by ring_nf; finish)
  · exact stepStar_trans (rebuild_end2_e0 (a := a + m) (D := D + 2 * m)) (by ring_nf; finish)

-- Full rebuild with e=1: (a, B, 3, D, 1) →* (a+B+D, 0, 0, 0, 3D+2B+4)
theorem rebuild_e1 (B : ℕ) : ⟨a, B, 3, D, 1⟩ [fm]⊢* ⟨a + B + D, 0, 0, 0, 3 * D + 2 * B + 4⟩ := by
  obtain ⟨m, s, rfl, hs⟩ : ∃ m s, B = s + 3 * m ∧ s < 3 := ⟨B / 3, B % 3, by omega, by omega⟩
  apply stepStar_trans (rebuild_iter_e1 m)
  interval_cases s
  · exact stepStar_trans (rebuild_end0_e1 (a := a + m) (D := D + 2 * m)) (by ring_nf; finish)
  · exact stepStar_trans (rebuild_end1_e1 (a := a + m) (D := D + 2 * m)) (by ring_nf; finish)
  · exact stepStar_trans (rebuild_end2_e1 (a := a + m) (D := D + 2 * m)) (by ring_nf; finish)

-- Transitions: from (a+k+1, 0, 0, 0, 4k+r) →⁺ (a+2k+2, 0, 0, 0, next_e)
theorem trans_r0 (a k : ℕ) :
    ⟨a + k + 1, 0, 0, 0, 4 * k⟩ [fm]⊢⁺ ⟨a + 2 * k + 2, 0, 0, 0, 4 * k + 6⟩ := by
  rw [show a + k + 1 = (a + k) + 1 from by ring]; step fm
  show ⟨a + k, 0, 0, 2, 4 * k⟩ [fm]⊢* _
  rw [show (4 * k : ℕ) = 0 + 4 * k from by ring]
  apply stepStar_trans (drain_iter k (a := a) (b := 0) (e := 0))
  rw [show 0 + 2 * k = 2 * k from by ring]
  apply stepStar_trans (drain_end_0 (a := a) (b := 2 * k))
  apply stepStar_trans (rebuild_e0 (2 * k) (a := a + 1) (D := 1))
  ring_nf; finish

theorem trans_r1 (a k : ℕ) :
    ⟨a + k + 1, 0, 0, 0, 4 * k + 1⟩ [fm]⊢⁺ ⟨a + 2 * k + 2, 0, 0, 0, 4 * k + 7⟩ := by
  rw [show a + k + 1 = (a + k) + 1 from by ring]; step fm
  show ⟨a + k, 0, 0, 2, 4 * k + 1⟩ [fm]⊢* _
  rw [show 4 * k + 1 = 1 + 4 * k from by ring]
  apply stepStar_trans (drain_iter k (a := a) (b := 0) (e := 1))
  rw [show 0 + 2 * k = 2 * k from by ring]
  apply stepStar_trans (drain_end_1 (a := a) (b := 2 * k))
  apply stepStar_trans (rebuild_e1 (2 * k) (a := a + 1) (D := 1))
  ring_nf; finish

theorem trans_r2 (a k : ℕ) :
    ⟨a + k + 1, 0, 0, 0, 4 * k + 2⟩ [fm]⊢⁺ ⟨a + 2 * k + 2, 0, 0, 0, 4 * k + 5⟩ := by
  rw [show a + k + 1 = (a + k) + 1 from by ring]; step fm
  show ⟨a + k, 0, 0, 2, 4 * k + 2⟩ [fm]⊢* _
  rw [show 4 * k + 2 = 2 + 4 * k from by ring]
  apply stepStar_trans (drain_iter k (a := a) (b := 0) (e := 2))
  rw [show 0 + 2 * k = 2 * k from by ring]
  apply stepStar_trans (drain_end_2 (a := a) (b := 2 * k))
  apply stepStar_trans (rebuild_e0 (2 * k + 1) (a := a + 1) (D := 0))
  ring_nf; finish

theorem trans_r3 (a k : ℕ) :
    ⟨a + k + 1, 0, 0, 0, 4 * k + 3⟩ [fm]⊢⁺ ⟨a + 2 * k + 2, 0, 0, 0, 4 * k + 6⟩ := by
  rw [show a + k + 1 = (a + k) + 1 from by ring]; step fm
  show ⟨a + k, 0, 0, 2, 4 * k + 3⟩ [fm]⊢* _
  rw [show 4 * k + 3 = 3 + 4 * k from by ring]
  apply stepStar_trans (drain_iter k (a := a) (b := 0) (e := 3))
  rw [show 0 + 2 * k = 2 * k from by ring]
  apply stepStar_trans (drain_end_3 (a := a) (b := 2 * k))
  apply stepStar_trans (rebuild_e1 (2 * k + 1) (a := a + 1) (D := 0))
  ring_nf; finish

theorem nonhalt : ¬halts fm c₀ := by
  apply progress_nonhalt (fm := fm)
    (P := fun q ↦ ∃ a k r, q = ⟨a + k + 1, 0, 0, 0, 4 * k + r⟩ ∧ r < 4)
  · intro c ⟨a, k, r, hq, hr⟩; subst hq
    interval_cases r
    · -- r=0: next is (a+2k+2, 0, 0, 0, 4k+6) = ((a+k) + (k+1) + 1, 0, 0, 0, 4*(k+1) + 2)
      exact ⟨_, ⟨a + k, k + 1, 2, by ring_nf, by omega⟩, trans_r0 a k⟩
    · -- r=1: next is (a+2k+2, 0, 0, 0, 4k+7) = ((a+k) + (k+1) + 1, 0, 0, 0, 4*(k+1) + 3)
      exact ⟨_, ⟨a + k, k + 1, 3, by ring_nf, by omega⟩, trans_r1 a k⟩
    · -- r=2: next is (a+2k+2, 0, 0, 0, 4k+5) = ((a+k) + (k+1) + 1, 0, 0, 0, 4*(k+1) + 1)
      exact ⟨_, ⟨a + k, k + 1, 1, by ring_nf, by omega⟩, trans_r2 a k⟩
    · -- r=3: next is (a+2k+2, 0, 0, 0, 4k+6) = ((a+k) + (k+1) + 1, 0, 0, 0, 4*(k+1) + 2)
      exact ⟨_, ⟨a + k, k + 1, 2, by ring_nf, by omega⟩, trans_r3 a k⟩
  · exact ⟨0, 0, 0, rfl, by omega⟩

end Sz22_2003_unofficial_1467
