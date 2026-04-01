import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #1520: [7/15, 99/14, 484/3, 5/11, 3/2]

Vector representation:
```
 0 -1 -1  1  0
-1  2  0 -1  1
 2 -1  0  0  2
 0  0  1  0 -1
-1  1  0  0  0
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_1520

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a, b+1, c+1, d, e⟩ => some ⟨a, b, c, d+1, e⟩
  | ⟨a+1, b, c, d+1, e⟩ => some ⟨a, b+2, c, d, e+1⟩
  | ⟨a, b+1, c, d, e⟩ => some ⟨a+2, b, c, d, e+2⟩
  | ⟨a, b, c, d, e+1⟩ => some ⟨a, b, c+1, d, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b+1, c, d, e⟩
  | _ => none

theorem r3_step_a0 {b d e : ℕ} : (⟨0, b + 1, 0, d, e⟩ : Q) [fm]⊢ ⟨2, b, 0, d, e + 2⟩ := by
  simp [fm]

theorem e_to_c : ∀ k, (⟨a, 0, c, 0, e + k⟩ : Q) [fm]⊢* ⟨a, 0, c + k, 0, e⟩ := by
  intro k; induction' k with k ih generalizing c e
  · exists 0
  · rw [show e + (k + 1) = e + k + 1 from by ring]
    step fm; apply stepStar_trans (ih (c := c + 1)); ring_nf; finish

theorem r3_chain_d0 : ∀ k, (⟨a, k + b, 0, 0, e⟩ : Q) [fm]⊢* ⟨a + 2 * k, b, 0, 0, e + 2 * k⟩ := by
  intro k; induction' k with k ih generalizing a b e
  · simp; finish
  · rw [show (k + 1) + b = (k + b) + 1 from by ring]
    step fm; apply stepStar_trans (ih (a := a + 2) (e := e + 2)); ring_nf; finish

theorem r2_chain : ∀ k, (⟨a + k, b, 0, d + k, e⟩ : Q) [fm]⊢* ⟨a, b + 2 * k, 0, d, e + k⟩ := by
  intro k; induction' k with k ih generalizing a b d e
  · simp; finish
  · rw [show a + (k + 1) = (a + k) + 1 from by ring,
        show d + (k + 1) = (d + k) + 1 from by ring]
    step fm; apply stepStar_trans (ih (b := b + 2) (e := e + 1)); ring_nf; finish

theorem r3r2r2_cycle : (⟨0, b + 1, 0, d + 2, e⟩ : Q) [fm]⊢* ⟨0, b + 4, 0, d, e + 4⟩ := by
  apply stepStar_trans (step_stepStar r3_step_a0)
  step fm; step fm; ring_nf; finish

theorem r3r2_d1 : (⟨0, b + 1, 0, 1, e⟩ : Q) [fm]⊢* ⟨1, b + 2, 0, 0, e + 3⟩ := by
  apply stepStar_trans (step_stepStar r3_step_a0)
  step fm; ring_nf; finish

theorem drain_a0 : ∀ D, ∀ B E,
    (⟨0, B + 1, 0, D, E⟩ : Q) [fm]⊢* ⟨2 * (B + 1) + 3 * D, 0, 0, 0, E + 2 * (B + 1) + 5 * D⟩ := by
  intro D; induction' D using Nat.strongRecOn with D ih; intro B E
  rcases D with _ | _ | D
  · -- D = 0
    rw [show B + 1 = (B + 1) + 0 from by ring]
    apply stepStar_trans (r3_chain_d0 (B + 1) (a := 0) (b := 0) (e := E))
    ring_nf; finish
  · -- D = 1
    apply stepStar_trans (r3r2_d1 (b := B) (e := E))
    rw [show B + 2 = (B + 2) + 0 from by ring]
    apply stepStar_trans (r3_chain_d0 (B + 2) (a := 1) (b := 0) (e := E + 3))
    ring_nf; finish
  · -- D + 2
    rw [show D + 2 = D + 2 from rfl]
    apply stepStar_trans (r3r2r2_cycle (b := B) (d := D) (e := E))
    rw [show B + 4 = (B + 3) + 1 from by ring]
    apply stepStar_trans (ih D (by omega) (B + 3) (E + 4))
    ring_nf; finish

theorem drain : ∀ D, ∀ a e, (⟨a + 1, 0, 0, D, e⟩ : Q) [fm]⊢* ⟨a + 1 + 3 * D, 0, 0, 0, e + 5 * D⟩ := by
  intro D; rcases D with _ | D
  · intro a e; simp; finish
  · intro a e
    rcases le_or_gt (a + 1) (D + 1) with h | h
    · -- a+1 <= D+1: R2 drains a+1 steps
      obtain ⟨d, hd⟩ : ∃ d, D + 1 = d + (a + 1) := ⟨D - a, by omega⟩
      rw [show a + 1 = 0 + (a + 1) from by ring, hd]
      apply stepStar_trans (r2_chain (a + 1) (a := 0) (b := 0) (d := d) (e := e))
      rw [show 0 + 2 * (a + 1) = (2 * a + 1) + 1 from by ring]
      have goal_rw : (⟨2 * (2 * a + 1 + 1) + 3 * d, 0, 0, 0, e + (a + 1) + 2 * (2 * a + 1 + 1) + 5 * d⟩ : Q) =
          ⟨0 + (a + 1) + 3 * (d + (a + 1)), 0, 0, 0, e + 5 * (d + (a + 1))⟩ := by
        congr 1 <;> ring_nf
      rw [← goal_rw]
      exact drain_a0 d (2 * a + 1) (e + (a + 1))
    · -- a+1 > D+1: R2 drains D+1 steps
      obtain ⟨a', ha⟩ : ∃ a', a + 1 = a' + (D + 1) := ⟨a - D, by omega⟩
      rw [ha]
      rw [show a' + (D + 1) + 3 * (D + 1) = a' + 4 * (D + 1) from by ring,
          show e + 5 * (D + 1) = e + (D + 1) + 4 * (D + 1) from by ring]
      rw [show a' + (D + 1) = a' + (D + 1) from rfl]
      have hr2 := r2_chain (D + 1) (a := a') (b := 0) (d := 0) (e := e)
      simp only [Nat.zero_add] at hr2
      apply stepStar_trans hr2
      have hr3 := r3_chain_d0 (2 * (D + 1)) (a := a') (b := 0) (e := e + (D + 1))
      simp only [Nat.add_zero] at hr3
      have goal_rw : (⟨a' + 2 * (2 * (D + 1)), 0, 0, 0, e + (D + 1) + 2 * (2 * (D + 1))⟩ : Q) =
          ⟨a' + 4 * (D + 1), 0, 0, 0, e + (D + 1) + 4 * (D + 1)⟩ := by
        congr 1 <;> ring_nf
      rw [← goal_rw]; exact hr3

theorem spiral : ∀ k, (⟨a + 1 + k, 2, 2 * k + c, d, e⟩ : Q) [fm]⊢* ⟨a + 1, 2, c, d + k, e + k⟩ := by
  intro k; induction' k with k ih generalizing a c d e
  · simp; finish
  · rw [show a + 1 + (k + 1) = (a + 1 + k) + 1 from by ring,
        show 2 * (k + 1) + c = (2 * k + c) + 2 from by ring]
    step fm; step fm; step fm
    apply stepStar_trans (ih (d := d + 1) (e := e + 1))
    ring_nf; finish

theorem main_trans (a : ℕ) :
    (⟨a + 3, 0, 0, 0, 2 * a + 4⟩ : Q) [fm]⊢⁺ ⟨3 * a + 8, 0, 0, 0, 6 * a + 14⟩ := by
  rw [show (2 * a + 4 : ℕ) = 0 + (2 * a + 4) from by ring]
  apply stepStar_stepPlus_stepPlus (e_to_c (2 * a + 4) (a := a + 3) (c := 0) (e := 0))
  rw [show 0 + (2 * a + 4) = 2 * a + 4 from by ring]
  -- R5, R1, R2: (a+3, 0, 2a+4, 0, 0) → (a+1, 2, 2a+3, 0, 1)
  step fm; step fm; step fm
  -- spiral: (a+1, 2, 2a+3, 0, 1) → (1, 2, 3, a, a+1)
  rw [show a + 1 = 0 + 1 + a from by ring,
      show (2 * a + 3 : ℕ) = 2 * a + 3 from rfl]
  apply stepStar_trans (spiral (a := 0) (c := 3) (d := 0) (e := 1) a)
  -- (1, 2, 3, a, a+1): R1, R1, R2, R1
  rw [show (0 + 1 : ℕ) = 1 from rfl]
  step fm; step fm; step fm; step fm
  -- R3 step with a=0
  have hr3 : (⟨0, 1, 0, a + 2, a + 2⟩ : Q) [fm]⊢* ⟨2, 0, 0, a + 2, a + 4⟩ := by
    apply stepStar_trans (step_stepStar (r3_step_a0 (b := 0) (d := a + 2) (e := a + 2)))
    ring_nf; finish
  apply stepStar_trans (show (⟨0, 1, 0, 0 + a + 1 + 1, 1 + a + 1⟩ : Q) [fm]⊢*
    ⟨2, 0, 0, a + 2, a + 4⟩ from by convert hr3 using 2; ring_nf)
  -- drain
  rw [show (2 : ℕ) = 1 + 1 from rfl]
  have hdrain := drain (a + 2) 1 (a + 4)
  have hgoal : (⟨1 + 1 + 3 * (a + 2), 0, 0, 0, a + 4 + 5 * (a + 2)⟩ : Q) =
      ⟨3 * a + 8, 0, 0, 0, 6 * a + 14⟩ := by congr 1 <;> ring_nf
  rw [hgoal] at hdrain; exact hdrain

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨5, 0, 0, 0, 8⟩) (by execute fm 12)
  apply progress_nonhalt_simple (fm := fm) (A := ℕ)
    (fun n ↦ ⟨n + 5, 0, 0, 0, 2 * n + 8⟩) 0
  intro n; exists 3 * n + 9
  have h := main_trans (n + 2)
  convert h using 2; ring_nf

end Sz22_2003_unofficial_1520
