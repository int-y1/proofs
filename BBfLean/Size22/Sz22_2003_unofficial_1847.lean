import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #1847: [9/35, 1/33, 50/3, 11/5, 63/2]

Vector representation:
```
 0  2 -1 -1  0
 0 -1  0  0 -1
 1 -1  2  0  0
 0  0 -1  0  1
-1  2  0  1  0
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_1847

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a, b, c+1, d+1, e⟩ => some ⟨a, b+2, c, d, e⟩
  | ⟨a, b+1, c, d, e+1⟩ => some ⟨a, b, c, d, e⟩
  | ⟨a, b+1, c, d, e⟩ => some ⟨a+1, b, c+2, d, e⟩
  | ⟨a, b, c+1, d, e⟩ => some ⟨a, b, c, d, e+1⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b+2, c, d+1, e⟩
  | _ => none

theorem drain : ∀ k, ⟨a + k, 0, 0, d, e + 2 * k⟩ [fm]⊢* ⟨a, 0, 0, d + k, e⟩ := by
  intro k; induction' k with k ih generalizing a d e
  · exists 0
  · rw [show a + (k + 1) = (a + k) + 1 from by ring]
    rw [show e + 2 * (k + 1) = (e + 2 * k) + 1 + 1 from by ring]
    step fm; step fm; step fm
    apply stepStar_trans (ih (a := a) (d := d + 1) (e := e))
    ring_nf; finish

theorem c_to_e : ∀ k, ⟨a, 0, c + k, 0, e⟩ [fm]⊢* ⟨a, 0, c, 0, e + k⟩ := by
  intro k; induction' k with k ih generalizing a c e
  · exists 0
  · rw [show c + (k + 1) = (c + k) + 1 from by ring]
    step fm
    apply stepStar_trans (ih (c := c) (e := e + 1))
    ring_nf; finish

theorem b_to_ac : ∀ k, ⟨a, b + k, c, 0, 0⟩ [fm]⊢* ⟨a + k, b, c + 2 * k, 0, 0⟩ := by
  intro k; induction' k with k ih generalizing a b c
  · exists 0
  · rw [show b + (k + 1) = (b + k) + 1 from by ring]
    step fm
    apply stepStar_trans (ih (a := a + 1) (b := b) (c := c + 2))
    ring_nf; finish

theorem interleaved : ∀ k, ⟨a, b + 1, 0, d + 2 * k, 0⟩ [fm]⊢* ⟨a + k, b + 1 + 3 * k, 0, d, 0⟩ := by
  intro k; induction' k with k ih generalizing a b d
  · exists 0
  · rw [show d + 2 * (k + 1) = d + 2 * k + 1 + 1 from by ring]
    step fm; step fm; step fm
    apply stepStar_trans (ih (a := a + 1) (b := b + 3) (d := d))
    ring_nf; finish

theorem d1_finish : ⟨a, b + 1, 0, 1, 0⟩ [fm]⊢* ⟨a + 2, b + 1, 3, 0, 0⟩ := by
  step fm; step fm; step fm; finish

theorem buildup_e0_odd : ⟨a + 1, 0, 0, 2 * m + 1, 0⟩ [fm]⊢⁺ ⟨a + 4 * m + 6, 0, 0, 0, 6 * m + 10⟩ := by
  rw [show 2 * m + 1 = 2 * m + 1 from by ring]
  step fm; step fm; step fm; step fm
  rw [show 2 * m = 0 + 2 * m from by ring]
  apply stepStar_trans (interleaved m (a := a + 1) (b := 4) (d := 0))
  rw [show 4 + 1 + 3 * m = 0 + (5 + 3 * m) from by ring]
  apply stepStar_trans (b_to_ac (5 + 3 * m) (a := a + 1 + m) (b := 0) (c := 0))
  rw [show 0 + 2 * (5 + 3 * m) = 0 + (10 + 6 * m) from by ring]
  apply stepStar_trans (c_to_e (10 + 6 * m) (a := a + 1 + m + (5 + 3 * m)) (c := 0) (e := 0))
  ring_nf; finish

theorem buildup_e0_even : ⟨a + 1, 0, 0, 2 * m + 2, 0⟩ [fm]⊢⁺ ⟨a + 4 * m + 8, 0, 0, 0, 6 * m + 13⟩ := by
  rw [show 2 * m + 2 = 2 * m + 1 + 1 from by ring]
  step fm; step fm; step fm; step fm
  rw [show 2 * m + 1 = 1 + 2 * m from by ring]
  apply stepStar_trans (interleaved m (a := a + 1) (b := 4) (d := 1))
  rw [show 4 + 1 + 3 * m = 4 + 3 * m + 1 from by ring]
  apply stepStar_trans (d1_finish (a := a + 1 + m) (b := 4 + 3 * m))
  rw [show 4 + 3 * m + 1 = 0 + (5 + 3 * m) from by ring]
  apply stepStar_trans (b_to_ac (5 + 3 * m) (a := a + 1 + m + 2) (b := 0) (c := 3))
  rw [show 3 + 2 * (5 + 3 * m) = 0 + (13 + 6 * m) from by ring]
  apply stepStar_trans (c_to_e (13 + 6 * m) (a := a + 1 + m + 2 + (5 + 3 * m)) (c := 0) (e := 0))
  ring_nf; finish

theorem buildup_e0_d0 : ⟨a + 1, 0, 0, 0, 0⟩ [fm]⊢⁺ ⟨a + 4, 0, 0, 0, 7⟩ := by
  step fm; step fm; step fm
  step fm; step fm; step fm
  rw [show 7 = 0 + 7 from by ring]
  apply stepStar_trans (c_to_e 7 (a := a + 4) (c := 0) (e := 0))
  ring_nf; finish

theorem buildup_e1_odd : ⟨a + 1, 0, 0, 2 * m + 1, 1⟩ [fm]⊢⁺ ⟨a + 4 * m + 5, 0, 0, 0, 6 * m + 8⟩ := by
  rw [show 2 * m + 1 = 2 * m + 1 from by ring]
  step fm; step fm; step fm; step fm; step fm
  rw [show 2 * m = 0 + 2 * m from by ring]
  apply stepStar_trans (interleaved m (a := a + 1) (b := 3) (d := 0))
  rw [show 3 + 1 + 3 * m = 0 + (4 + 3 * m) from by ring]
  apply stepStar_trans (b_to_ac (4 + 3 * m) (a := a + 1 + m) (b := 0) (c := 0))
  rw [show 0 + 2 * (4 + 3 * m) = 0 + (8 + 6 * m) from by ring]
  apply stepStar_trans (c_to_e (8 + 6 * m) (a := a + 1 + m + (4 + 3 * m)) (c := 0) (e := 0))
  ring_nf; finish

theorem buildup_e1_even : ⟨a + 1, 0, 0, 2 * m + 2, 1⟩ [fm]⊢⁺ ⟨a + 4 * m + 7, 0, 0, 0, 6 * m + 11⟩ := by
  rw [show 2 * m + 2 = 2 * m + 1 + 1 from by ring]
  step fm; step fm; step fm; step fm; step fm
  rw [show 2 * m + 1 = 1 + 2 * m from by ring]
  apply stepStar_trans (interleaved m (a := a + 1) (b := 3) (d := 1))
  rw [show 3 + 1 + 3 * m = 3 + 3 * m + 1 from by ring]
  apply stepStar_trans (d1_finish (a := a + 1 + m) (b := 3 + 3 * m))
  rw [show 3 + 3 * m + 1 = 0 + (4 + 3 * m) from by ring]
  apply stepStar_trans (b_to_ac (4 + 3 * m) (a := a + 1 + m + 2) (b := 0) (c := 3))
  rw [show 3 + 2 * (4 + 3 * m) = 0 + (11 + 6 * m) from by ring]
  apply stepStar_trans (c_to_e (11 + 6 * m) (a := a + 1 + m + 2 + (4 + 3 * m)) (c := 0) (e := 0))
  ring_nf; finish

theorem buildup_e1_d0 : ⟨a + 1, 0, 0, 0, 1⟩ [fm]⊢⁺ ⟨a + 3, 0, 0, 0, 5⟩ := by
  step fm; step fm; step fm; step fm; step fm; step fm
  rw [show 5 = 0 + 5 from by ring]
  apply stepStar_trans (c_to_e 5 (a := a + 3) (c := 0) (e := 0))
  ring_nf; finish

theorem cycle_even (a m : ℕ) : ⟨a + m + 1, 0, 0, 0, 2 * m⟩ [fm]⊢⁺ ⟨a + 2 * m + 4, 0, 0, 0, 3 * m + 7⟩ := by
  rcases m with _ | m
  · show ⟨a + 1, 0, 0, 0, 0⟩ [fm]⊢⁺ ⟨a + 4, 0, 0, 0, 7⟩
    exact buildup_e0_d0
  · rw [show a + (m + 1) + 1 = (a + 1) + (m + 1) from by ring,
        show 2 * (m + 1) = 0 + 2 * (m + 1) from by ring]
    apply stepStar_stepPlus_stepPlus (drain (m + 1) (a := a + 1) (d := 0) (e := 0))
    rw [show 0 + (m + 1) = m + 1 from by ring, show (0 : ℕ) = 0 from rfl]
    rcases Nat.even_or_odd (m + 1) with ⟨j, hj⟩ | ⟨j, hj⟩
    · rw [show j + j = 2 * j from by ring] at hj
      rcases j with _ | j
      · omega
      · rw [show m + 1 = 2 * j + 2 from by omega]
        apply stepPlus_stepStar_stepPlus (buildup_e0_even (a := a) (m := j))
        ring_nf; finish
    · rw [show m + 1 = 2 * j + 1 from by omega]
      apply stepPlus_stepStar_stepPlus (buildup_e0_odd (a := a) (m := j))
      ring_nf; finish

theorem cycle_odd (a m : ℕ) : ⟨a + m + 1, 0, 0, 0, 2 * m + 1⟩ [fm]⊢⁺ ⟨a + 2 * m + 3, 0, 0, 0, 3 * m + 5⟩ := by
  rcases m with _ | m
  · show ⟨a + 1, 0, 0, 0, 1⟩ [fm]⊢⁺ ⟨a + 3, 0, 0, 0, 5⟩
    exact buildup_e1_d0
  · rw [show a + (m + 1) + 1 = (a + 1) + (m + 1) from by ring,
        show 2 * (m + 1) + 1 = 1 + 2 * (m + 1) from by ring]
    apply stepStar_stepPlus_stepPlus (drain (m + 1) (a := a + 1) (d := 0) (e := 1))
    rw [show 0 + (m + 1) = m + 1 from by ring]
    rcases Nat.even_or_odd (m + 1) with ⟨j, hj⟩ | ⟨j, hj⟩
    · rw [show j + j = 2 * j from by ring] at hj
      rcases j with _ | j
      · omega
      · rw [show m + 1 = 2 * j + 2 from by omega]
        apply stepPlus_stepStar_stepPlus (buildup_e1_even (a := a) (m := j))
        ring_nf; finish
    · rw [show m + 1 = 2 * j + 1 from by omega]
      apply stepPlus_stepStar_stepPlus (buildup_e1_odd (a := a) (m := j))
      ring_nf; finish

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨4, 0, 0, 0, 7⟩) (by execute fm 13)
  apply progress_nonhalt (fm := fm)
    (P := fun q ↦ ∃ a e, q = ⟨a + 1, 0, 0, 0, e⟩ ∧ 2 * a + 1 ≥ e)
  · intro c ⟨a, e, hq, hinv⟩; subst hq
    rcases Nat.even_or_odd e with ⟨m, hm⟩ | ⟨m, hm⟩
    · rw [show m + m = 2 * m from by ring] at hm; subst hm
      have ham : a ≥ m := by omega
      obtain ⟨s, rfl⟩ : ∃ s, a = s + m := ⟨a - m, by omega⟩
      refine ⟨⟨s + 2 * m + 4, 0, 0, 0, 3 * m + 7⟩,
        ⟨s + 2 * m + 3, 3 * m + 7, rfl, by omega⟩, ?_⟩
      rw [show s + m + 1 = s + m + 1 from rfl]
      exact cycle_even s m
    · subst hm
      have ham : a ≥ m := by omega
      obtain ⟨s, rfl⟩ : ∃ s, a = s + m := ⟨a - m, by omega⟩
      refine ⟨⟨s + 2 * m + 3, 0, 0, 0, 3 * m + 5⟩,
        ⟨s + 2 * m + 2, 3 * m + 5, rfl, by omega⟩, ?_⟩
      rw [show s + m + 1 = s + m + 1 from rfl]
      exact cycle_odd s m
  · exact ⟨3, 7, rfl, by omega⟩
