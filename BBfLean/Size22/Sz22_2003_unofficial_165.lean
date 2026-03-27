import BBfLean.FM
import Mathlib.Tactic.Ring
import Mathlib.Tactic.IntervalCases

/-!
# sz22_2003_unofficial #165: [1/45, 5/77, 1/7, 182/5, 33/13, 5/2]

Vector representation:
```
 0 -2 -1  0  0  0
 0  0  1 -1 -1  0
 0  0  0 -1  0  0
 1  0 -1  1  0  1
 0  1  0  0  1 -1
-1  0  1  0  0  0
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_165

def Q := ℕ × ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a, b+2, c+1, d, e, f⟩ => some ⟨a, b, c, d, e, f⟩
  | ⟨a, b, c, d+1, e+1, f⟩ => some ⟨a, b, c+1, d, e, f⟩
  | ⟨a, b, c, d+1, e, f⟩ => some ⟨a, b, c, d, e, f⟩
  | ⟨a, b, c+1, d, e, f⟩ => some ⟨a+1, b, c, d+1, e, f+1⟩
  | ⟨a, b, c, d, e, f+1⟩ => some ⟨a, b+1, c, d, e+1, f⟩
  | ⟨a+1, b, c, d, e, f⟩ => some ⟨a, b, c+1, d, e, f⟩
  | _ => none

theorem pump0 : ∀ k, ∀ a e f,
    (⟨a, 0, 1, 0, e + k, f⟩ : Q) [fm]⊢* ⟨a + k, 0, 1, 0, e, f + k⟩ := by
  intro k; induction' k with k ih <;> intro a e f
  · exists 0
  rw [show e + (k + 1) = (e + k) + 1 from by ring]
  step fm; step fm
  rw [show f + (k + 1) = (f + 1) + k from by ring,
      show a + (k + 1) = (a + 1) + k from by ring]
  exact ih _ _ _

theorem pump1 : ∀ k, ∀ a e f,
    (⟨a, 1, 1, 0, e + k, f⟩ : Q) [fm]⊢* ⟨a + k, 1, 1, 0, e, f + k⟩ := by
  intro k; induction' k with k ih <;> intro a e f
  · exists 0
  rw [show e + (k + 1) = (e + k) + 1 from by ring]
  step fm; step fm
  rw [show f + (k + 1) = (f + 1) + k from by ring,
      show a + (k + 1) = (a + 1) + k from by ring]
  exact ih _ _ _

theorem r5_phase : ∀ k, ∀ a b e,
    (⟨a, b, 0, 0, e, k⟩ : Q) [fm]⊢* ⟨a, b + k, 0, 0, e + k, 0⟩ := by
  intro k; induction' k with k ih <;> intro a b e
  · exists 0
  rw [show (k + 1 : ℕ) = k + 1 from rfl]
  step fm
  rw [show b + (k + 1) = (b + 1) + k from by ring,
      show e + (k + 1) = (e + 1) + k from by ring]
  exact ih _ _ _

theorem drain : ∀ k, ∀ a b e,
    (⟨a + k, b + 2 * k, 0, 0, e, 0⟩ : Q) [fm]⊢* ⟨a, b, 0, 0, e, 0⟩ := by
  intro k; induction' k with k ih <;> intro a b e
  · exists 0
  rw [show a + (k + 1) = (a + k) + 1 from by ring,
      show b + 2 * (k + 1) = (b + 2 * k) + 2 from by ring]
  step fm; step fm
  exact ih _ _ _

-- Case 1: b=0, e=2m. (a+1, 0, 0, 0, 2m, 0) ->+ (a+1+m, 1, 0, 0, 2m+1, 0)
theorem trans_b0_even (a m : ℕ) :
    (⟨a + 1, 0, 0, 0, 2 * m, 0⟩ : Q) [fm]⊢⁺ ⟨a + 1 + m, 1, 0, 0, 2 * m + 1, 0⟩ := by
  apply step_stepStar_stepPlus (by unfold fm; rfl)
  apply stepStar_trans
  · have h := pump0 (2 * m) a 0 0; simp only [Nat.zero_add] at h; exact h
  step fm; step fm
  apply stepStar_trans
  · have h := r5_phase (2 * m + 1) (a + 2 * m + 1) 0 0
    simp only [Nat.zero_add] at h; exact h
  have h := drain m (a + 1 + m) 1 (2 * m + 1)
  rw [show a + 1 + m + m = a + 2 * m + 1 from by ring,
      show 1 + 2 * m = 2 * m + 1 from by ring] at h
  exact h

-- Case 2: b=0, e=2m+1. (a+1, 0, 0, 0, 2m+1, 0) ->+ (a+1+m, 0, 0, 0, 2m+2, 0)
theorem trans_b0_odd (a m : ℕ) :
    (⟨a + 1, 0, 0, 0, 2 * m + 1, 0⟩ : Q) [fm]⊢⁺ ⟨a + 1 + m, 0, 0, 0, 2 * m + 2, 0⟩ := by
  apply step_stepStar_stepPlus (by unfold fm; rfl)
  apply stepStar_trans
  · have h := pump0 (2 * m + 1) a 0 0; simp only [Nat.zero_add] at h; exact h
  step fm; step fm
  apply stepStar_trans
  · have h := r5_phase (2 * m + 2) (a + 2 * m + 2) 0 0
    simp only [Nat.zero_add] at h; exact h
  have h := drain (m + 1) (a + 1 + m) 0 (2 * m + 2)
  rw [show a + 1 + m + (m + 1) = a + 2 * m + 2 from by ring,
      show 0 + 2 * (m + 1) = 2 * (m + 1) from by ring] at h
  ring_nf; ring_nf at h; exact h

-- Case 3: b=1, e=2(m+1). (a+1, 1, 0, 0, 2(m+1), 0) ->+ (a+1+m, 0, 0, 0, 2(m+1)+1, 0)
theorem trans_b1_even (a m : ℕ) :
    (⟨a + 1, 1, 0, 0, 2 * (m + 1), 0⟩ : Q) [fm]⊢⁺
    ⟨a + 1 + m, 0, 0, 0, 2 * (m + 1) + 1, 0⟩ := by
  apply step_stepStar_stepPlus (by unfold fm; rfl)
  apply stepStar_trans
  · have h := pump1 (2 * (m + 1)) a 0 0; simp only [Nat.zero_add] at h; exact h
  step fm; step fm
  apply stepStar_trans
  · have h := r5_phase (2 * (m + 1) + 1) (a + 2 * (m + 1) + 1) 1 0
    rw [show 1 + (2 * (m + 1) + 1) = 2 * (m + 1) + 2 from by ring] at h
    simp only [Nat.zero_add] at h; exact h
  have h := drain (m + 2) (a + 1 + m) 0 (2 * (m + 1) + 1)
  rw [show a + 1 + m + (m + 2) = a + 2 * (m + 1) + 1 from by ring,
      show 0 + 2 * (m + 2) = 2 * (m + 1) + 2 from by ring] at h
  ring_nf; ring_nf at h; exact h

-- Case 4: b=1, e=2m+1. (a+1, 1, 0, 0, 2m+1, 0) ->+ (a+1+m, 1, 0, 0, 2m+2, 0)
theorem trans_b1_odd (a m : ℕ) :
    (⟨a + 1, 1, 0, 0, 2 * m + 1, 0⟩ : Q) [fm]⊢⁺ ⟨a + 1 + m, 1, 0, 0, 2 * m + 2, 0⟩ := by
  apply step_stepStar_stepPlus (by unfold fm; rfl)
  apply stepStar_trans
  · have h := pump1 (2 * m + 1) a 0 0; simp only [Nat.zero_add] at h; exact h
  step fm; step fm
  apply stepStar_trans
  · have h := r5_phase (2 * m + 2) (a + 2 * m + 2) 1 0
    rw [show 1 + (2 * m + 2) = 2 * m + 3 from by ring] at h
    simp only [Nat.zero_add] at h; exact h
  have h := drain (m + 1) (a + 1 + m) 1 (2 * m + 2)
  rw [show a + 1 + m + (m + 1) = a + 2 * m + 2 from by ring,
      show 1 + 2 * (m + 1) = 2 * m + 3 from by ring] at h
  exact h

theorem main_trans : ∀ a b e, a ≥ 1 → b ≤ 1 → e ≥ 1 →
    ∃ a' b' e', a' ≥ 1 ∧ b' ≤ 1 ∧ e' ≥ 1 ∧
    (⟨a, b, 0, 0, e, 0⟩ : Q) [fm]⊢⁺ ⟨a', b', 0, 0, e', 0⟩ := by
  intro a b e ha hb he
  obtain ⟨a', rfl⟩ := Nat.exists_eq_add_of_le ha
  rw [show 1 + a' = a' + 1 from by ring]
  interval_cases b
  · -- b = 0
    have hmod := Nat.div_add_mod e 2
    set m := e / 2
    set r := e % 2
    have hr : r < 2 := Nat.mod_lt e (by omega)
    interval_cases r
    · -- e = 2*m
      rw [show e = 2 * m from by omega]
      exact ⟨a' + 1 + m, 1, 2 * m + 1, by omega, by omega, by omega, trans_b0_even a' m⟩
    · -- e = 2*m + 1
      rw [show e = 2 * m + 1 from by omega]
      exact ⟨a' + 1 + m, 0, 2 * m + 2, by omega, by omega, by omega, trans_b0_odd a' m⟩
  · -- b = 1
    have hmod := Nat.div_add_mod e 2
    set m := e / 2
    set r := e % 2
    have hr : r < 2 := Nat.mod_lt e (by omega)
    interval_cases r
    · -- e = 2*m, m >= 1 since e >= 1
      have hm : m ≥ 1 := by omega
      obtain ⟨m', hm'⟩ := Nat.exists_eq_add_of_le hm
      rw [show e = 2 * (m' + 1) from by omega]
      exact ⟨a' + 1 + m', 0, 2 * (m' + 1) + 1, by omega, by omega, by omega,
        trans_b1_even a' m'⟩
    · -- e = 2*m + 1
      rw [show e = 2 * m + 1 from by omega]
      exact ⟨a' + 1 + m, 1, 2 * m + 2, by omega, by omega, by omega, trans_b1_odd a' m⟩

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨1, 1, 0, 0, 1, 0⟩) (by execute fm 4)
  apply progress_nonhalt (fm := fm)
    (P := fun q ↦ ∃ a b e, q = ⟨a, b, 0, 0, e, 0⟩ ∧ a ≥ 1 ∧ b ≤ 1 ∧ e ≥ 1)
  · intro c ⟨a, b, e, hq, ha, hb, he⟩
    subst hq
    obtain ⟨a', b', e', ha', hb', he', htrans⟩ := main_trans a b e ha hb he
    exact ⟨⟨a', b', 0, 0, e', 0⟩, ⟨a', b', e', rfl, ha', hb', he'⟩, htrans⟩
  · exact ⟨1, 1, 1, rfl, by omega, by omega, by omega⟩

end Sz22_2003_unofficial_165
