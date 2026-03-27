import BBfLean.FM
import Mathlib.Tactic.Ring
import Mathlib.Tactic.IntervalCases

/-!
# sz22_2003_unofficial #440: [27/35, 5/33, 98/3, 11/7, 21/2]

Vector representation:
```
 0  3 -1 -1  0
 0 -1  1  0 -1
 1 -1  0  2  0
 0  0  0 -1  1
-1  1  0  1  0
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_440

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a, b, c+1, d+1, e⟩ => some ⟨a, b+3, c, d, e⟩
  | ⟨a, b+1, c, d, e+1⟩ => some ⟨a, b, c+1, d, e⟩
  | ⟨a, b+1, c, d, e⟩ => some ⟨a+1, b, c, d+2, e⟩
  | ⟨a, b, c, d+1, e⟩ => some ⟨a, b, c, d, e+1⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b+1, c, d+1, e⟩
  | _ => none

-- Rule 3 drain: b steps of rule 3 when c=0, e=0
theorem b_drain : ∀ k a d,
    (⟨a, k, 0, d, 0⟩ : Q) [fm]⊢* ⟨a + k, 0, 0, d + 2 * k, 0⟩ := by
  intro k; induction k with
  | zero => intro a d; simp; exists 0
  | succ k ih =>
    intro a d
    step fm
    rw [show d + 2 * (k + 1) = (d + 2) + 2 * k from by ring,
        show a + (k + 1) = (a + 1) + k from by ring]
    exact ih (a + 1) (d + 2)

-- rule3 + 2*rule1: consume 2 from c
theorem c_drain_2 : ∀ a b c,
    (⟨a, b + 1, c + 2, 0, 0⟩ : Q) [fm]⊢* ⟨a + 1, b + 6, c, 0, 0⟩ := by
  intro a b c
  step fm; step fm; step fm; ring_nf; finish

-- c_drain_2 iterated k times
theorem c_drain_2k : ∀ k a b c,
    (⟨a, b + 1, c + 2 * k, 0, 0⟩ : Q) [fm]⊢* ⟨a + k, b + 1 + 5 * k, c, 0, 0⟩ := by
  intro k; induction k with
  | zero => intro a b c; simp; exists 0
  | succ k ih =>
    intro a b c
    rw [show c + 2 * (k + 1) = (c + 2 * k) + 2 from by ring]
    apply stepStar_trans (c_drain_2 a b (c + 2 * k))
    have h := ih (a + 1) (b + 5) c
    rw [show (b + 5) + 1 + 5 * k = b + 1 + 5 * (k + 1) from by ring,
        show (a + 1) + k = a + (k + 1) from by ring,
        show b + 6 = (b + 5) + 1 from by ring] at h
    exact h

-- Handle c = 1 remainder
theorem c_drain_1 : ∀ a b,
    (⟨a, b + 1, 1, 0, 0⟩ : Q) [fm]⊢* ⟨a + 1, b + 3, 0, 1, 0⟩ := by
  intro a b; step fm; step fm; finish

-- Full drain even
theorem full_drain_even : ∀ k a b,
    (⟨a, b + 1, 2 * k, 0, 0⟩ : Q) [fm]⊢*
    ⟨a + b + 1 + 3 * (2 * k), 0, 0, 2 * (b + 1) + 5 * (2 * k), 0⟩ := by
  intro k a b
  have h0 := c_drain_2k k a b 0
  rw [show 0 + 2 * k = 2 * k from by ring] at h0
  apply stepStar_trans h0
  have h := b_drain (b + 1 + 5 * k) (a + k) 0
  rw [show 0 + 2 * (b + 1 + 5 * k) = 2 * (b + 1) + 5 * (2 * k) from by ring,
      show a + k + (b + 1 + 5 * k) = a + b + 1 + 3 * (2 * k) from by ring] at h
  exact h

-- Full drain odd
theorem full_drain_odd : ∀ k a b,
    (⟨a, b + 1, 2 * k + 1, 0, 0⟩ : Q) [fm]⊢*
    ⟨a + b + 1 + 3 * (2 * k + 1), 0, 0, 2 * (b + 1) + 5 * (2 * k + 1), 0⟩ := by
  intro k a b
  have h0 := c_drain_2k k a b 1
  rw [show 1 + 2 * k = 2 * k + 1 from by ring] at h0
  apply stepStar_trans h0
  have h1 := c_drain_1 (a + k) (b + 5 * k)
  rw [show b + 5 * k + 1 = b + 1 + 5 * k from by ring] at h1
  apply stepStar_trans h1
  step fm
  have h := b_drain (b + 5 * k + 2) (a + k + 2) 3
  rw [show 3 + 2 * (b + 5 * k + 2) = 2 * (b + 1) + 5 * (2 * k + 1) from by ring,
      show a + k + 2 + (b + 5 * k + 2) = a + b + 1 + 3 * (2 * k + 1) from by ring] at h
  exact h

-- General drain
theorem full_drain : ∀ c a b,
    (⟨a, b + 1, c, 0, 0⟩ : Q) [fm]⊢* ⟨a + b + 1 + 3 * c, 0, 0, 2 * (b + 1) + 5 * c, 0⟩ := by
  intro c a b
  rcases Nat.even_or_odd c with ⟨k, hk⟩ | ⟨k, hk⟩
  · rw [hk, show k + k = 2 * k from by ring]; exact full_drain_even k a b
  · rw [hk]; exact full_drain_odd k a b

-- Inner loop step: 4 rule2 + rule5 + rule1
theorem inner_step : ∀ a c e,
    (⟨a + 1, 4, c, 0, e + 4⟩ : Q) [fm]⊢* ⟨a, 4, c + 3, 0, e⟩ := by
  intro a c e
  step fm; step fm; step fm; step fm; step fm; step fm; ring_nf; finish

-- Inner loop iterated k times
theorem inner_loop : ∀ k a c e,
    (⟨a + k, 4, c, 0, e + 4 * k⟩ : Q) [fm]⊢* ⟨a, 4, c + 3 * k, 0, e⟩ := by
  intro k; induction k with
  | zero => intro a c e; simp; exists 0
  | succ k ih =>
    intro a c e
    rw [show e + 4 * (k + 1) = (e + 4 * k) + 4 from by ring,
        show a + (k + 1) = (a + k) + 1 from by ring]
    apply stepStar_trans (inner_step (a + k) c (e + 4 * k))
    rw [show c + 3 * (k + 1) = (c + 3) + 3 * k from by ring]
    exact ih a (c + 3) e

-- Phase 2: rule5, rule2, rule1
theorem phase2 : ∀ a d,
    (⟨a + 1, 0, 0, 0, d + 1⟩ : Q) [fm]⊢* ⟨a, 3, 0, 0, d⟩ := by
  intro a d; step fm; step fm; step fm; finish

-- Preamble for d >= 3: 3 rule2 + rule5 + rule1
theorem preamble_d3 : ∀ a f,
    (⟨a + 1, 3, 0, 0, f + 3⟩ : Q) [fm]⊢* ⟨a, 4, 2, 0, f⟩ := by
  intro a f; step fm; step fm; step fm; step fm; step fm; ring_nf; finish

-- rule4 drain
theorem d_to_e' : ∀ k a e,
    (⟨a, 0, 0, k, e⟩ : Q) [fm]⊢* ⟨a, 0, 0, 0, e + k⟩ := by
  intro k; induction k with
  | zero => intro a e; simp; exists 0
  | succ k ih =>
    intro a e; step fm
    rw [show e + (k + 1) = (e + 1) + k from by ring]
    exact ih a (e + 1)

-- rule2 drain: consume k steps of rule 2
theorem rule2_drain : ∀ k a b c e,
    (⟨a, b + k, c, 0, e + k⟩ : Q) [fm]⊢* ⟨a, b, c + k, 0, e⟩ := by
  intro k; induction k with
  | zero => intro a b c e; simp; exists 0
  | succ k ih =>
    intro a b c e
    rw [show b + (k + 1) = (b + k) + 1 from by ring,
        show e + (k + 1) = (e + k) + 1 from by ring]
    step fm
    rw [show c + (k + 1) = (c + 1) + k from by ring]
    exact ih a b (c + 1) e

-- Combined phase1+2: (a+1, 0, 0, d+1, 0) ⊢* (a, 3, 0, 0, d)
theorem full_phase12 : ∀ a d,
    (⟨a + 1, 0, 0, d + 1, 0⟩ : Q) [fm]⊢* ⟨a, 3, 0, 0, d⟩ := by
  intro a d
  have h1 := d_to_e' (d + 1) (a + 1) 0
  rw [show 0 + (d + 1) = d + 1 from by ring] at h1
  apply stepStar_trans h1
  exact phase2 a d

-- Transition d=1
theorem trans_1 : ∀ a, (⟨a + 1, 0, 0, 1, 0⟩ : Q) [fm]⊢⁺ ⟨a + 3, 0, 0, 6, 0⟩ := by
  intro a
  apply step_stepStar_stepPlus (show fm (a + 1, 0, 0, 1, 0) = some (a + 1, 0, 0, 0, 1) from rfl)
  apply stepStar_trans (phase2 a 0)
  exact b_drain 3 a 0

-- Transition d=2
theorem trans_2 : ∀ a, (⟨a + 1, 0, 0, 2, 0⟩ : Q) [fm]⊢⁺ ⟨a + 5, 0, 0, 9, 0⟩ := by
  intro a
  apply step_stepStar_stepPlus (show fm (a + 1, 0, 0, 2, 0) = some (a + 1, 0, 0, 1, 1) from rfl)
  step fm
  apply stepStar_trans (phase2 a 1)
  step fm
  have h := full_drain 1 a 1
  rw [show a + 1 + 1 + 3 * 1 = a + 5 from by ring,
      show 2 * (1 + 1) + 5 * 1 = 9 from by ring] at h
  exact h

-- Transition d=3
theorem trans_3 : ∀ a, (⟨a + 1, 0, 0, 3, 0⟩ : Q) [fm]⊢⁺ ⟨a + 7, 0, 0, 12, 0⟩ := by
  intro a
  apply step_stepStar_stepPlus (show fm (a + 1, 0, 0, 3, 0) = some (a + 1, 0, 0, 2, 1) from rfl)
  step fm; step fm
  apply stepStar_trans (phase2 a 2)
  apply stepStar_trans (rule2_drain 2 a 1 0 0)
  have h := full_drain 2 a 0
  rw [show a + 0 + 1 + 3 * 2 = a + 7 from by ring,
      show 2 * (0 + 1) + 5 * 2 = 12 from by ring] at h
  exact h

-- Helper: chain full_phase12 + preamble_d3 + inner_loop + rule2_drain r + full_drain
-- for the 4 remainder cases. Each starts with step_stepStar_stepPlus.

-- r=0: d = 4k+4
theorem trans_ge4_r0 : ∀ k a,
    (⟨a + k + 2, 0, 0, 4 * k + 4, 0⟩ : Q) [fm]⊢⁺
    ⟨a + 9 * k + 10, 0, 0, 15 * k + 18, 0⟩ := by
  intro k a
  apply step_stepStar_stepPlus
    (show fm (a + k + 2, 0, 0, 4 * k + 4, 0) = some (a + k + 2, 0, 0, 4 * k + 3, 1) from rfl)
  have h1 := d_to_e' (4 * k + 3) (a + k + 2) 1
  rw [show 1 + (4 * k + 3) = 4 * k + 4 from by ring] at h1
  apply stepStar_trans h1
  have h2 := phase2 (a + k + 1) (4 * k + 3)
  rw [show (a + k + 1) + 1 = a + k + 2 from by ring, show (4 * k + 3) + 1 = 4 * k + 4 from by ring] at h2
  apply stepStar_trans h2
  have h3 := preamble_d3 (a + k) (4 * k)
  rw [show (a + k) + 1 = a + k + 1 from by ring, show 4 * k + 3 = 4 * k + 3 from rfl] at h3
  apply stepStar_trans h3
  have h4 := inner_loop k a 2 0
  rw [show 0 + 4 * k = 4 * k from by ring] at h4
  apply stepStar_trans h4
  have h5 := full_drain (2 + 3 * k) a 3
  rw [show a + 3 + 1 + 3 * (2 + 3 * k) = a + 9 * k + 10 from by ring,
      show 2 * (3 + 1) + 5 * (2 + 3 * k) = 15 * k + 18 from by ring] at h5
  exact h5

-- r=1: d = 4k+5
theorem trans_ge4_r1 : ∀ k a,
    (⟨a + k + 2, 0, 0, 4 * k + 5, 0⟩ : Q) [fm]⊢⁺
    ⟨a + 9 * k + 12, 0, 0, 15 * k + 21, 0⟩ := by
  intro k a
  apply step_stepStar_stepPlus
    (show fm (a + k + 2, 0, 0, 4 * k + 5, 0) = some (a + k + 2, 0, 0, 4 * k + 4, 1) from rfl)
  have h1 := d_to_e' (4 * k + 4) (a + k + 2) 1
  rw [show 1 + (4 * k + 4) = 4 * k + 5 from by ring] at h1
  apply stepStar_trans h1
  have h2 := phase2 (a + k + 1) (4 * k + 4)
  rw [show (a + k + 1) + 1 = a + k + 2 from by ring, show (4 * k + 4) + 1 = 4 * k + 5 from by ring] at h2
  apply stepStar_trans h2
  have h3 := preamble_d3 (a + k) (4 * k + 1)
  rw [show (a + k) + 1 = a + k + 1 from by ring, show (4 * k + 1) + 3 = 4 * k + 4 from by ring] at h3
  apply stepStar_trans h3
  have h4 := inner_loop k a 2 1
  rw [show 1 + 4 * k = 4 * k + 1 from by ring] at h4
  apply stepStar_trans h4
  have h5 := rule2_drain 1 a 3 (2 + 3 * k) 0
  simp at h5
  rw [show 2 + 3 * k + 1 = 3 + 3 * k from by ring] at h5
  apply stepStar_trans h5
  have h6 := full_drain (3 + 3 * k) a 2
  rw [show a + 2 + 1 + 3 * (3 + 3 * k) = a + 9 * k + 12 from by ring,
      show 2 * (2 + 1) + 5 * (3 + 3 * k) = 15 * k + 21 from by ring] at h6
  exact h6

-- r=2: d = 4k+6
theorem trans_ge4_r2 : ∀ k a,
    (⟨a + k + 2, 0, 0, 4 * k + 6, 0⟩ : Q) [fm]⊢⁺
    ⟨a + 9 * k + 14, 0, 0, 15 * k + 24, 0⟩ := by
  intro k a
  apply step_stepStar_stepPlus
    (show fm (a + k + 2, 0, 0, 4 * k + 6, 0) = some (a + k + 2, 0, 0, 4 * k + 5, 1) from rfl)
  have h1 := d_to_e' (4 * k + 5) (a + k + 2) 1
  rw [show 1 + (4 * k + 5) = 4 * k + 6 from by ring] at h1
  apply stepStar_trans h1
  have h2 := phase2 (a + k + 1) (4 * k + 5)
  rw [show (a + k + 1) + 1 = a + k + 2 from by ring, show (4 * k + 5) + 1 = 4 * k + 6 from by ring] at h2
  apply stepStar_trans h2
  have h3 := preamble_d3 (a + k) (4 * k + 2)
  rw [show (a + k) + 1 = a + k + 1 from by ring, show (4 * k + 2) + 3 = 4 * k + 5 from by ring] at h3
  apply stepStar_trans h3
  have h4 := inner_loop k a 2 2
  rw [show 2 + 4 * k = 4 * k + 2 from by ring] at h4
  apply stepStar_trans h4
  have h5 := rule2_drain 2 a 2 (2 + 3 * k) 0
  simp at h5
  rw [show 2 + 3 * k + 2 = 4 + 3 * k from by ring] at h5
  apply stepStar_trans h5
  have h6 := full_drain (4 + 3 * k) a 1
  rw [show a + 1 + 1 + 3 * (4 + 3 * k) = a + 9 * k + 14 from by ring,
      show 2 * (1 + 1) + 5 * (4 + 3 * k) = 15 * k + 24 from by ring] at h6
  exact h6

-- r=3: d = 4k+7
theorem trans_ge4_r3 : ∀ k a,
    (⟨a + k + 2, 0, 0, 4 * k + 7, 0⟩ : Q) [fm]⊢⁺
    ⟨a + 9 * k + 16, 0, 0, 15 * k + 27, 0⟩ := by
  intro k a
  apply step_stepStar_stepPlus
    (show fm (a + k + 2, 0, 0, 4 * k + 7, 0) = some (a + k + 2, 0, 0, 4 * k + 6, 1) from rfl)
  have h1 := d_to_e' (4 * k + 6) (a + k + 2) 1
  rw [show 1 + (4 * k + 6) = 4 * k + 7 from by ring] at h1
  apply stepStar_trans h1
  have h2 := phase2 (a + k + 1) (4 * k + 6)
  rw [show (a + k + 1) + 1 = a + k + 2 from by ring, show (4 * k + 6) + 1 = 4 * k + 7 from by ring] at h2
  apply stepStar_trans h2
  have h3 := preamble_d3 (a + k) (4 * k + 3)
  rw [show (a + k) + 1 = a + k + 1 from by ring, show (4 * k + 3) + 3 = 4 * k + 6 from by ring] at h3
  apply stepStar_trans h3
  have h4 := inner_loop k a 2 3
  rw [show 3 + 4 * k = 4 * k + 3 from by ring] at h4
  apply stepStar_trans h4
  have h5 := rule2_drain 3 a 1 (2 + 3 * k) 0
  simp at h5
  rw [show 2 + 3 * k + 3 = 5 + 3 * k from by ring] at h5
  apply stepStar_trans h5
  have h6 := full_drain (5 + 3 * k) a 0
  rw [show a + 0 + 1 + 3 * (5 + 3 * k) = a + 9 * k + 16 from by ring,
      show 2 * (0 + 1) + 5 * (5 + 3 * k) = 15 * k + 27 from by ring] at h6
  exact h6

theorem main_progress : ∀ a d, a ≥ 1 → d ≥ 1 → 4 * a > d →
    ∃ a' d', a' ≥ 1 ∧ d' ≥ 1 ∧ 4 * a' > d' ∧
    (⟨a, 0, 0, d, 0⟩ : Q) [fm]⊢⁺ ⟨a', 0, 0, d', 0⟩ := by
  intro a d ha hd h4a
  match d, hd with
  | 1, _ =>
    obtain ⟨a', rfl⟩ : ∃ a', a = a' + 1 := ⟨a - 1, by omega⟩
    exact ⟨a' + 3, 6, by omega, by omega, by omega, trans_1 a'⟩
  | 2, _ =>
    obtain ⟨a', rfl⟩ : ∃ a', a = a' + 1 := ⟨a - 1, by omega⟩
    exact ⟨a' + 5, 9, by omega, by omega, by omega, trans_2 a'⟩
  | 3, _ =>
    obtain ⟨a', rfl⟩ : ∃ a', a = a' + 1 := ⟨a - 1, by omega⟩
    exact ⟨a' + 7, 12, by omega, by omega, by omega, trans_3 a'⟩
  | d' + 4, _ =>
    have hr : d' % 4 < 4 := Nat.mod_lt d' (by omega)
    have hd'eq : d' = 4 * (d' / 4) + d' % 4 := by omega
    obtain ⟨a'', rfl⟩ : ∃ a'', a = a'' + d' / 4 + 2 := ⟨a - d' / 4 - 2, by omega⟩
    set k := d' / 4 with hk_def
    set r := d' % 4 with hr_def
    -- Rewrite d' in the goal
    have hgoal_rw : d' + 4 = 4 * k + r + 4 := by omega
    interval_cases r
    · -- r = 0
      rw [show 4 * k + 0 + 4 = 4 * k + 4 from by ring] at hgoal_rw
      rw [hgoal_rw]
      exact ⟨a'' + 9 * k + 10, 15 * k + 18, by omega, by omega, by omega, trans_ge4_r0 k a''⟩
    · -- r = 1
      rw [show 4 * k + 1 + 4 = 4 * k + 5 from by ring] at hgoal_rw
      rw [hgoal_rw]
      exact ⟨a'' + 9 * k + 12, 15 * k + 21, by omega, by omega, by omega, trans_ge4_r1 k a''⟩
    · -- r = 2
      rw [show 4 * k + 2 + 4 = 4 * k + 6 from by ring] at hgoal_rw
      rw [hgoal_rw]
      exact ⟨a'' + 9 * k + 14, 15 * k + 24, by omega, by omega, by omega, trans_ge4_r2 k a''⟩
    · -- r = 3
      rw [show 4 * k + 3 + 4 = 4 * k + 7 from by ring] at hgoal_rw
      rw [hgoal_rw]
      exact ⟨a'' + 9 * k + 16, 15 * k + 27, by omega, by omega, by omega, trans_ge4_r3 k a''⟩

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := (⟨1, 0, 0, 3, 0⟩ : Q))
  · execute fm 2
  apply progress_nonhalt (fm := fm)
    (P := fun q ↦ ∃ a d, q = (⟨a, 0, 0, d, 0⟩ : Q) ∧ a ≥ 1 ∧ d ≥ 1 ∧ 4 * a > d)
  · intro c ⟨a, d, hq, ha, hd, h4a⟩
    subst hq
    obtain ⟨a', d', ha', hd', h4a', htrans⟩ := main_progress a d ha hd h4a
    exact ⟨⟨a', 0, 0, d', 0⟩, ⟨a', d', rfl, ha', hd', h4a'⟩, htrans⟩
  · exact ⟨1, 3, rfl, by omega, by omega, by omega⟩

end Sz22_2003_unofficial_440
