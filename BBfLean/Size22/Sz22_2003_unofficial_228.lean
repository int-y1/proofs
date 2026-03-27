import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #228: [11/105, 10/3, 27/55, 7/2, 55/7]

Vector representation:
```
 0 -1 -1 -1  1
 1 -1  1  0  0
 0  3 -1  0 -1
-1  0  0  1  0
 0  0  1 -1  1
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6 (1M context)
-/

namespace Sz22_2003_unofficial_228

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a, b+1, c+1, d+1, e⟩ => some ⟨a, b, c, d, e+1⟩
  | ⟨a, b+1, c, d, e⟩ => some ⟨a+1, b, c+1, d, e⟩
  | ⟨a, b, c+1, d, e+1⟩ => some ⟨a, b+3, c, d, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b, c, d+1, e⟩
  | ⟨a, b, c, d+1, e⟩ => some ⟨a, b, c+1, d, e+1⟩
  | _ => none

-- R4 chain: (k, 0, c, d, 0) →* (0, 0, c, d+k, 0)
theorem r4_chain : ∀ k c d, ⟨k, 0, c, d, 0⟩ [fm]⊢* ⟨0, 0, c, d+k, 0⟩ := by
  intro k; induction k with
  | zero => intro c d; simp; exists 0
  | succ k ih =>
    intro c d
    have h1 : fm ⟨k + 1, 0, c, d, 0⟩ = some ⟨k, 0, c, d + 1, 0⟩ := by simp [fm]
    have h2 := ih c (d + 1)
    rw [show d + 1 + k = d + (k + 1) from by ring] at h2
    exact stepStar_trans (step_stepStar h1) h2

-- Burn step: (0, 0, c+4, d+3, e+1) →* (0, 0, c, d, e+3) in 4 steps
theorem burn_step : ⟨0, 0, c+4, d+3, e+1⟩ [fm]⊢* ⟨0, 0, c, d, e+3⟩ := by
  apply stepStar_trans (step_stepStar (by show fm ⟨0, 0, (c+3)+1, d+3, (e)+1⟩ = some ⟨0, 0+3, c+3, d+3, e⟩; simp [fm]))
  apply stepStar_trans (step_stepStar (by show fm ⟨0, (0+2)+1, (c+2)+1, (d+2)+1, e⟩ = some ⟨0, 0+2, c+2, d+2, e+1⟩; simp [fm]))
  apply stepStar_trans (step_stepStar (by show fm ⟨0, (0+1)+1, (c+1)+1, (d+1)+1, e+1⟩ = some ⟨0, 0+1, c+1, d+1, (e+1)+1⟩; simp [fm]))
  apply step_stepStar; show fm ⟨0, 0+1, (c)+1, (d)+1, (e+1)+1⟩ = some ⟨0, 0, c, d, ((e+1)+1)+1⟩; simp [fm]

-- Burn loop repeated k times
theorem burn_loop : ∀ k c d e, ⟨0, 0, c+4*k, d+3*k, e+1⟩ [fm]⊢* ⟨0, 0, c, d, e+2*k+1⟩ := by
  intro k; induction k with
  | zero => intro c d e; simp; exists 0
  | succ k ih =>
    intro c d e
    rw [show c + 4 * (k + 1) = (c + 4 * k) + 4 from by ring,
        show d + 3 * (k + 1) = (d + 3 * k) + 3 from by ring]
    exact stepStar_trans burn_step
      (by rw [show e + 3 = (e + 2) + 1 from by ring]
          have := ih c d (e + 2)
          rw [show (e + 2) + 2 * k + 1 = e + 2 * (k + 1) + 1 from by ring] at this; exact this)

-- Accumulate step: (a, 0, 1, d+1, e+1) →* (a+2, 0, 1, d, e+1) in 4 steps
theorem accum_step : ⟨a, 0, 1, d+1, e+1⟩ [fm]⊢* ⟨a+2, 0, 1, d, e+1⟩ := by
  apply stepStar_trans (step_stepStar (by show fm ⟨a, 0, 0+1, d+1, (e)+1⟩ = some ⟨a, 0+3, 0, d+1, e⟩; simp [fm]))
  apply stepStar_trans (step_stepStar (by show fm ⟨a, (0+2)+1, 0, d+1, e⟩ = some ⟨a+1, 0+2, 0+1, d+1, e⟩; simp [fm]))
  apply stepStar_trans (step_stepStar (by show fm ⟨a+1, (0+1)+1, 0+1, (d)+1, e⟩ = some ⟨a+1, 0+1, 0, d, e+1⟩; simp [fm]))
  apply step_stepStar; show fm ⟨a+1, 0+1, 0, d, e+1⟩ = some ⟨(a+1)+1, 0, 0+1, d, e+1⟩; simp [fm]

-- Accumulate loop
theorem accum_loop : ∀ k a e, ⟨a, 0, 1, k, e+1⟩ [fm]⊢* ⟨a+2*k, 0, 1, 0, e+1⟩ := by
  intro k; induction k with
  | zero => intro a e; simp; exists 0
  | succ k ih =>
    intro a e
    have h1 := @accum_step a k e
    have h2 := ih (a + 2) e
    rw [show a + 2 + 2 * k = a + 2 * (k + 1) from by ring] at h2
    exact stepStar_trans h1 h2

-- Build step: (a, 0, c+1, 0, e+1) →* (a+3, 0, c+3, 0, e) in 4 steps
theorem build_step : ⟨a, 0, c+1, 0, e+1⟩ [fm]⊢* ⟨a+3, 0, c+3, 0, e⟩ := by
  apply stepStar_trans (step_stepStar (by show fm ⟨a, 0, (c)+1, 0, (e)+1⟩ = some ⟨a, 0+3, c, 0, e⟩; simp [fm]))
  apply stepStar_trans (step_stepStar (by show fm ⟨a, (0+2)+1, c, 0, e⟩ = some ⟨a+1, 0+2, c+1, 0, e⟩; simp [fm]))
  apply stepStar_trans (step_stepStar (by show fm ⟨a+1, (0+1)+1, c+1, 0, e⟩ = some ⟨(a+1)+1, 0+1, (c+1)+1, 0, e⟩; simp [fm]))
  apply step_stepStar; show fm ⟨(a+1)+1, 0+1, (c+1)+1, 0, e⟩ = some ⟨((a+1)+1)+1, 0, ((c+1)+1)+1, 0, e⟩; simp [fm]

-- Build loop
theorem build_loop : ∀ k a c, ⟨a, 0, c+1, 0, k+1⟩ [fm]⊢* ⟨a+3*(k+1), 0, c+2*(k+1)+1, 0, 0⟩ := by
  intro k; induction k with
  | zero =>
    intro a c
    have h := @build_step a c 0
    rw [show a + 3 = a + 3 * 1 from by ring, show c + 3 = c + 2 * 1 + 1 from by ring] at h
    exact h
  | succ k ih =>
    intro a c
    have h1 := @build_step a c (k + 1)
    rw [show c + 3 = (c + 2) + 1 from by ring] at h1
    have h2 := ih (a + 3) (c + 2)
    rw [show a + 3 + 3 * (k + 1) = a + 3 * (k + 1 + 1) from by ring,
        show c + 2 + 2 * (k + 1) + 1 = c + 2 * (k + 1 + 1) + 1 from by ring] at h2
    exact stepStar_trans h1 h2

-- Residual r=0: (0, 0, 0, d+1, e+1) →* (0, 0, 1, d, e+2) in 1 step via R5
theorem res0 : ⟨0, 0, 0, d+1, e+1⟩ [fm]⊢* ⟨0, 0, 1, d, e+2⟩ := by
  apply step_stepStar; show fm ⟨0, 0, 0, (d)+1, e+1⟩ = some ⟨0, 0, 0+1, d, (e+1)+1⟩; simp [fm]

-- Residual r=2: (0, 0, 2, d+2, e+1) →* (0, 0, 1, d, e+3) in 6 steps
theorem res2 : ⟨0, 0, 2, d+2, e+1⟩ [fm]⊢* ⟨0, 0, 1, d, e+3⟩ := by
  apply stepStar_trans (step_stepStar (by show fm ⟨0, 0, (0+1)+1, d+2, (e)+1⟩ = some ⟨0, 0+3, 0+1, d+2, e⟩; simp [fm]))
  apply stepStar_trans (step_stepStar (by show fm ⟨0, (0+2)+1, 0+1, (d+1)+1, e⟩ = some ⟨0, 0+2, 0, d+1, e+1⟩; simp [fm]))
  apply stepStar_trans (step_stepStar (by show fm ⟨0, (0+1)+1, 0, d+1, e+1⟩ = some ⟨0+1, 0+1, 0+1, d+1, e+1⟩; simp [fm]))
  apply stepStar_trans (step_stepStar (by show fm ⟨0+1, 0+1, 0+1, (d)+1, e+1⟩ = some ⟨0+1, 0, 0, d, (e+1)+1⟩; simp [fm]))
  apply stepStar_trans (step_stepStar (by show fm ⟨0+1, 0, 0, d, (e+1)+1⟩ = some ⟨0, 0, 0, d+1, (e+1)+1⟩; simp [fm]))
  apply step_stepStar; show fm ⟨0, 0, 0, (d)+1, (e+1)+1⟩ = some ⟨0, 0, 0+1, d, ((e+1)+1)+1⟩; simp [fm]

-- Composite: build E+1 steps then R4 chain
-- (a, 0, 1, 0, E+1) →* (0, 0, 2*E+3, a+3*(E+1), 0)
theorem build_r4 (E a : ℕ) : ⟨a, 0, 1, 0, E+1⟩ [fm]⊢* ⟨0, 0, 2*E+3, a+3*(E+1), 0⟩ := by
  have h1 := build_loop E a 0
  rw [show 0 + 2 * (E + 1) + 1 = 2 * E + 3 from by ring] at h1
  simp only [Nat.zero_add] at h1
  have h2 := r4_chain (a + 3 * (E + 1)) (2 * E + 3) 0
  rw [show 0 + (a + 3 * (E + 1)) = a + 3 * (E + 1) from by ring] at h2
  exact stepStar_trans h1 h2

-- R5 step
theorem r5_step' (c d : ℕ) : ⟨0, 0, c, d+1, 0⟩ [fm]⊢* ⟨0, 0, c+1, d, 1⟩ := by
  apply step_stepStar; show fm ⟨0, 0, c, (d)+1, 0⟩ = some ⟨0, 0, c+1, d, 0+1⟩; simp [fm]

-- Even macro: (a, 0, 1, 0, 2*(m+1)) →⁺ (0, 0, 1, a+3*m, 2*m+5)
-- where m ≥ 1 (so e = 2*(m+1) ≥ 4)
-- Build 2*(m+1) = (2*m+1)+1 steps: → (a+3*(2*m+2), 0, 2*(2*m+1)+3, 0, 0) = (a+6m+6, 0, 4m+5, 0, 0)
-- R4: → (0, 0, 4m+5, a+6m+6, 0)
-- R5: → (0, 0, 4m+6, a+6m+5, 1)
-- Burn (m+1) times with residual 2: → (0, 0, 2, a+3m+2, 2m+3)
-- Res2: → (0, 0, 1, a+3m, 2m+5)
theorem macro_even (a m : ℕ) (hm : m ≥ 1) :
    ⟨a, 0, 1, 0, 2*(m+1)⟩ [fm]⊢⁺ ⟨0, 0, 1, a+3*m, 2*m+5⟩ := by
  -- build + R4
  have h1 := build_r4 (2*m+1) a
  rw [show 2 * (2 * m + 1) + 3 = 4 * m + 5 from by ring,
      show a + 3 * (2 * m + 1 + 1) = a + 6 * m + 6 from by ring,
      show (2 * m + 1) + 1 = 2 * (m + 1) from by ring] at h1
  -- R5
  have h2 := r5_step' (4 * m + 5) (a + 6 * m + 5)
  rw [show (a + 6 * m + 5) + 1 = a + 6 * m + 6 from by ring,
      show (4 * m + 5) + 1 = 4 * m + 6 from by ring] at h2
  -- Burn (m+1) times
  have h3 := burn_loop (m + 1) 2 (a + 3 * m + 2) 0
  rw [show 2 + 4 * (m + 1) = 4 * m + 6 from by ring,
      show (a + 3 * m + 2) + 3 * (m + 1) = a + 6 * m + 5 from by ring,
      show 0 + 2 * (m + 1) + 1 = 2 * m + 3 from by ring] at h3
  -- Res2
  have h4 := @res2 (a + 3 * m) (2 * m + 2)
  rw [show (a + 3 * m) + 2 = a + 3 * m + 2 from by ring,
      show (2 * m + 2) + 1 = 2 * m + 3 from by ring,
      show (2 * m + 2) + 3 = 2 * m + 5 from by ring] at h4
  exact stepStar_stepPlus
    (stepStar_trans h1 (stepStar_trans h2 (stepStar_trans h3 h4)))
    (by simp only [Q, ne_eq, Prod.mk.injEq, not_and]; omega)

-- Odd macro: (a, 0, 1, 0, 2*m+1) →⁺ (0, 0, 1, a+3*m-2, 2*m+4)
-- where m ≥ 2 (so e = 2*m+1 ≥ 5)
-- Build (2*m+1) = (2*m)+1 steps: → (a+3*(2*m+1), 0, 2*(2*m)+3, 0, 0) = (a+6m+3, 0, 4m+3, 0, 0)
-- R4: → (0, 0, 4m+3, a+6m+3, 0)
-- R5: → (0, 0, 4m+4, a+6m+2, 1)
-- Burn (m+1) times with residual 0: → (0, 0, 0, a+3m-1, 2m+3)
-- Res0: → (0, 0, 1, a+3m-2, 2m+4)
theorem macro_odd (a m : ℕ) (hm : m ≥ 2) :
    ⟨a, 0, 1, 0, 2*m+1⟩ [fm]⊢⁺ ⟨0, 0, 1, a+3*m-2, 2*m+4⟩ := by
  -- build + R4
  have h1 := build_r4 (2*m) a
  rw [show 2 * (2 * m) + 3 = 4 * m + 3 from by ring,
      show a + 3 * (2 * m + 1) = a + 6 * m + 3 from by ring,
      show (2 * m) + 1 = 2 * m + 1 from by ring] at h1
  -- R5
  have h2 := r5_step' (4 * m + 3) (a + 6 * m + 2)
  rw [show (a + 6 * m + 2) + 1 = a + 6 * m + 3 from by ring,
      show (4 * m + 3) + 1 = 4 * m + 4 from by ring] at h2
  -- Burn (m+1) times
  have h3 := burn_loop (m + 1) 0 (a + 3 * m - 1) 0
  rw [show 0 + 4 * (m + 1) = 4 * m + 4 from by ring,
      show (a + 3 * m - 1) + 3 * (m + 1) = a + 6 * m + 2 from by omega,
      show 0 + 2 * (m + 1) + 1 = 2 * m + 3 from by ring] at h3
  -- Res0
  have h4 := @res0 (a + 3 * m - 2) (2 * m + 2)
  rw [show (a + 3 * m - 2) + 1 = a + 3 * m - 1 from by omega,
      show (2 * m + 2) + 1 = 2 * m + 3 from by ring,
      show (2 * m + 2) + 2 = 2 * m + 4 from by ring] at h4
  exact stepStar_stepPlus
    (stepStar_trans h1 (stepStar_trans h2 (stepStar_trans h3 h4)))
    (by simp only [Q, ne_eq, Prod.mk.injEq, not_and]; omega)

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨3, 0, 1, 0, 4⟩)
  · execute fm 42
  apply progress_nonhalt (fm := fm)
    (P := fun q ↦ ∃ a d e, q = ⟨a, 0, 1, d, e⟩ ∧ e ≥ 4)
  · intro c ⟨a, d, e, hq, he⟩; subst hq
    rcases d with _ | d
    · -- d = 0: full macro
      rcases Nat.even_or_odd e with ⟨m, hm⟩ | ⟨m, hm⟩
      · -- e even: e = m + m
        subst hm
        have hm2 : m ≥ 2 := by omega
        obtain ⟨m', rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
        rw [show m' + 1 + (m' + 1) = 2 * (m' + 1) from by ring]
        exact ⟨⟨0, 0, 1, a + 3 * m', 2 * m' + 5⟩,
               ⟨0, a + 3 * m', 2 * m' + 5, rfl, by omega⟩,
               macro_even a m' (by omega)⟩
      · -- e odd: e = 2*m + 1
        subst hm
        have hm2 : m ≥ 2 := by omega
        exact ⟨⟨0, 0, 1, a + 3 * m - 2, 2 * m + 4⟩,
               ⟨0, a + 3 * m - 2, 2 * m + 4, rfl, by omega⟩,
               macro_odd a m hm2⟩
    · -- d ≥ 1: accumulate step
      obtain ⟨e', rfl⟩ : ∃ e', e = e' + 1 := ⟨e - 1, by omega⟩
      exact ⟨⟨a + 2, 0, 1, d, e' + 1⟩,
             ⟨a + 2, d, e' + 1, rfl, by omega⟩,
             stepStar_stepPlus accum_step (by simp only [Q, ne_eq, Prod.mk.injEq, not_and]; omega)⟩
  · exact ⟨3, 0, 4, rfl, by omega⟩

end Sz22_2003_unofficial_228
