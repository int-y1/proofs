import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #179: [1/45, 98/5, 25/77, 3/7, 55/2]

Vector representation:
```
 0 -2 -1  0  0
 1  0 -1  2  0
 0  0  2 -1 -1
 0  1  0 -1  0
-1  0  1  0  1
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_179

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a, b+2, c+1, d, e⟩ => some ⟨a, b, c, d, e⟩
  | ⟨a, b, c+1, d, e⟩ => some ⟨a+1, b, c, d+2, e⟩
  | ⟨a, b, c, d+1, e+1⟩ => some ⟨a, b, c+2, d, e⟩
  | ⟨a, b, c, d+1, e⟩ => some ⟨a, b+1, c, d, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b, c+1, d, e+1⟩
  | _ => none

-- Growth loop for b=0: R3, R2, R2 repeated k times
theorem growth_b0 : ∀ a d, ⟨a, 0, 0, d+1, k⟩ [fm]⊢* ⟨a+2*k, 0, 0, d+1+3*k, 0⟩ := by
  induction k with
  | zero => intro a d; simp; finish
  | succ k ih =>
    intro a d
    rw [show d + 1 + 3 * (k + 1) = (d + 3) + 1 + 3 * k from by ring]
    step fm; step fm; step fm
    apply stepStar_trans (ih (a + 2) (d + 3))
    ring_nf; finish

-- Growth loop for b=1
theorem growth_b1 : ∀ a d, ⟨a, 1, 0, d+1, k⟩ [fm]⊢* ⟨a+2*k, 1, 0, d+1+3*k, 0⟩ := by
  induction k with
  | zero => intro a d; simp; finish
  | succ k ih =>
    intro a d
    rw [show d + 1 + 3 * (k + 1) = (d + 3) + 1 + 3 * k from by ring]
    step fm; step fm; step fm
    apply stepStar_trans (ih (a + 2) (d + 3))
    ring_nf; finish

-- Drain d to b (rule 4 repeated)
theorem drain : ∀ b, ⟨a, b, 0, k, 0⟩ [fm]⊢* ⟨a, b+k, 0, 0, 0⟩ := by
  induction k with
  | zero => intro b; simp; finish
  | succ k ih =>
    intro b
    step fm
    apply stepStar_trans (ih (b + 1))
    ring_nf; finish

-- Descent with even b
theorem descent_even : ∀ a e, ⟨a+k, 2*k, 0, 0, e⟩ [fm]⊢* ⟨a, 0, 0, 0, e+k⟩ := by
  induction k with
  | zero => intro a e; simp; finish
  | succ k ih =>
    intro a e
    rw [show 2 * (k + 1) = 2 * k + 2 from by ring,
        show a + (k + 1) = (a + k) + 1 from by ring]
    step fm; step fm
    apply stepStar_trans (ih a (e + 1))
    ring_nf; finish

-- Descent with odd b
theorem descent_odd : ∀ a e, ⟨a+k, 2*k+1, 0, 0, e⟩ [fm]⊢* ⟨a, 1, 0, 0, e+k⟩ := by
  induction k with
  | zero => intro a e; simp; finish
  | succ k ih =>
    intro a e
    rw [show 2 * (k + 1) + 1 = (2 * k + 1) + 2 from by ring,
        show a + (k + 1) = (a + k) + 1 from by ring]
    step fm; step fm
    apply stepStar_trans (ih a (e + 1))
    ring_nf; finish

-- Bootstrap for b=0
theorem boot_b0 : ⟨a+1, 0, 0, 0, e⟩ [fm]⊢⁺ ⟨a+1, 0, 0, 2, e+1⟩ := by
  execute fm 2

-- Bootstrap for b=1
theorem boot_b1 : ⟨a+1, 1, 0, 0, e⟩ [fm]⊢⁺ ⟨a+1, 1, 0, 2, e+1⟩ := by
  execute fm 2

-- Full growth for b=0
theorem full_growth_b0 : ⟨a+1, 0, 0, 0, e⟩ [fm]⊢⁺ ⟨a+2*e+3, 3*e+5, 0, 0, 0⟩ := by
  apply stepPlus_stepStar_stepPlus boot_b0
  rw [show (2 : ℕ) = 0 + 1 + 1 from by ring]
  apply stepStar_trans (growth_b0 (a + 1) 1)
  apply stepStar_trans (drain 0)
  ring_nf; finish

-- Full growth for b=1
theorem full_growth_b1 : ⟨a+1, 1, 0, 0, e⟩ [fm]⊢⁺ ⟨a+2*e+3, 3*e+6, 0, 0, 0⟩ := by
  apply stepPlus_stepStar_stepPlus boot_b1
  rw [show (2 : ℕ) = 0 + 1 + 1 from by ring]
  apply stepStar_trans (growth_b1 (a + 1) 1)
  apply stepStar_trans (drain 1)
  ring_nf; finish

-- Cycle 1: b=0, E=2*n → b=1, E'=3*n+2
theorem cycle_b0_even : ⟨a+1, 0, 0, 0, 2*n⟩ [fm]⊢⁺ ⟨(a+n)+1, 1, 0, 0, 3*n+2⟩ := by
  have hg := @full_growth_b0 a (2 * n)
  apply stepPlus_stepStar_stepPlus hg
  rw [show a + 2 * (2 * n) + 3 = (a + n) + 1 + (3 * n + 2) from by ring,
      show 3 * (2 * n) + 5 = 2 * (3 * n + 2) + 1 from by ring]
  apply stepStar_trans (descent_odd ((a + n) + 1) 0)
  ring_nf; finish

-- Cycle 2: b=0, E=2*n+1 → b=0, E'=3*n+4
theorem cycle_b0_odd : ⟨a+1, 0, 0, 0, 2*n+1⟩ [fm]⊢⁺ ⟨(a+n)+1, 0, 0, 0, 3*n+4⟩ := by
  have hg := @full_growth_b0 a (2 * n + 1)
  apply stepPlus_stepStar_stepPlus hg
  rw [show a + 2 * (2 * n + 1) + 3 = (a + n) + 1 + (3 * n + 4) from by ring,
      show 3 * (2 * n + 1) + 5 = 2 * (3 * n + 4) from by ring]
  apply stepStar_trans (descent_even ((a + n) + 1) 0)
  ring_nf; finish

-- Cycle 3: b=1, E=2*m+2 → b=0, E'=3*m+6
theorem cycle_b1_even : ⟨a+1, 1, 0, 0, 2*m+2⟩ [fm]⊢⁺ ⟨(a+m)+1, 0, 0, 0, 3*m+6⟩ := by
  have hg := @full_growth_b1 a (2 * m + 2)
  apply stepPlus_stepStar_stepPlus hg
  rw [show a + 2 * (2 * m + 2) + 3 = (a + m) + 1 + (3 * m + 6) from by ring,
      show 3 * (2 * m + 2) + 6 = 2 * (3 * m + 6) from by ring]
  apply stepStar_trans (descent_even ((a + m) + 1) 0)
  ring_nf; finish

-- Cycle 4: b=1, E=2*m+3 → b=1, E'=3*m+7
theorem cycle_b1_odd : ⟨a+1, 1, 0, 0, 2*m+3⟩ [fm]⊢⁺ ⟨(a+m+1)+1, 1, 0, 0, 3*m+7⟩ := by
  have hg := @full_growth_b1 a (2 * m + 3)
  apply stepPlus_stepStar_stepPlus hg
  rw [show a + 2 * (2 * m + 3) + 3 = (a + m + 1) + 1 + (3 * m + 7) from by ring,
      show 3 * (2 * m + 3) + 6 = 2 * (3 * m + 7) + 1 from by ring]
  apply stepStar_trans (descent_odd ((a + m + 1) + 1) 0)
  ring_nf; finish

theorem nonhalt : ¬halts fm c₀ := by
  apply progress_nonhalt (fm := fm)
    (P := fun q ↦ (∃ a e, q = ⟨a+1, 0, 0, 0, e⟩) ∨ (∃ a e, q = ⟨a+1, 1, 0, 0, e+2⟩))
  · intro c hc
    rcases hc with ⟨a, e, rfl⟩ | ⟨a, e, rfl⟩
    · -- b=0 case: split on parity of e
      rcases Nat.even_or_odd e with ⟨n, hn⟩ | ⟨n, hn⟩
      · -- e even: e = n + n
        rw [show n + n = 2 * n from by ring] at hn; subst hn
        exact ⟨_, Or.inr ⟨a + n, 3 * n, by ring_nf⟩, cycle_b0_even⟩
      · -- e odd: e = 2 * n + 1
        subst hn
        exact ⟨_, Or.inl ⟨a + n, 3 * n + 4, rfl⟩, cycle_b0_odd⟩
    · -- b=1 case: state is (a+1, 1, 0, 0, e+2), split on parity of e
      rcases Nat.even_or_odd e with ⟨m, hm⟩ | ⟨m, hm⟩
      · -- e even: e = m + m, so e+2 = 2*m+2
        rw [show m + m = 2 * m from by ring] at hm; subst hm
        exact ⟨_, Or.inl ⟨a + m, 3 * m + 6, rfl⟩, cycle_b1_even⟩
      · -- e odd: e = 2*m+1, so e+2 = 2*m+3
        subst hm
        exact ⟨_, Or.inr ⟨a + m + 1, 3 * m + 5, by ring_nf⟩, cycle_b1_odd⟩
  · exact Or.inl ⟨0, 0, rfl⟩

end Sz22_2003_unofficial_179
