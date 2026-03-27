import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #416: [25/63, 7/55, 242/7, 3/11, 35/2]

Vector representation:
```
 0 -2  2 -1  0
 0  0 -1  1 -1
 1  0  0 -1  2
 0  1  0  0 -1
-1  0  1  1  0
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_416

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a, b+2, c, d+1, e⟩ => some ⟨a, b, c+2, d, e⟩
  | ⟨a, b, c+1, d, e+1⟩ => some ⟨a, b, c, d+1, e⟩
  | ⟨a, b, c, d+1, e⟩ => some ⟨a+1, b, c, d, e+2⟩
  | ⟨a, b, c, d, e+1⟩ => some ⟨a, b+1, c, d, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b, c+1, d+1, e⟩
  | _ => none

theorem r3_chain : ⟨a, 0, 0, d+k, e⟩ [fm]⊢* ⟨a+k, 0, 0, d, e+2*k⟩ := by
  induction k generalizing a e with
  | zero => exists 0
  | succ k ih =>
    rw [show d + (k + 1) = (d + k) + 1 from by ring]
    step fm
    apply stepStar_trans (ih (a := a + 1) (e := e + 2))
    ring_nf; finish

theorem r4_chain : ⟨a, b, 0, 0, k⟩ [fm]⊢* ⟨a, b+k, 0, 0, 0⟩ := by
  induction k generalizing b with
  | zero => exists 0
  | succ k ih =>
    step fm
    apply stepStar_trans (ih (b := b + 1))
    ring_nf; finish

theorem r3_chain_b1 : ⟨a, 1, 0, d+k, e⟩ [fm]⊢* ⟨a+k, 1, 0, d, e+2*k⟩ := by
  induction k generalizing a e with
  | zero => exists 0
  | succ k ih =>
    rw [show d + (k + 1) = (d + k) + 1 from by ring]
    step fm
    apply stepStar_trans (ih (a := a + 1) (e := e + 2))
    ring_nf; finish

theorem descent_even : ⟨a+k, 2*k, c, 0, 0⟩ [fm]⊢* ⟨a, 0, c+3*k, 0, 0⟩ := by
  induction k generalizing a c with
  | zero => exists 0
  | succ k ih =>
    rw [show a + (k + 1) = (a + k) + 1 from by ring,
        show 2 * (k + 1) = 2 * k + 2 from by ring]
    step fm; step fm
    apply stepStar_trans (ih (a := a) (c := c + 3))
    ring_nf; finish

theorem descent_odd : ⟨a+k+1, 2*k+1, c, 0, 0⟩ [fm]⊢* ⟨a+1, 1, c+3*k, 0, 0⟩ := by
  induction k generalizing a c with
  | zero => exists 0
  | succ k ih =>
    rw [show a + (k + 1) + 1 = (a + k + 1) + 1 from by ring,
        show 2 * (k + 1) + 1 = (2 * k + 1) + 2 from by ring]
    step fm; step fm
    apply stepStar_trans (ih (a := a) (c := c + 3))
    ring_nf; finish

theorem inner_step_b0 : ⟨a, 0, c+2, d+1, 0⟩ [fm]⊢* ⟨a+1, 0, c, d+2, (0:ℕ)⟩ := by
  step fm; step fm; step fm; finish

theorem inner_loop_b0 : ⟨a, 0, 2*k, d+1, 0⟩ [fm]⊢* ⟨a+k, 0, 0, d+k+1, 0⟩ := by
  induction k generalizing a d with
  | zero => exists 0
  | succ k ih =>
    rw [show 2 * (k + 1) = 2 * k + 2 from by ring]
    apply stepStar_trans inner_step_b0
    apply stepStar_trans (ih (a := a + 1) (d := d + 1))
    ring_nf; finish

theorem inner_loop_b0_odd : ⟨a, 0, 2*k+1, d+1, 0⟩ [fm]⊢* ⟨a+k, 0, 1, d+k+1, 0⟩ := by
  induction k generalizing a d with
  | zero => exists 0
  | succ k ih =>
    rw [show 2 * (k + 1) + 1 = (2 * k + 1) + 2 from by ring]
    apply stepStar_trans inner_step_b0
    apply stepStar_trans (ih (a := a + 1) (d := d + 1))
    ring_nf; finish

theorem inner_step_b1 : ⟨a, 1, c+2, d+1, 0⟩ [fm]⊢* ⟨a+1, 1, c, d+2, (0:ℕ)⟩ := by
  step fm; step fm; step fm; finish

theorem inner_loop_b1 : ⟨a, 1, 2*k, d+1, 0⟩ [fm]⊢* ⟨a+k, 1, 0, d+k+1, 0⟩ := by
  induction k generalizing a d with
  | zero => exists 0
  | succ k ih =>
    rw [show 2 * (k + 1) = 2 * k + 2 from by ring]
    apply stepStar_trans inner_step_b1
    apply stepStar_trans (ih (a := a + 1) (d := d + 1))
    ring_nf; finish

theorem inner_loop_b1_odd : ⟨a, 1, 2*k+1, d+1, 0⟩ [fm]⊢* ⟨a+k, 1, 1, d+k+1, 0⟩ := by
  induction k generalizing a d with
  | zero => exists 0
  | succ k ih =>
    rw [show 2 * (k + 1) + 1 = (2 * k + 1) + 2 from by ring]
    apply stepStar_trans inner_step_b1
    apply stepStar_trans (ih (a := a + 1) (d := d + 1))
    ring_nf; finish

-- Climb b=0, c=0
theorem climb_b0_zero : ⟨m+1, 0, 0, 0, 0⟩ [fm]⊢⁺ ⟨m+2, 3, 0, 0, 0⟩ := by
  execute fm 7

-- Climb b=0, c odd = 2j+1
theorem climb_b0_odd : ⟨m+1, 0, 2*j+1, 0, 0⟩ [fm]⊢⁺ ⟨m+2*j+3, 2*j+4, 0, 0, 0⟩ := by
  rw [show 2 * j + 1 = (2 * j) + 1 from by ring]
  -- 4 setup steps: (m+1, 0, 2j+1, 0, 0) -> (m+1, 0, 2j, 2, 0)
  step fm; step fm; step fm; step fm
  rw [show (2 : ℕ) = 1 + 1 from by ring]
  apply stepStar_trans (inner_loop_b0 (k := j) (a := m + 1) (d := 1))
  rw [show m + 1 + j = m + j + 1 from by ring,
      show 1 + j + 1 = 0 + (j + 2) from by ring]
  apply stepStar_trans (r3_chain (k := j + 2) (a := m + j + 1) (d := 0) (e := 0))
  apply stepStar_trans (r4_chain (k := 0 + 2 * (j + 2)) (a := m + j + 1 + (j + 2)) (b := 0))
  ring_nf; finish

-- Climb b=0, c even = 2*(j+1)
theorem climb_b0_even : ⟨m+1, 0, 2*(j+1), 0, 0⟩ [fm]⊢⁺ ⟨m+2*j+4, 2*j+5, 0, 0, 0⟩ := by
  rw [show 2 * (j + 1) = (2 * j + 1) + 1 from by ring]
  step fm; step fm; step fm; step fm
  rw [show (2 : ℕ) = 1 + 1 from by ring]
  apply stepStar_trans (inner_loop_b0_odd (k := j) (a := m + 1) (d := 1))
  rw [show m + 1 + j = m + j + 1 from by ring,
      show 1 + j + 1 = j + 2 from by ring]
  step fm; step fm
  rw [show j + 2 = 0 + (j + 2) from by ring]
  apply stepStar_trans (r3_chain (k := j + 2) (a := m + j + 2) (d := 0) (e := 1))
  apply stepStar_trans (r4_chain (k := 1 + 2 * (j + 2)) (a := m + j + 2 + (j + 2)) (b := 0))
  ring_nf; finish

-- Climb b=1, c=0
theorem climb_b1_zero : ⟨m+1, 1, 0, 0, 0⟩ [fm]⊢⁺ ⟨m+2, 4, 0, 0, 0⟩ := by
  execute fm 7

-- Climb b=1, c odd = 2j+1
theorem climb_b1_odd : ⟨m+1, 1, 2*j+1, 0, 0⟩ [fm]⊢⁺ ⟨m+2*j+3, 2*j+5, 0, 0, 0⟩ := by
  rw [show 2 * j + 1 = (2 * j) + 1 from by ring]
  step fm; step fm; step fm; step fm
  rw [show (2 : ℕ) = 1 + 1 from by ring]
  apply stepStar_trans (inner_loop_b1 (k := j) (a := m + 1) (d := 1))
  rw [show m + 1 + j = m + j + 1 from by ring,
      show 1 + j + 1 = 0 + (j + 2) from by ring]
  apply stepStar_trans (r3_chain_b1 (k := j + 2) (a := m + j + 1) (d := 0) (e := 0))
  apply stepStar_trans (r4_chain (k := 0 + 2 * (j + 2)) (a := m + j + 1 + (j + 2)) (b := 1))
  ring_nf; finish

-- Climb b=1, c even = 2*(j+1)
theorem climb_b1_even : ⟨m+1, 1, 2*(j+1), 0, 0⟩ [fm]⊢⁺ ⟨m+2*j+4, 2*j+6, 0, 0, 0⟩ := by
  rw [show 2 * (j + 1) = (2 * j + 1) + 1 from by ring]
  step fm; step fm; step fm; step fm
  rw [show (2 : ℕ) = 1 + 1 from by ring]
  apply stepStar_trans (inner_loop_b1_odd (k := j) (a := m + 1) (d := 1))
  rw [show m + 1 + j = m + j + 1 from by ring,
      show 1 + j + 1 = j + 2 from by ring]
  step fm; step fm
  rw [show j + 2 = 0 + (j + 2) from by ring]
  apply stepStar_trans (r3_chain_b1 (k := j + 2) (a := m + j + 2) (d := 0) (e := 1))
  apply stepStar_trans (r4_chain (k := 1 + 2 * (j + 2)) (a := m + j + 2 + (j + 2)) (b := 1))
  ring_nf; finish

-- Combined cycle lemmas (climb then descent)
theorem cycle_b0_odd :
    ⟨m+1, 0, 2*j+1, 0, 0⟩ [fm]⊢⁺ ⟨m+j+1, 0, 3*j+6, 0, 0⟩ := by
  apply stepPlus_stepStar_stepPlus (climb_b0_odd (m := m) (j := j))
  rw [show m + 2 * j + 3 = (m + j + 1) + (j + 2) from by ring,
      show 2 * j + 4 = 2 * (j + 2) from by ring]
  have h := descent_even (a := m + j + 1) (k := j + 2) (c := 0)
  rw [show 0 + 3 * (j + 2) = 3 * j + 6 from by ring] at h; exact h

theorem cycle_b0_even :
    ⟨m+1, 0, 2*(j+1), 0, 0⟩ [fm]⊢⁺ ⟨m+j+2, 1, 3*j+6, 0, 0⟩ := by
  apply stepPlus_stepStar_stepPlus (climb_b0_even (m := m) (j := j))
  rw [show m + 2 * j + 4 = (m + j + 1) + (j + 2) + 1 from by ring,
      show 2 * j + 5 = 2 * (j + 2) + 1 from by ring]
  have h := descent_odd (a := m + j + 1) (k := j + 2) (c := 0)
  rw [show (m + j + 1) + 1 = m + j + 2 from by ring,
      show 0 + 3 * (j + 2) = 3 * j + 6 from by ring] at h; exact h

theorem cycle_b0_zero :
    ⟨m+1, 0, 0, 0, 0⟩ [fm]⊢⁺ ⟨m+1, 1, 3, 0, 0⟩ := by
  apply stepPlus_stepStar_stepPlus climb_b0_zero
  rw [show m + 2 = (m + 0) + 1 + 1 from by ring, show (3:ℕ) = 2 * 1 + 1 from by ring]
  have h := descent_odd (a := m + 0) (k := 1) (c := 0)
  rw [show (m + 0) + 1 = m + 1 from by ring, show 0 + 3 * 1 = 3 from by ring] at h; exact h

theorem cycle_b1_odd :
    ⟨m+1, 1, 2*j+1, 0, 0⟩ [fm]⊢⁺ ⟨m+j+1, 1, 3*j+6, 0, 0⟩ := by
  apply stepPlus_stepStar_stepPlus (climb_b1_odd (m := m) (j := j))
  rw [show m + 2 * j + 3 = (m + j) + (j + 2) + 1 from by ring,
      show 2 * j + 5 = 2 * (j + 2) + 1 from by ring]
  have h := descent_odd (a := m + j) (k := j + 2) (c := 0)
  rw [show (m + j) + 1 = m + j + 1 from by ring,
      show 0 + 3 * (j + 2) = 3 * j + 6 from by ring] at h; exact h

theorem cycle_b1_even :
    ⟨m+1, 1, 2*(j+1), 0, 0⟩ [fm]⊢⁺ ⟨m+j+1, 0, 3*j+9, 0, 0⟩ := by
  apply stepPlus_stepStar_stepPlus (climb_b1_even (m := m) (j := j))
  rw [show m + 2 * j + 4 = (m + j + 1) + (j + 3) from by ring,
      show 2 * j + 6 = 2 * (j + 3) from by ring]
  have h := descent_even (a := m + j + 1) (k := j + 3) (c := 0)
  rw [show 0 + 3 * (j + 3) = 3 * j + 9 from by ring] at h; exact h

theorem cycle_b1_zero :
    ⟨m+1, 1, 0, 0, 0⟩ [fm]⊢⁺ ⟨m, 0, 6, 0, 0⟩ := by
  apply stepPlus_stepStar_stepPlus climb_b1_zero
  rw [show m + 2 = m + 2 from rfl, show (4:ℕ) = 2 * 2 from by ring]
  have h := descent_even (a := m) (k := 2) (c := 0)
  rw [show 0 + 3 * 2 = 6 from by ring] at h; exact h

theorem nonhalt : ¬halts fm c₀ := by
  apply progress_nonhalt (fm := fm)
    (P := fun q ↦
      (∃ m c₁, q = ⟨m+1, 0, c₁, 0, 0⟩) ∨
      (∃ m c₁, q = ⟨m+1, 1, c₁, 0, 0⟩ ∧ m + c₁ ≥ 1))
  · intro q hq
    rcases hq with ⟨m, c₁, rfl⟩ | ⟨m, c₁, rfl, hmc⟩
    · -- Case r=0: (m+1, 0, c₁, 0, 0)
      rcases c₁ with _ | c₁
      · exact ⟨_, Or.inr ⟨m, 3, rfl, by omega⟩, cycle_b0_zero⟩
      rcases Nat.even_or_odd c₁ with ⟨j, hj⟩ | ⟨j, hj⟩
      · -- c₁ = j + j, so c₁ + 1 = 2j + 1
        subst hj; rw [show j + j + 1 = 2 * j + 1 from by ring]
        exact ⟨_, Or.inl ⟨m+j, 3*j+6, by ring_nf⟩, cycle_b0_odd⟩
      · -- c₁ = 2j + 1, so c₁ + 1 = 2*(j+1)
        subst hj; rw [show 2 * j + 1 + 1 = 2 * (j + 1) from by ring]
        exact ⟨_, Or.inr ⟨m+j+1, 3*j+6, by constructor <;> [ring_nf; omega]⟩, cycle_b0_even⟩
    · -- Case r=1: (m+1, 1, c₁, 0, 0) with m + c₁ >= 1
      rcases c₁ with _ | c₁
      · have hm : m ≥ 1 := by omega
        have hm1 : m - 1 + 1 = m := Nat.sub_add_cancel hm
        exact ⟨_, Or.inl ⟨m-1, 6, by rw [hm1]⟩, cycle_b1_zero⟩
      rcases Nat.even_or_odd c₁ with ⟨j, hj⟩ | ⟨j, hj⟩
      · subst hj; rw [show j + j + 1 = 2 * j + 1 from by ring]
        exact ⟨_, Or.inr ⟨m+j, 3*j+6, by constructor <;> [ring_nf; omega]⟩, cycle_b1_odd⟩
      · subst hj; rw [show 2 * j + 1 + 1 = 2 * (j + 1) from by ring]
        exact ⟨_, Or.inl ⟨m+j, 3*j+9, by ring_nf⟩, cycle_b1_even⟩
  · exact Or.inl ⟨0, 0, rfl⟩

end Sz22_2003_unofficial_416
