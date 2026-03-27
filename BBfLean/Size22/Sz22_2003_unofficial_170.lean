import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #170: [1/45, 7/5, 50/77, 3/7, 605/2]

Vector representation:
```
 0 -2 -1  0  0
 0  0 -1  1  0
 1  0  2 -1 -1
 0  1  0 -1  0
-1  0  1  0  2
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_170

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a, b+2, c+1, d, e⟩ => some ⟨a, b, c, d, e⟩
  | ⟨a, b, c+1, d, e⟩ => some ⟨a, b, c, d+1, e⟩
  | ⟨a, b, c, d+1, e+1⟩ => some ⟨a+1, b, c+2, d, e⟩
  | ⟨a, b, c, d+1, e⟩ => some ⟨a, b+1, c, d, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b, c+1, d, e+2⟩
  | _ => none

-- Descent: rule 5 then rule 1, repeated k times
theorem descent : ∀ a e, ⟨a+1+k, 2*k, 0, 0, e⟩ [fm]⊢* ⟨a+1, 0, 0, 0, e+2*k⟩ := by
  induction k with
  | zero => intro a e; simp; finish
  | succ k ih =>
    intro a e
    rw [show 2 * (k + 1) = 2 * k + 2 from by ring,
        show a + 1 + (k + 1) = (a + 1 + k) + 1 from by ring]
    step fm; step fm
    apply stepStar_trans (ih a (e + 2))
    ring_nf; finish

-- Descent to b=1
theorem descent_b1 : ∀ a e, ⟨a+1+k, 2*k+1, 0, 0, e⟩ [fm]⊢* ⟨a+1, 1, 0, 0, e+2*k⟩ := by
  induction k with
  | zero => intro a e; simp; finish
  | succ k ih =>
    intro a e
    rw [show 2 * (k + 1) + 1 = (2 * k + 1) + 2 from by ring,
        show a + 1 + (k + 1) = (a + 1 + k) + 1 from by ring]
    step fm; step fm
    apply stepStar_trans (ih a (e + 2))
    ring_nf; finish

-- Growth bootstrap for b=0
theorem boot_b0 : ⟨a+1, 0, 0, 0, e⟩ [fm]⊢⁺ ⟨a+1, 0, 0, 2, e+1⟩ := by
  execute fm 5

-- Growth bootstrap for b=1
theorem boot_b1 : ⟨a+1, 1, 0, 0, e⟩ [fm]⊢⁺ ⟨a+1, 1, 0, 2, e+1⟩ := by
  execute fm 5

-- Growth main loop for b=0
theorem loop_b0 : ∀ a d, ⟨a, 0, 0, d+1, k⟩ [fm]⊢* ⟨a+k, 0, 0, d+1+k, 0⟩ := by
  induction k with
  | zero => intro a d; simp; finish
  | succ k ih =>
    intro a d
    rw [show d + 1 + (k + 1) = (d + 1) + 1 + k from by ring]
    step fm; step fm; step fm
    apply stepStar_trans (ih (a + 1) (d + 1))
    ring_nf; finish

-- Growth main loop for b=1
theorem loop_b1 : ∀ a d, ⟨a, 1, 0, d+1, k⟩ [fm]⊢* ⟨a+k, 1, 0, d+1+k, 0⟩ := by
  induction k with
  | zero => intro a d; simp; finish
  | succ k ih =>
    intro a d
    rw [show d + 1 + (k + 1) = (d + 1) + 1 + k from by ring]
    step fm; step fm; step fm
    apply stepStar_trans (ih (a + 1) (d + 1))
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

-- Full growth for b=0: (a+1, 0, 0, 0, e) →⁺ (a+e+2, e+3, 0, 0, 0)
theorem growth_b0 : ⟨a+1, 0, 0, 0, e⟩ [fm]⊢⁺ ⟨a+e+2, e+3, 0, 0, 0⟩ := by
  apply stepPlus_stepStar_stepPlus boot_b0
  rw [show (2 : ℕ) = 0 + 1 + 1 from by ring]
  apply stepStar_trans (loop_b0 (a+1) 1)
  apply stepStar_trans (drain 0)
  ring_nf; finish

-- Full growth for b=1: (a+1, 1, 0, 0, e) →⁺ (a+e+2, e+4, 0, 0, 0)
theorem growth_b1 : ⟨a+1, 1, 0, 0, e⟩ [fm]⊢⁺ ⟨a+e+2, e+4, 0, 0, 0⟩ := by
  apply stepPlus_stepStar_stepPlus boot_b1
  rw [show (2 : ℕ) = 0 + 1 + 1 from by ring]
  apply stepStar_trans (loop_b1 (a+1) 1)
  apply stepStar_trans (drain 1)
  ring_nf; finish

-- Cycle b0: (a+1, 0, 0, 0, 2*n) →⁺ ((n+a)+1, 1, 0, 0, 2*(n+1))
theorem cycle_b0 : ⟨a+1, 0, 0, 0, 2*n⟩ [fm]⊢⁺ ⟨(n+a)+1, 1, 0, 0, 2*(n+1)⟩ := by
  have hg := @growth_b0 a (2*n)
  apply stepPlus_stepStar_stepPlus hg
  rw [show a + 2 * n + 2 = (n + a) + 1 + (n + 1) from by ring,
      show 2 * n + 3 = 2 * (n + 1) + 1 from by ring]
  apply stepStar_trans (descent_b1 (n + a) 0)
  ring_nf; finish

-- Cycle b1: (a+1, 1, 0, 0, 2*(n+1)) →⁺ ((n+a)+1, 0, 0, 0, 2*(n+3))
theorem cycle_b1 : ⟨a+1, 1, 0, 0, 2*(n+1)⟩ [fm]⊢⁺ ⟨(n+a)+1, 0, 0, 0, 2*(n+3)⟩ := by
  have hg := @growth_b1 a (2*(n+1))
  apply stepPlus_stepStar_stepPlus hg
  rw [show a + 2 * (n + 1) + 2 = (n + a) + 1 + (n + 3) from by ring,
      show 2 * (n + 1) + 4 = 2 * (n + 3) from by ring]
  apply stepStar_trans (descent (n + a) 0)
  ring_nf; finish

theorem nonhalt : ¬halts fm c₀ := by
  apply progress_nonhalt (fm := fm)
    (P := fun q ↦ (∃ a n, q = ⟨a+1, 0, 0, 0, 2*n⟩) ∨ (∃ a n, q = ⟨a+1, 1, 0, 0, 2*(n+1)⟩))
  · intro c hc
    rcases hc with ⟨a, n, rfl⟩ | ⟨a, n, rfl⟩
    · exact ⟨_, Or.inr ⟨n+a, n, rfl⟩, cycle_b0⟩
    · exact ⟨_, Or.inl ⟨n+a, n+3, rfl⟩, cycle_b1⟩
  · exact Or.inl ⟨0, 0, rfl⟩

end Sz22_2003_unofficial_170
