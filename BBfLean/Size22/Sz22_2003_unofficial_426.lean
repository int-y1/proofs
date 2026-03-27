import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #426: [27/10, 55/21, 4/3, 7/11, 33/2]

Vector representation:
```
-1  3 -1  0  0
 0 -1  1 -1  1
 2 -1  0  0  0
 0  0  0  1 -1
-1  1  0  0  1
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_426

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a+1, b, c+1, d, e⟩ => some ⟨a, b+3, c, d, e⟩
  | ⟨a, b+1, c, d+1, e⟩ => some ⟨a, b, c+1, d, e+1⟩
  | ⟨a, b+1, c, d, e⟩ => some ⟨a+2, b, c, d, e⟩
  | ⟨a, b, c, d, e+1⟩ => some ⟨a, b, c, d+1, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b+1, c, d, e+1⟩
  | _ => none

lemma step_r1 : ⟨a+1, b, c+1, d, e⟩ [fm]⊢ ⟨a, b+3, c, d, e⟩ := by unfold fm; rfl
lemma step_r2 : ⟨a, b+1, 0, d+1, e⟩ [fm]⊢ ⟨a, b, 1, d, e+1⟩ := by unfold fm; simp only
lemma step_r3 : ⟨a, b+1, 0, 0, e⟩ [fm]⊢ ⟨a+2, b, 0, 0, e⟩ := by unfold fm; simp only
lemma step_r4 : ⟨a, 0, 0, d, e+1⟩ [fm]⊢ ⟨a, 0, 0, d+1, e⟩ := by unfold fm; simp only
lemma step_r5 : ⟨a+1, 0, 0, d, 0⟩ [fm]⊢ ⟨a, 1, 0, d, 1⟩ := by unfold fm; simp only

theorem e_to_d : ⟨a, 0, 0, d, e + k⟩ [fm]⊢* ⟨a, 0, 0, d + k, e⟩ := by
  have h : ∀ k d, ⟨a, 0, 0, d, e + k⟩ [fm]⊢* ⟨a, 0, 0, d + k, e⟩ := by
    intro k; induction k with
    | zero => intro d; exists 0
    | succ k ih =>
      intro d; rw [show e + (k + 1) = (e + k) + 1 from by ring]
      refine stepStar_trans (step_stepStar step_r4) ?_
      have := ih (d + 1)
      rw [show d + 1 + k = d + (k + 1) from by ring] at this; exact this
  exact h k d

theorem b_to_a : ⟨a, b + k, 0, 0, e⟩ [fm]⊢* ⟨a + 2 * k, b, 0, 0, e⟩ := by
  have h : ∀ k a, ⟨a, b + k, 0, 0, e⟩ [fm]⊢* ⟨a + 2 * k, b, 0, 0, e⟩ := by
    intro k; induction k with
    | zero => intro a; exists 0
    | succ k ih =>
      intro a; rw [show b + (k + 1) = (b + k) + 1 from by ring]
      refine stepStar_trans (step_stepStar step_r3) ?_
      have := ih (a + 2)
      rw [show a + 2 + 2 * k = a + 2 * (k + 1) from by ring] at this; exact this
  exact h k a

-- Consume loop: k+1 iterations of (R2, R1)
-- First component starts as a + k + 1 = (a+k)+1 which is always in succ form.
theorem consume_loop :
    ⟨a + k + 1, b + 1, 0, k + 1, e⟩ [fm]⊢* ⟨a, b + 3 + 2 * k, 0, 0, e + k + 1⟩ := by
  have h : ∀ k b a e, ⟨a + k + 1, b + 1, 0, k + 1, e⟩ [fm]⊢* ⟨a, b + 3 + 2 * k, 0, 0, e + k + 1⟩ := by
    intro k; induction k with
    | zero =>
      intro b a e
      exact stepStar_trans (step_stepStar step_r2) (step_stepStar step_r1)
    | succ k ih =>
      intro b a e
      rw [show a + (k + 1) + 1 = (a + k + 1) + 1 from by ring]
      refine stepStar_trans (step_stepStar step_r2) ?_
      refine stepStar_trans (step_stepStar step_r1) ?_
      rw [show b + 3 = (b + 2) + 1 from by ring]
      refine stepStar_trans (ih (b + 2) a (e + 1)) ?_
      ring_nf; finish
  exact h k b a e

theorem main_step {n : ℕ} (hn : n ≥ 1) :
    ⟨a + n + 1, 0, 0, 0, n⟩ [fm]⊢⁺ ⟨a + 4 * n + 2, 0, 0, 0, n + 1⟩ := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  show ⟨a + (m + 1) + 1, 0, 0, 0, m + 1⟩ [fm]⊢⁺ ⟨a + 4 * (m + 1) + 2, 0, 0, 0, m + 1 + 1⟩
  -- Phase 1: e_to_d: →* (a+m+2, 0, 0, m+1, 0)
  have he : ⟨a + (m + 1) + 1, 0, 0, 0, m + 1⟩ [fm]⊢*
            ⟨a + (m + 1) + 1, 0, 0, m + 1, 0⟩ := by
    have := @e_to_d (a + (m + 1) + 1) 0 0 (m + 1)
    simp only [Nat.zero_add] at this; exact this
  -- Phase 2: R5: →⁺ (a+m+1, 1, 0, m+1, 1)
  have hr5 : ⟨a + (m + 1) + 1, 0, 0, m + 1, 0⟩ [fm]⊢ ⟨a + m + 1, 1, 0, m + 1, 1⟩ := by
    rw [show a + (m + 1) + 1 = (a + m + 1) + 1 from by ring]; exact step_r5
  -- Phase 3: consume_loop (m + 1 iterations)
  -- (a+m+1, 1, 0, m+1, 1) = (a + m + 1, 0 + 1, 0, m + 1, 1)
  -- consume_loop with a' = a, k = m, b = 0, e = 1:
  -- (a + m + 1, 0 + 1, 0, m + 1, 1) →* (a, 0 + 3 + 2*m, 0, 0, 1 + m + 1)
  have hcl : ⟨a + m + 1, 1, 0, m + 1, 1⟩ [fm]⊢*
             ⟨a, 3 + 2 * m, 0, 0, m + 2⟩ := by
    rw [show (1 : ℕ) = 0 + 1 from by ring]
    refine stepStar_trans (consume_loop (a := a) (k := m) (b := 0) (e := 1)) ?_
    ring_nf; finish
  -- Phase 4: b_to_a
  have hba : ⟨a, 3 + 2 * m, 0, 0, m + 2⟩ [fm]⊢*
             ⟨a + 4 * (m + 1) + 2, 0, 0, 0, m + 1 + 1⟩ := by
    rw [show (3 + 2 * m : ℕ) = 0 + (3 + 2 * m) from by ring]
    refine stepStar_trans (b_to_a (a := a) (b := 0) (k := 3 + 2 * m) (e := m + 2)) ?_
    ring_nf; finish
  -- Combine: ⊢* then ⊢ then ⊢* then ⊢* = ⊢⁺
  exact stepStar_stepPlus_stepPlus he
    (step_stepStar_stepPlus hr5 (stepStar_trans hcl hba))

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨6, 0, 0, 0, 2⟩)
  · execute fm 9
  apply progress_nonhalt (fm := fm)
    (P := fun q ↦ ∃ a n, q = ⟨a, 0, 0, 0, n⟩ ∧ n ≥ 2 ∧ a ≥ n + 1)
  · intro c ⟨a, n, hq, hn, ha⟩; subst hq
    obtain ⟨m, rfl⟩ : ∃ m, a = m + n + 1 := ⟨a - n - 1, by omega⟩
    exact ⟨⟨m + 4 * n + 2, 0, 0, 0, n + 1⟩,
           ⟨m + 4 * n + 2, n + 1, rfl, by omega, by omega⟩,
           main_step (by omega)⟩
  · exact ⟨6, 2, rfl, by omega, by omega⟩
