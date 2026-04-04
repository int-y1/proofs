import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #1871: [9/35, 25/66, 14/3, 11/7, 9/2]

Vector representation:
```
 0  2 -1 -1  0
-1 -1  2  0 -1
 1 -1  0  1  0
 0  0  0 -1  1
-1  2  0  0  0
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_1871

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a, b, c+1, d+1, e⟩ => some ⟨a, b+2, c, d, e⟩
  | ⟨a+1, b+1, c, d, e+1⟩ => some ⟨a, b, c+2, d, e⟩
  | ⟨a, b+1, c, d, e⟩ => some ⟨a+1, b, c, d+1, e⟩
  | ⟨a, b, c, d+1, e⟩ => some ⟨a, b, c, d, e+1⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b+2, c, d, e⟩
  | _ => none

theorem d_to_e : ∀ k, ∀ a e, ⟨a, 0, 0, k, e⟩ [fm]⊢* ⟨a, 0, 0, 0, e + k⟩ := by
  intro k; induction k with
  | zero => intro a e; simp; exists 0
  | succ k ih =>
    intro a e
    have h : fm ⟨a, 0, 0, k + 1, e⟩ = some ⟨a, 0, 0, k, e + 1⟩ := by simp [fm]
    apply stepStar_trans (step_stepStar h)
    apply stepStar_trans (ih a (e + 1))
    rw [show e + 1 + k = e + (k + 1) from by ring]; finish

theorem r5r2r2_step : ⟨a + 3, 0, c, 0, e + 2⟩ [fm]⊢⁺ ⟨a, 0, c + 4, 0, e⟩ := by
  step fm; step fm; step fm; finish

theorem r5r2r2_chain : ∀ k, ∀ a c, ⟨a + 3 * k, 0, c, 0, 2 * k⟩ [fm]⊢* ⟨a, 0, c + 4 * k, 0, 0⟩ := by
  intro k; induction k with
  | zero => intro a c; exists 0
  | succ k ih =>
    intro a c
    have h : ⟨a + 3 * (k + 1), 0, c, 0, 2 * (k + 1)⟩ [fm]⊢⁺ ⟨a + 3 * k, 0, c + 4, 0, 2 * k⟩ := by
      rw [show a + 3 * (k + 1) = (a + 3 * k) + 3 from by ring,
          show 2 * (k + 1) = 2 * k + 2 from by ring]
      exact r5r2r2_step
    apply stepStar_trans (stepPlus_stepStar h)
    apply stepStar_trans (ih a (c + 4))
    rw [show c + 4 + 4 * k = c + 4 * (k + 1) from by ring]; finish

theorem r3r1_step : ⟨a, b + 2, n + 1, 0, 0⟩ [fm]⊢⁺ ⟨a + 1, b + 3, n, 0, 0⟩ := by
  step fm; step fm; finish

theorem r3r1_chain : ∀ n, ∀ a b, ⟨a, b + 2, n, 0, 0⟩ [fm]⊢* ⟨a + n, b + n + 2, 0, 0, 0⟩ := by
  intro n; induction n with
  | zero => intro a b; exists 0
  | succ n ih =>
    intro a b
    apply stepStar_trans (stepPlus_stepStar (r3r1_step (a := a) (b := b) (n := n)))
    rw [show b + 3 = (b + 1) + 2 from by ring]
    apply stepStar_trans (ih (a + 1) (b + 1))
    ring_nf; finish

theorem b_to_d : ∀ k, ∀ a d, ⟨a, k, 0, d, 0⟩ [fm]⊢* ⟨a + k, 0, 0, d + k, 0⟩ := by
  intro k; induction k with
  | zero => intro a d; exists 0
  | succ k ih =>
    intro a d
    have h : fm ⟨a, k + 1, 0, d, 0⟩ = some ⟨a + 1, k, 0, d + 1, 0⟩ := by simp [fm]
    apply stepStar_trans (step_stepStar h)
    apply stepStar_trans (ih (a + 1) (d + 1))
    ring_nf; finish

theorem main_trans (F D : ℕ) : ⟨F + 3 * D + 4, 0, 0, 2 * D + 2, 0⟩ [fm]⊢⁺
    ⟨F + 8 * D + 10, 0, 0, 4 * D + 6, 0⟩ := by
  -- Phase 1: d to e
  have p1 : ⟨F + 3 * D + 4, 0, 0, 2 * D + 2, 0⟩ [fm]⊢*
      ⟨F + 3 * D + 4, 0, 0, 0, 2 * D + 2⟩ := by
    apply stepStar_trans (d_to_e (2 * D + 2) (F + 3 * D + 4) 0)
    ring_nf; finish
  -- Phase 2: R5+R2+R2 drain (D+1 rounds)
  have p2 : ⟨F + 3 * D + 4, 0, 0, 0, 2 * D + 2⟩ [fm]⊢⁺
      ⟨F + 1, 0, 4 * D + 4, 0, 0⟩ := by
    rw [show F + 3 * D + 4 = (F + 1 + 3 * D) + 3 from by ring,
        show 2 * D + 2 = 2 * D + 2 from rfl]
    apply stepPlus_stepStar_stepPlus r5r2r2_step
    apply stepStar_trans (r5r2r2_chain D (F + 1) 4)
    rw [show 4 + 4 * D = 4 * D + 4 from by ring]; finish
  -- Phase 3: R5 then R3+R1 chain
  have p3 : ⟨F + 1, 0, 4 * D + 4, 0, 0⟩ [fm]⊢⁺
      ⟨F + 4 * D + 4, 4 * D + 6, 0, 0, 0⟩ := by
    rw [show F + 1 = F + 0 + 1 from by ring]
    step fm
    apply stepStar_trans (r3r1_chain (4 * D + 4) F 0)
    ring_nf; finish
  -- Phase 4: b to d
  have p4 : ⟨F + 4 * D + 4, 4 * D + 6, 0, 0, 0⟩ [fm]⊢*
      ⟨F + 8 * D + 10, 0, 0, 4 * D + 6, 0⟩ := by
    apply stepStar_trans (b_to_d (4 * D + 6) (F + 4 * D + 4) 0)
    ring_nf; finish
  exact stepStar_stepPlus_stepPlus p1 (stepPlus_stepStar_stepPlus (stepPlus_trans p2 p3) p4)

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨7, 0, 0, 4, 0⟩)
  · execute fm 20
  apply progress_nonhalt_simple (fm := fm) (A := ℕ × ℕ)
    (fun ⟨F, D⟩ ↦ ⟨F + 3 * D + 4, 0, 0, 2 * D + 2, 0⟩) ⟨0, 1⟩
  intro ⟨F, D⟩
  refine ⟨⟨F + 2 * D, 2 * D + 2⟩, ?_⟩
  show ⟨F + 3 * D + 4, 0, 0, 2 * D + 2, 0⟩ [fm]⊢⁺
    ⟨F + 2 * D + 3 * (2 * D + 2) + 4, 0, 0, 2 * (2 * D + 2) + 2, 0⟩
  rw [show F + 2 * D + 3 * (2 * D + 2) + 4 = F + 8 * D + 10 from by ring,
      show 2 * (2 * D + 2) + 2 = 4 * D + 6 from by ring]
  exact main_trans F D
