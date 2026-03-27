import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #305: [15/2, 44/21, 5/3, 7/275, 22/5]

Vector representation:
```
-1  1  1  0  0
 2 -1  0 -1  1
 0 -1  1  0  0
 0  0 -2  1 -1
 1  0 -1  0  1
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_305

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b+1, c+1, d, e⟩
  | ⟨a, b+1, c, d+1, e⟩ => some ⟨a+2, b, c, d, e+1⟩
  | ⟨a, b+1, c, d, e⟩ => some ⟨a, b, c+1, d, e⟩
  | ⟨a, b, c+2, d, e+1⟩ => some ⟨a, b, c, d+1, e⟩
  | ⟨a, b, c+1, d, e⟩ => some ⟨a+1, b, c, d, e+1⟩
  | _ => none

-- Rule 3 repeated: drain b to c when d=0
theorem drain_b (b e : ℕ) : ∀ k c,
    (⟨(0:ℕ), b+k, c, 0, e⟩ : Q) [fm]⊢* ⟨0, b, c+k, 0, e⟩ := by
  intro k; induction k with
  | zero => intro c; exists 0
  | succ k ih =>
    intro c
    rw [show b + (k + 1) = (b + k) + 1 from by ring]
    step fm
    apply stepStar_trans (ih _)
    ring_nf; finish

-- Rule 4 repeated: convert c,e to d
theorem convert_ce (e : ℕ) : ∀ k c d,
    (⟨(0:ℕ), 0, c + 2 * k, d, e + k⟩ : Q) [fm]⊢* ⟨0, 0, c, d + k, e⟩ := by
  intro k; induction k with
  | zero => intro c d; exists 0
  | succ k ih =>
    intro c d
    have h : fm ⟨0, 0, (c + 2*k) + 2, d, (e + k) + 1⟩ = some ⟨0, 0, c + 2*k, d+1, e + k⟩ := by
      unfold fm; simp
    rw [show c + 2 * (k + 1) = (c + 2 * k) + 2 from by ring,
        show e + (k + 1) = (e + k) + 1 from by ring]
    exact stepStar_trans (step_stepStar h)
      (by apply stepStar_trans (ih c (d+1)); ring_nf; finish)

-- Build phase: one R2+R1+R1 iteration
theorem build_step (k C D : ℕ) :
    (⟨0, k+1, C, D+1, k+1⟩ : Q) [fm]⊢⁺ ⟨0, k+2, C+2, D, k+2⟩ := by
  step fm; step fm; execute fm 1

-- Build phase: d iterations of R2+R1+R1
theorem build_loop : ∀ d C k,
    (⟨0, k+1, C, d, k+1⟩ : Q) [fm]⊢* ⟨0, k+1+d, C+2*d, 0, k+1+d⟩ := by
  intro d; induction d with
  | zero => intro C k; simp; exists 0
  | succ d ih =>
    intro C k
    apply stepStar_trans (stepPlus_stepStar (build_step k C d))
    apply stepStar_trans (ih _ (k+1))
    ring_nf; finish

-- Initial 2 steps: R5 then R1
theorem init_steps (c d : ℕ) :
    (⟨0, 0, c+1, d, 0⟩ : Q) [fm]⊢⁺ ⟨0, 1, c+1, d, 1⟩ := by
  step fm; step fm; finish

-- Full cycle: (0, 0, c+1, d+2, 0) →⁺ (0, 0, c+d+2, d+3, 0)
theorem full_cycle (c d : ℕ) :
    (⟨0, 0, c+1, d+2, 0⟩ : Q) [fm]⊢⁺ ⟨0, 0, c+d+2, d+3, 0⟩ := by
  apply stepPlus_stepStar_stepPlus (init_steps c (d+2))
  -- Goal: (0, 1, c+1, d+2, 1) ⊢* (0, 0, c+d+2, d+3, 0)
  -- Phase 1: Build loop
  have hbuild : (⟨0, 0+1, (c+1)+2*0, d+2, 0+1⟩ : Q) [fm]⊢*
      ⟨0, 0+1+(d+2), (c+1)+2*(d+2), 0, 0+1+(d+2)⟩ := build_loop (d+2) (c+1) 0
  simp only [Nat.zero_add] at hbuild
  apply stepStar_trans hbuild
  -- Now at (0, d+3, c+2*d+5, 0, d+3)
  -- Phase 2: Drain b
  have hdrain : (⟨0, 0+(d+3), (c+2*d+5)+0, 0, d+3⟩ : Q) [fm]⊢*
      ⟨0, 0, (c+2*d+5)+0+(d+3), 0, d+3⟩ := drain_b 0 (d+3) (d+3) (c+2*d+5+0)
  simp only [Nat.zero_add, Nat.add_zero] at hdrain
  rw [show (1 + (d + 2) : ℕ) = d + 3 from by ring,
      show (c + 1 + 2 * (d + 2) : ℕ) = c + 2 * d + 5 from by ring]
  apply stepStar_trans hdrain
  -- Now at (0, 0, c+3*d+8, 0, d+3)
  -- Phase 3: Convert c,e to d
  have hconv : (⟨0, 0, (c+d+2)+2*(d+3), 0, 0+(d+3)⟩ : Q) [fm]⊢*
      ⟨0, 0, c+d+2, 0+(d+3), 0⟩ := convert_ce 0 (d+3) (c+d+2) 0
  simp only [Nat.zero_add] at hconv
  rw [show c + 2 * d + 5 + (d + 3) = (c + d + 2) + 2 * (d + 3) from by ring]
  exact hconv

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := (⟨0, 0, 1, 2, 0⟩ : Q))
  · execute fm 15
  apply progress_nonhalt (fm := fm)
    (P := fun q ↦ ∃ c d, q = (⟨0, 0, c+1, d+2, 0⟩ : Q))
  · intro q ⟨c, d, hq⟩; subst hq
    exact ⟨⟨0, 0, c+d+2, d+3, 0⟩, ⟨c+d+1, d+1, by ring_nf⟩, full_cycle c d⟩
  · exact ⟨0, 0, by rfl⟩
