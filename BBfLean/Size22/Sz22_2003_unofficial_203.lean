import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #203: [1/6, 35/2, 4/385, 3/5, 242/21]

Vector representation:
```
-1 -1  0  0  0
-1  0  1  1  0
 2  0 -1 -1 -1
 0  1 -1  0  0
 1 -1  0 -1  2
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_203

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a+1, b+1, c, d, e⟩ => some ⟨a, b, c, d, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b, c+1, d+1, e⟩
  | ⟨a, b, c+1, d+1, e+1⟩ => some ⟨a+2, b, c, d, e⟩
  | ⟨a, b, c+1, d, e⟩ => some ⟨a, b+1, c, d, e⟩
  | ⟨a, b+1, c, d+1, e⟩ => some ⟨a+1, b, c, d, e+2⟩
  | _ => none

-- Phase 1: R4 repeated, convert c to b when e=0
theorem c_to_b : ∀ k b c d, ⟨0, b, c + k, d, 0⟩ [fm]⊢* ⟨0, b + k, c, d, 0⟩ := by
  intro k; induction k with
  | zero => intro b c d; exists 0
  | succ k ih =>
    intro b c d
    rw [show c + (k + 1) = (c + k) + 1 from by ring]
    step fm
    apply stepStar_trans (ih _ _ _)
    ring_nf; finish

-- Phase 2: R5/R1 pairs drain b, then final R5
theorem r5r1_pairs : ∀ k b d e, ⟨0, b + 2 * k, 0, d + k, e⟩ [fm]⊢* ⟨0, b, 0, d, e + 2 * k⟩ := by
  intro k; induction k with
  | zero => intro b d e; exists 0
  | succ k ih =>
    intro b d e
    rw [show b + 2 * (k + 1) = (b + 2 * k) + 1 + 1 from by ring,
        show d + (k + 1) = (d + k) + 1 from by ring]
    step fm
    step fm
    apply stepStar_trans (ih _ _ _)
    ring_nf; finish

theorem drain_b : ∀ k d e, ⟨0, 2 * k + 1, 0, d + k + 1, e⟩ [fm]⊢* ⟨1, 0, 0, d, e + 2 * k + 2⟩ := by
  intro k d e
  apply stepStar_trans (c₂ := ⟨0, 1, 0, d + 1, e + 2 * k⟩)
  · have h := r5r1_pairs k 1 (d + 1) e
    rw [show 1 + 2 * k = 2 * k + 1 from by ring,
        show d + 1 + k = d + k + 1 from by ring] at h; exact h
  step fm
  ring_nf; finish

-- Phase 3: R3,R2,R2 loop
theorem core_loop : ∀ k c D e, ⟨0, 0, c + 1, D + c + 1, e + k⟩ [fm]⊢* ⟨0, 0, c + 1 + k, D + c + 1 + k, e⟩ := by
  intro k; induction k with
  | zero => intro c D e; exists 0
  | succ k ih =>
    intro c D e
    rw [show e + (k + 1) = (e + k) + 1 from by ring]
    step fm
    step fm
    step fm
    apply stepStar_trans (ih _ _ _)
    ring_nf; finish

-- Phase 3 full: initial R2 then core_loop
theorem phase3 : ∀ D E, ⟨1, 0, 0, D, E⟩ [fm]⊢* ⟨0, 0, E + 1, D + E + 1, 0⟩ := by
  intro D E
  step fm
  apply stepStar_trans (c₂ := ⟨0, 0, 0 + 1 + E, D + 0 + 1 + E, 0⟩)
  · have h := core_loop E 0 D 0
    rw [show 0 + E = E from by ring] at h; exact h
  ring_nf; finish

-- Recursive definition of d-values: D(0)=1, D(n+1) = D(n) + n + 2
def D : ℕ → ℕ
  | 0 => 1
  | n + 1 => D n + n + 2

-- D(n) ≥ n + 1
theorem D_ge (n : ℕ) : D n ≥ n + 1 := by
  induction n with
  | zero => decide
  | succ n ih => unfold D; omega

-- Main transition
theorem main_trans (n : ℕ) : ⟨0, 0, 2 * n + 1, D n, 0⟩ [fm]⊢⁺ ⟨0, 0, 2 * (n + 1) + 1, D (n + 1), 0⟩ := by
  have hge := D_ge n
  -- Phase 1: c_to_b (all 2*n+1 steps)
  have hP1 := c_to_b (2 * n + 1) 0 0 (D n)
  simp only [Nat.zero_add] at hP1
  -- Phase 2: drain_b
  have hP2 := drain_b n (D n - n - 1) 0
  rw [show D n - n - 1 + n + 1 = D n from by omega] at hP2
  simp only [Nat.zero_add] at hP2
  -- Phase 3: phase3
  have hP3 := phase3 (D n - n - 1) (2 * n + 2)
  rw [show (2 * n + 2) + 1 = 2 * (n + 1) + 1 from by ring,
      show D n - n - 1 + (2 * n + 2) + 1 = D (n + 1) from by simp [D]; omega] at hP3
  -- Chain: ⊢* then ⊢* then ⊢* = ⊢*, need ⊢⁺
  -- Use stepStar_stepPlus: c₁ ≠ c₂ + ⊢* → ⊢⁺
  have hAll := stepStar_trans hP1 (stepStar_trans hP2 hP3)
  exact stepStar_stepPlus hAll (by intro h; have := congrArg (fun q : Q ↦ q.2.2.1) h; simp at this)

theorem nonhalt : ¬halts fm c₀ := by
  -- c₀ = (1, 0, 0, 0, 0), execute to reach (0, 0, 1, 1, 0) = C(0)
  apply stepStar_not_halts_not_halts (c₂ := ⟨0, 0, 1, 1, 0⟩) (by execute fm 1)
  -- D(0) = 1, so C(0) = (0, 0, 1, 1, 0)
  change ¬halts fm ⟨0, 0, 2 * 0 + 1, D 0, 0⟩
  apply progress_nonhalt_simple (fm := fm) (A := ℕ) (fun n ↦ ⟨0, 0, 2 * n + 1, D n, 0⟩) 0
  intro n; exact ⟨n + 1, main_trans n⟩

end Sz22_2003_unofficial_203
