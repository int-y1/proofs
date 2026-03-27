import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #111: [1/30, 63/2, 4/77, 5/7, 242/5]

Vector representation:
```
-1 -1 -1  0  0
-1  2  0  1  0
 2  0  0 -1 -1
 0  0  1 -1  0
 1  0 -1  0  2
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_111

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a+1, b+1, c+1, d, e⟩ => some ⟨a, b, c, d, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b+2, c, d+1, e⟩
  | ⟨a, b, c, d+1, e+1⟩ => some ⟨a+2, b, c, d, e⟩
  | ⟨a, b, c, d+1, e⟩ => some ⟨a, b, c+1, d, e⟩
  | ⟨a, b, c+1, d, e⟩ => some ⟨a+1, b, c, d, e+2⟩
  | _ => none

-- R4 repeated: d → c
theorem d_to_c : ∀ k, ∀ b c, ⟨0, b, c, k, 0⟩ [fm]⊢* ⟨(0 : ℕ), b, c + k, 0, 0⟩ := by
  intro k; induction k with
  | zero => intro b c; exists 0
  | succ k ih =>
    intro b c
    rw [show k + 1 = (k) + 1 from by ring]
    step fm
    apply stepStar_trans (ih _ _)
    ring_nf; finish

-- R5/R1 chain: consume pairs from c, building up e
theorem c_consume : ∀ k, ∀ b e, ⟨0, b + k, 2 * k + 1, 0, e⟩ [fm]⊢* ⟨(1 : ℕ), b, 0, 0, e + 2 * k + 2⟩ := by
  intro k; induction k with
  | zero =>
    intro b e
    step fm
    ring_nf; finish
  | succ k ih =>
    intro b e
    rw [show b + (k + 1) = (b + k) + 1 from by ring,
        show 2 * (k + 1) + 1 = (2 * k + 1) + 1 + 1 from by ring]
    step fm; step fm
    rw [show e + 2 * (k + 1) + 2 = (e + 2) + 2 * k + 2 from by ring]
    exact ih b (e + 2)

-- R3,R2,R2 loop: consume e, building d
theorem r3r2r2_loop : ∀ k, ∀ b d, ⟨0, b, 0, d + 1, k⟩ [fm]⊢* ⟨(0 : ℕ), b + 4 * k, 0, d + k + 1, 0⟩ := by
  intro k; induction k with
  | zero => intro b d; exists 0
  | succ k ih =>
    intro b d
    rw [show (k + 1 : ℕ) = (k) + 1 from by ring]
    step fm; step fm; step fm
    apply stepStar_trans (ih _ (d + 1))
    ring_nf; finish

-- Main transition
theorem main_step : ∀ m β, ⟨0, β + m, 0, 2 * m + 1, 0⟩ [fm]⊢⁺ ⟨(0 : ℕ), β + 8 * m + 10, 0, 2 * m + 3, 0⟩ := by
  intro m β
  -- Phase 1: d → c
  apply stepStar_stepPlus_stepPlus
  · have h := d_to_c (2 * m + 1) (β + m) 0
    simp only [Nat.zero_add] at h; exact h
  -- Phase 2: c_consume
  apply stepStar_stepPlus_stepPlus
  · exact c_consume m β 0
  -- Phase 3: R2
  apply step_stepStar_stepPlus
  · show fm ⟨1, β, 0, 0, 0 + 2 * m + 2⟩ = some ⟨0, β + 2, 0, 1, 0 + 2 * m + 2⟩
    unfold fm; simp
  -- Phase 4: r3r2r2 loop
  show ⟨0, β + 2, 0, 0 + 1, 0 + 2 * m + 2⟩ [fm]⊢* ⟨0, β + 8 * m + 10, 0, 2 * m + 3, 0⟩
  rw [show (0 : ℕ) + 1 = 1 from by ring, show (0 : ℕ) + 2 * m + 2 = 2 * m + 2 from by ring]
  apply stepStar_trans (r3r2r2_loop (2 * m + 2) (β + 2) 0)
  ring_nf; finish

-- Bootstrap: c₀ reaches the first canonical state
theorem bootstrap : c₀ [fm]⊢* ⟨(0 : ℕ), 2, 0, 1, 0⟩ := by
  unfold c₀; execute fm 1

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts bootstrap
  apply progress_nonhalt_simple (A := ℕ × ℕ) (fm := fm)
    (C := fun p ↦ ⟨0, p.1 + p.2, 0, 2 * p.2 + 1, 0⟩)
    (i₀ := ⟨2, 0⟩)
  intro ⟨β, m⟩
  exact ⟨⟨β + 7 * m + 9, m + 1⟩, by rw [show β + 7 * m + 9 + (m + 1) = β + 8 * m + 10 from by ring]; exact main_step m β⟩

end Sz22_2003_unofficial_111
