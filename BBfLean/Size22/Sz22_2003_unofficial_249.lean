import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #249: [135/2, 4/35, 11/45, 7/3, 5/11]

Vector representation:
```
-1  3  1  0  0
 2  0 -1 -1  0
 0 -2 -1  0  1
 0 -1  0  1  0
 0  0  1  0 -1
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_249

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b+3, c+1, d, e⟩
  | ⟨a, b, c+1, d+1, e⟩ => some ⟨a+2, b, c, d, e⟩
  | ⟨a, b+2, c+1, d, e⟩ => some ⟨a, b, c, d, e+1⟩
  | ⟨a, b+1, c, d, e⟩ => some ⟨a, b, c, d+1, e⟩
  | ⟨a, b, c, d, e+1⟩ => some ⟨a, b, c+1, d, e⟩
  | _ => none

-- R2,R1,R1 loop: (0, 6*k, k+1, D, E) →* (0, 6*(k+D), k+D+1, 0, E)
theorem r12_loop : ∀ D : ℕ, ∀ k E : ℕ,
    ⟨0, 6*k, k+1, D, E⟩ [fm]⊢* ⟨0, 6*(k+D), k+D+1, 0, E⟩ := by
  intro D; induction D with
  | zero => intro k E; simp; finish
  | succ D ih =>
    intro k E
    rw [show k + 1 = (k + 0) + 1 from by ring]
    -- R2: (0, 6*k, k+1, D+1, E) → (2, 6*k, k, D, E)
    step fm
    -- R1: (2, 6*k, k, D, E) → (1, 6*k+3, k+1, D, E)
    step fm
    -- R1: → (0, 6*k+6, k+2, D, E) = (0, 6*(k+1), (k+1)+1, D, E)
    step fm
    rw [show 6 * k + 6 = 6 * (k + 1) from by ring,
        show k + 2 = (k + 1) + 1 from by ring]
    apply stepStar_trans (ih (k + 1) E)
    rw [show k + 1 + D = k + (D + 1) from by ring]; finish

-- R3 loop: (0, 2*c + b, c, 0, E) →* (0, b, 0, 0, c + E)
theorem r3_loop : ∀ c : ℕ, ∀ b E : ℕ,
    ⟨0, 2*c + b, c, 0, E⟩ [fm]⊢* ⟨0, b, 0, 0, c + E⟩ := by
  intro c; induction c with
  | zero => intro b E; simp; finish
  | succ c ih =>
    intro b E
    rw [show 2 * (c + 1) + b = (2 * c + b) + 2 from by ring,
        show c + 1 = c + 0 + 1 from by ring]
    -- R3: (0, 2*c+b+2, c+1, 0, E) → (0, 2*c+b, c, 0, E+1)
    step fm
    apply stepStar_trans (ih b (E + 1))
    rw [show c + (E + 1) = (c + 1) + E from by ring]; finish

-- R4 loop: (0, b, 0, d, E) →* (0, 0, 0, d + b, E)
theorem b_to_d : ∀ b : ℕ, ∀ d E : ℕ,
    ⟨0, b, 0, d, E⟩ [fm]⊢* ⟨0, 0, 0, d + b, E⟩ := by
  intro b; induction b with
  | zero => intro d E; simp; finish
  | succ b ih =>
    intro d E
    step fm
    apply stepStar_trans (ih (d + 1) E)
    rw [show d + 1 + b = d + (b + 1) from by ring]; finish

-- Main transition: (0, 0, 0, D+1, E+1) →⁺ (0, 0, 0, 4*D+2, D+E+2)
theorem main_step (D E : ℕ) :
    ⟨0, 0, 0, D+1, E+1⟩ [fm]⊢⁺ ⟨0, 0, 0, 4*D+2, D+E+2⟩ := by
  -- R5: (0, 0, 0, D+1, E+1) → (0, 0, 1, D+1, E)
  -- R2: (0, 0, 1, D+1, E) → (2, 0, 0, D, E)
  -- R1: (2, 0, 0, D, E) → (1, 3, 1, D, E)
  -- R1: (1, 3, 1, D, E) → (0, 6, 2, D, E) = (0, 6*1, 1+1, D, E)
  apply step_stepStar_stepPlus
  · show fm ⟨0, 0, 0, D + 1, E + 1⟩ = some ⟨0, 0, 1, D + 1, E⟩; simp [fm]
  step fm; step fm; step fm
  rw [show (6 : ℕ) = 6 * 1 from by ring, show (2 : ℕ) = 1 + 1 from by ring]
  -- r12_loop: (0, 6*1, 1+1, D, E) →* (0, 6*(1+D), 1+D+1, 0, E)
  apply stepStar_trans (r12_loop D 1 E)
  -- Now at (0, 6*(1+D), D+2, 0, E) = (0, 6*D+6, D+2, 0, E)
  -- r3_loop with c = D+2, b = 4*D+2: 2*(D+2) + (4*D+2) = 6*D+6
  rw [show 6 * (1 + D) = 2 * (D + 2) + (4 * D + 2) from by ring,
      show 1 + D + 1 = D + 2 from by ring]
  apply stepStar_trans (r3_loop (D + 2) (4 * D + 2) E)
  -- Now at (0, 4*D+2, 0, 0, D+2+E)
  rw [show (D + 2) + E = D + E + 2 from by ring]
  -- b_to_d: (0, 4*D+2, 0, 0, D+E+2) →* (0, 0, 0, 4*D+2, D+E+2)
  apply stepStar_trans (b_to_d (4 * D + 2) 0 (D + E + 2))
  simp; finish

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨0, 0, 0, 1, 1⟩)
  · execute fm 3
  apply progress_nonhalt_simple (fm := fm) (A := ℕ × ℕ)
    (fun ⟨D, E⟩ ↦ ⟨0, 0, 0, D + 1, E + 1⟩) ⟨0, 0⟩
  intro ⟨D, E⟩
  refine ⟨⟨4 * D + 1, D + E + 1⟩, ?_⟩
  show ⟨0, 0, 0, D + 1, E + 1⟩ [fm]⊢⁺ ⟨0, 0, 0, (4 * D + 1) + 1, (D + E + 1) + 1⟩
  rw [show (4 * D + 1) + 1 = 4 * D + 2 from by ring,
      show (D + E + 1) + 1 = D + E + 2 from by ring]
  exact main_step D E

end Sz22_2003_unofficial_249
