import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #921: [4/15, 33/14, 1375/2, 7/11, 2/5]

Vector representation:
```
 2 -1 -1  0  0
-1  1  0 -1  1
-1  0  3  0  1
 0  0  0  1 -1
 1  0 -1  0  0
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_921

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a, b+1, c+1, d, e⟩ => some ⟨a+2, b, c, d, e⟩
  | ⟨a+1, b, c, d+1, e⟩ => some ⟨a, b+1, c, d, e+1⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b, c+3, d, e+1⟩
  | ⟨a, b, c, d, e+1⟩ => some ⟨a, b, c, d+1, e⟩
  | ⟨a, b, c+1, d, e⟩ => some ⟨a+1, b, c, d, e⟩
  | _ => none

-- R2/R1 interleaved chain: each round does R2 then R1
theorem r2r1_chain : ∀ k, ∀ a c e,
    ⟨a + 1, (0 : ℕ), c + k, k, e⟩ [fm]⊢* ⟨a + k + 1, 0, c, 0, e + k⟩ := by
  intro k; induction k with
  | zero => intro a c e; simp; exists 0
  | succ k ih =>
    intro a c e
    rw [show c + (k + 1) = (c + k) + 1 from by ring,
        show (k : ℕ) + 1 = k + 1 from rfl]
    step fm; step fm
    apply stepStar_trans (ih (a + 1) c (e + 1))
    ring_nf; finish

-- R3 drain: convert a to c and e (when b = 0, d = 0)
theorem r3_drain : ∀ k, ∀ c e,
    ⟨k, (0 : ℕ), c, (0 : ℕ), e⟩ [fm]⊢* ⟨0, 0, c + 3 * k, 0, e + k⟩ := by
  intro k; induction k with
  | zero => intro c e; simp; exists 0
  | succ k ih =>
    intro c e
    rw [show (k : ℕ) + 1 = k + 1 from rfl]
    step fm
    apply stepStar_trans (ih (c + 3) (e + 1))
    ring_nf; finish

-- R4 chain: transfer e to d
theorem r4_chain : ∀ k, ∀ c d,
    ⟨(0 : ℕ), (0 : ℕ), c, d, k⟩ [fm]⊢* ⟨0, 0, c, d + k, 0⟩ := by
  intro k; induction k with
  | zero => intro c d; simp; exists 0
  | succ k ih =>
    intro c d
    rw [show (k : ℕ) + 1 = k + 1 from rfl]
    step fm
    apply stepStar_trans (ih c (d + 1))
    ring_nf; finish

-- Main transition: (0, 0, 2d+1, d, 0) ⊢⁺ (0, 0, 4d+3, 2d+1, 0)
theorem main_trans (d : ℕ) :
    ⟨0, 0, 2 * d + 1, d, 0⟩ [fm]⊢⁺
    ⟨0, 0, 4 * d + 3, 2 * d + 1, 0⟩ := by
  -- Phase 1: R5 step (gives ⊢⁺)
  rw [show 2 * d + 1 = (2 * d) + 1 from by ring]
  apply step_stepStar_stepPlus
  · show fm ⟨0, 0, (2 * d) + 1, d, 0⟩ = some ⟨1, 0, 2 * d, d, 0⟩
    unfold fm; simp
  -- Phase 2: R2/R1 interleaved chain
  have h2 : ⟨1, (0 : ℕ), 2 * d, d, (0 : ℕ)⟩ [fm]⊢*
      ⟨d + 1, 0, d, 0, d⟩ := by
    have := r2r1_chain d 0 d 0
    rw [show 0 + 1 = 1 from by ring,
        show d + d = 2 * d from by ring,
        show 0 + d + 1 = d + 1 from by ring,
        show 0 + d = d from by ring] at this
    exact this
  -- Phase 3: R3 drain
  have h3 : ⟨d + 1, (0 : ℕ), d, (0 : ℕ), d⟩ [fm]⊢*
      ⟨0, 0, 4 * d + 3, 0, 2 * d + 1⟩ := by
    have := r3_drain (d + 1) d d
    rw [show d + 3 * (d + 1) = 4 * d + 3 from by ring,
        show d + (d + 1) = 2 * d + 1 from by ring] at this
    exact this
  -- Phase 4: R4 chain
  have h4 : ⟨(0 : ℕ), (0 : ℕ), 4 * d + 3, (0 : ℕ), 2 * d + 1⟩ [fm]⊢*
      ⟨0, 0, 4 * d + 3, 2 * d + 1, 0⟩ := by
    have := r4_chain (2 * d + 1) (4 * d + 3) 0
    rw [show 0 + (2 * d + 1) = 2 * d + 1 from by ring] at this
    exact this
  exact stepStar_trans h2 (stepStar_trans h3 h4)

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨0, 0, 3, 1, 0⟩)
  · execute fm 2
  apply progress_nonhalt_simple (fm := fm) (A := ℕ)
    (fun d ↦ ⟨0, 0, 2 * d + 1, d, 0⟩) 1
  intro d
  refine ⟨2 * d + 1, ?_⟩
  show ⟨0, 0, 2 * d + 1, d, 0⟩ [fm]⊢⁺
    ⟨0, 0, 2 * (2 * d + 1) + 1, 2 * d + 1, 0⟩
  rw [show 2 * (2 * d + 1) + 1 = 4 * d + 3 from by ring]
  exact main_trans d

end Sz22_2003_unofficial_921
