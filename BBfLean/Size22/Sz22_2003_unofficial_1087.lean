import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #1087: [5/6, 2/35, 539/2, 9/77, 10/3]

Vector representation:
```
-1 -1  1  0  0
 1  0 -1 -1  0
-1  0  0  2  1
 0  2  0 -1 -1
 1 -1  1  0  0
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_1087

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a+1, b+1, c, d, e⟩ => some ⟨a, b, c+1, d, e⟩
  | ⟨a, b, c+1, d+1, e⟩ => some ⟨a+1, b, c, d, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b, c, d+2, e+1⟩
  | ⟨a, b, c, d+1, e+1⟩ => some ⟨a, b+2, c, d, e⟩
  | ⟨a, b+1, c, d, e⟩ => some ⟨a+1, b, c+1, d, e⟩
  | _ => none

-- R1/R5 chain: drain b, build c
theorem r1r5_chain : ∀ k, ∀ c,
    ⟨(1 : ℕ), 2 * k, c, (0 : ℕ), (0 : ℕ)⟩ [fm]⊢* ⟨1, 0, c + 2 * k, 0, 0⟩ := by
  intro k; induction k with
  | zero => intro c; simp; exists 0
  | succ k ih =>
    intro c
    rw [show 2 * (k + 1) = (2 * k + 1) + 1 from by ring]
    step fm; step fm
    apply stepStar_trans (ih (c + 2))
    ring_nf; finish

-- R2/R3/R2 chain
theorem r2r3r2_chain : ∀ n, ∀ j c,
    ⟨j + 1, (0 : ℕ), c + 2 * n, (1 : ℕ), j + 1⟩ [fm]⊢*
    ⟨j + n + 1, 0, c, 1, j + n + 1⟩ := by
  intro n; induction n with
  | zero => intro j c; simp; exists 0
  | succ n ih =>
    intro j c
    rw [show c + 2 * (n + 1) = (c + 2 * n) + 2 from by ring]
    step fm; step fm; step fm
    apply stepStar_trans (ih (j + 1) c)
    ring_nf; finish

-- R3 drain
theorem r3_drain : ∀ k, ∀ d e,
    ⟨k, (0 : ℕ), (0 : ℕ), d, e⟩ [fm]⊢* ⟨0, 0, 0, d + 2 * k, e + k⟩ := by
  intro k; induction k with
  | zero => intro d e; simp; exists 0
  | succ k ih =>
    intro d e
    rw [show (k : ℕ) + 1 = k + 1 from rfl]
    step fm
    apply stepStar_trans (ih (d + 2) (e + 1))
    ring_nf; finish

-- R4 drain
theorem r4_drain : ∀ k, ∀ b,
    ⟨(0 : ℕ), b, (0 : ℕ), k + 1, k⟩ [fm]⊢* ⟨0, b + 2 * k, 0, 1, 0⟩ := by
  intro k; induction k with
  | zero => intro b; simp; exists 0
  | succ k ih =>
    intro b
    rw [show (k : ℕ) + 1 + 1 = (k + 1) + 1 from by ring,
        show (k : ℕ) + 1 = k + 1 from rfl]
    step fm
    apply stepStar_trans (ih (b + 2))
    ring_nf; finish

-- Main transition
theorem main_trans (b : ℕ) :
    ⟨0, 2 * b + 2, 0, 1, 0⟩ [fm]⊢⁺
    ⟨0, 4 * b + 4, 0, 1, 0⟩ := by
  -- Phase 1: Opening R5, R1, R2
  rw [show 2 * b + 2 = (2 * b) + 1 + 1 from by ring]
  apply step_stepStar_stepPlus
  · show fm ⟨0, (2 * b) + 1 + 1, 0, 1, 0⟩ = some ⟨1, (2 * b) + 1, 1, 1, 0⟩
    unfold fm; simp
  step fm; step fm
  -- Phase 2: R1/R5 drain
  have h1 : ⟨(1 : ℕ), 2 * b, 1, (0 : ℕ), (0 : ℕ)⟩ [fm]⊢*
      ⟨1, 0, 1 + 2 * b, 0, 0⟩ := r1r5_chain b 1
  apply stepStar_trans h1
  rw [show 1 + 2 * b = 2 * b + 1 from by ring]
  -- Phase 3a: R3 + R2
  step fm; step fm
  -- Phase 3b: R2/R3/R2 chain
  have h2 : ⟨0 + 1, (0 : ℕ), 0 + 2 * b, (1 : ℕ), 0 + 1⟩ [fm]⊢*
      ⟨0 + b + 1, 0, 0, 1, 0 + b + 1⟩ := r2r3r2_chain b 0 0
  simp only [Nat.zero_add] at h2
  apply stepStar_trans h2
  -- Phase 3c: R3 drain
  have h3 : ⟨b + 1, (0 : ℕ), (0 : ℕ), 1, b + 1⟩ [fm]⊢*
      ⟨0, 0, 0, 1 + 2 * (b + 1), b + 1 + (b + 1)⟩ := r3_drain (b + 1) 1 (b + 1)
  rw [show 1 + 2 * (b + 1) = 2 * b + 3 from by ring,
      show b + 1 + (b + 1) = 2 * b + 2 from by ring] at h3
  apply stepStar_trans h3
  -- Phase 4: R4 drain
  rw [show (2 * b + 3 : ℕ) = (2 * b + 2) + 1 from by ring]
  have h4 : ⟨(0 : ℕ), 0, (0 : ℕ), (2 * b + 2) + 1, 2 * b + 2⟩ [fm]⊢*
      ⟨0, 0 + 2 * (2 * b + 2), 0, 1, 0⟩ := r4_drain (2 * b + 2) 0
  rw [show 0 + 2 * (2 * b + 2) = 4 * b + 4 from by ring] at h4
  exact h4

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨0, 2, 0, 1, 0⟩)
  · execute fm 2
  apply progress_nonhalt_simple (fm := fm) (A := ℕ)
    (fun b ↦ ⟨0, 2 * b + 2, 0, 1, 0⟩) 0
  intro b
  refine ⟨2 * b + 1, ?_⟩
  show ⟨0, 2 * b + 2, 0, 1, 0⟩ [fm]⊢⁺
    ⟨0, 2 * (2 * b + 1) + 2, 0, 1, 0⟩
  rw [show 2 * (2 * b + 1) + 2 = 4 * b + 4 from by ring]
  exact main_trans b

end Sz22_2003_unofficial_1087
