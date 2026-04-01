import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #1199: [5/6, 539/2, 4/105, 3/7, 14/11]

Vector representation:
```
-1 -1  1  0  0
-1  0  0  2  1
 2 -1 -1 -1  0
 0  1  0 -1  0
 1  0  0  1 -1
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_1199

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a+1, b+1, c, d, e⟩ => some ⟨a, b, c+1, d, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b, c, d+2, e+1⟩
  | ⟨a, b+1, c+1, d+1, e⟩ => some ⟨a+2, b, c, d, e⟩
  | ⟨a, b, c, d+1, e⟩ => some ⟨a, b+1, c, d, e⟩
  | ⟨a, b, c, d, e+1⟩ => some ⟨a+1, b, c, d+1, e⟩
  | _ => none

-- R4 repeated: move d to b
theorem d_to_b : ∀ k b d, ⟨(0 : ℕ), b, (0 : ℕ), d + k, e⟩ [fm]⊢* ⟨(0 : ℕ), b + k, (0 : ℕ), d, e⟩ := by
  intro k; induction' k with k ih <;> intro b d
  · exists 0
  · rw [Nat.add_succ d k]
    step fm
    apply stepStar_trans (ih (b + 1) d)
    ring_nf; finish

-- Drain b round: consume 4 from b, 1 from e, add 2 to c
theorem drain_b_round : ⟨(0 : ℕ), b + 4, c, (0 : ℕ), e + 1⟩ [fm]⊢* ⟨(0 : ℕ), b, c + 2, (0 : ℕ), e⟩ := by
  step fm; step fm; step fm; step fm; step fm; finish

-- Drain b loop: k rounds
theorem drain_b_loop : ∀ k b c e, ⟨(0 : ℕ), b + 4 * k, c, (0 : ℕ), e + k⟩ [fm]⊢* ⟨(0 : ℕ), b, c + 2 * k, (0 : ℕ), e⟩ := by
  intro k; induction' k with k ih <;> intro b c e
  · exists 0
  · rw [show b + 4 * (k + 1) = (b + 4) + 4 * k from by ring,
        show e + (k + 1) = (e + 1) + k from by ring]
    apply stepStar_trans (ih (b + 4) c (e + 1))
    apply stepStar_trans drain_b_round
    ring_nf; finish

-- Drain b=3: (0, 3, c, 0, e+1) → (0, 0, c+1, 2, e+1)
theorem drain_b3 : ⟨(0 : ℕ), 3, c, (0 : ℕ), e + 1⟩ [fm]⊢* ⟨(0 : ℕ), (0 : ℕ), c + 1, 2, e + 1⟩ := by
  step fm; step fm; step fm; step fm; step fm; finish

-- Kick: (0, 0, c, 0, e+1) →⁺ (0, 0, c, 3, e+1)
theorem kick : ⟨(0 : ℕ), (0 : ℕ), c, (0 : ℕ), e + 1⟩ [fm]⊢⁺ ⟨(0 : ℕ), (0 : ℕ), c, 3, e + 1⟩ := by
  step fm; step fm; finish

-- Spiral step: (0, 0, c+1, d+2, e) → (0, 0, c, d+4, e+2)
theorem spiral_step : ⟨(0 : ℕ), (0 : ℕ), c + 1, d + 2, e⟩ [fm]⊢* ⟨(0 : ℕ), (0 : ℕ), c, d + 4, e + 2⟩ := by
  step fm; step fm; step fm; step fm; finish

-- Spiral loop: k rounds
theorem spiral_loop : ∀ k c d e, ⟨(0 : ℕ), (0 : ℕ), c + k, d + 2, e⟩ [fm]⊢* ⟨(0 : ℕ), (0 : ℕ), c, d + 2 + 2 * k, e + 2 * k⟩ := by
  intro k; induction' k with k ih <;> intro c d e
  · exists 0
  · rw [show c + (k + 1) = (c + 1) + k from by ring]
    apply stepStar_trans (ih (c + 1) d e)
    rw [show d + 2 + 2 * k = (d + 2 * k) + 2 from by ring]
    apply stepStar_trans spiral_step
    ring_nf; finish

-- Phase 1: (0,0,0, 4n+4, (3n+2)(n+1)) →⁺ (0,0,0, 4n+7, (3n+5)(n+1))
theorem phase1 (n : ℕ) : ⟨(0 : ℕ), (0 : ℕ), (0 : ℕ), 4 * n + 4, (3 * n + 2) * (n + 1)⟩ [fm]⊢⁺ ⟨(0 : ℕ), (0 : ℕ), (0 : ℕ), 4 * n + 7, (3 * n + 5) * (n + 1)⟩ := by
  -- d_to_b: rewrite to match d_to_b signature
  have h1 : ⟨(0 : ℕ), (0 : ℕ), (0 : ℕ), 4 * n + 4, (3 * n + 2) * (n + 1)⟩ [fm]⊢*
      ⟨(0 : ℕ), 4 * n + 4, (0 : ℕ), (0 : ℕ), (3 * n + 2) * (n + 1)⟩ := by
    rw [show (4 * n + 4 : ℕ) = 0 + (4 * n + 4) from by ring]
    exact d_to_b (4 * n + 4) 0 0
  -- drain_b_loop
  have h2 : ⟨(0 : ℕ), 4 * n + 4, (0 : ℕ), (0 : ℕ), (3 * n + 2) * (n + 1)⟩ [fm]⊢*
      ⟨(0 : ℕ), (0 : ℕ), 2 * n + 2, (0 : ℕ), (3 * n + 1) * (n + 1)⟩ := by
    rw [show (4 * n + 4 : ℕ) = 0 + 4 * (n + 1) from by ring,
        show (3 * n + 2) * (n + 1) = (3 * n + 1) * (n + 1) + (n + 1) from by ring,
        show (2 * n + 2 : ℕ) = 0 + 2 * (n + 1) from by ring]
    exact drain_b_loop (n + 1) 0 0 ((3 * n + 1) * (n + 1))
  -- kick
  have h3 : ⟨(0 : ℕ), (0 : ℕ), 2 * n + 2, (0 : ℕ), (3 * n + 1) * (n + 1)⟩ [fm]⊢⁺
      ⟨(0 : ℕ), (0 : ℕ), 2 * n + 2, 3, (3 * n + 1) * (n + 1)⟩ := by
    rw [show (3 * n + 1) * (n + 1) = 3 * n * n + 4 * n + 0 + 1 from by ring]
    exact kick
  -- spiral_loop
  have h4 : ⟨(0 : ℕ), (0 : ℕ), 2 * n + 2, 3, (3 * n + 1) * (n + 1)⟩ [fm]⊢*
      ⟨(0 : ℕ), (0 : ℕ), (0 : ℕ), 4 * n + 7, (3 * n + 5) * (n + 1)⟩ := by
    rw [show (2 * n + 2 : ℕ) = 0 + (2 * n + 2) from by ring,
        show (3 : ℕ) = 1 + 2 from by ring,
        show (4 * n + 7 : ℕ) = 1 + 2 + 2 * (2 * n + 2) from by ring,
        show (3 * n + 5) * (n + 1) = (3 * n + 1) * (n + 1) + 2 * (2 * n + 2) from by ring]
    exact spiral_loop (2 * n + 2) 0 1 ((3 * n + 1) * (n + 1))
  exact stepStar_stepPlus_stepPlus (stepStar_trans h1 h2) (stepPlus_stepStar_stepPlus h3 h4)

-- Phase 2: (0,0,0, 4n+7, (3n+5)(n+1)) →⁺ (0,0,0, 4n+8, (3n+5)(n+2))
theorem phase2 (n : ℕ) : ⟨(0 : ℕ), (0 : ℕ), (0 : ℕ), 4 * n + 7, (3 * n + 5) * (n + 1)⟩ [fm]⊢⁺ ⟨(0 : ℕ), (0 : ℕ), (0 : ℕ), 4 * n + 8, (3 * n + 5) * (n + 2)⟩ := by
  -- d_to_b
  have h1 : ⟨(0 : ℕ), (0 : ℕ), (0 : ℕ), 4 * n + 7, (3 * n + 5) * (n + 1)⟩ [fm]⊢*
      ⟨(0 : ℕ), 4 * n + 7, (0 : ℕ), (0 : ℕ), (3 * n + 5) * (n + 1)⟩ := by
    rw [show (4 * n + 7 : ℕ) = 0 + (4 * n + 7) from by ring]
    exact d_to_b (4 * n + 7) 0 0
  -- drain_b_loop with k=n+1
  have h2 : ⟨(0 : ℕ), 4 * n + 7, (0 : ℕ), (0 : ℕ), (3 * n + 5) * (n + 1)⟩ [fm]⊢*
      ⟨(0 : ℕ), 3, 2 * n + 2, (0 : ℕ), (3 * n + 4) * (n + 1)⟩ := by
    rw [show (4 * n + 7 : ℕ) = 3 + 4 * (n + 1) from by ring,
        show (3 * n + 5) * (n + 1) = (3 * n + 4) * (n + 1) + (n + 1) from by ring,
        show (2 * n + 2 : ℕ) = 0 + 2 * (n + 1) from by ring]
    exact drain_b_loop (n + 1) 3 0 ((3 * n + 4) * (n + 1))
  -- drain_b3
  have h3 : ⟨(0 : ℕ), 3, 2 * n + 2, (0 : ℕ), (3 * n + 4) * (n + 1)⟩ [fm]⊢*
      ⟨(0 : ℕ), (0 : ℕ), 2 * n + 3, 2, (3 * n + 4) * (n + 1)⟩ := by
    rw [show (2 * n + 3 : ℕ) = (2 * n + 2) + 1 from by ring,
        show (3 * n + 4) * (n + 1) = 3 * n * n + 7 * n + 3 + 1 from by ring]
    exact drain_b3
  -- spiral first step: ⊢⁺
  have h4a : ⟨(0 : ℕ), (0 : ℕ), 2 * n + 3, 2, (3 * n + 4) * (n + 1)⟩ [fm]⊢⁺
      ⟨(0 : ℕ), (0 : ℕ), 2 * n + 2, 4, (3 * n + 4) * (n + 1) + 2⟩ := by
    rw [show (2 * n + 3 : ℕ) = (2 * n + 2) + 1 from by ring,
        show (2 : ℕ) = 0 + 2 from by ring]
    step fm; step fm; step fm; step fm; finish
  -- spiral rest: ⊢*
  have h4b : ⟨(0 : ℕ), (0 : ℕ), 2 * n + 2, 4, (3 * n + 4) * (n + 1) + 2⟩ [fm]⊢*
      ⟨(0 : ℕ), (0 : ℕ), (0 : ℕ), 4 * n + 8, (3 * n + 5) * (n + 2)⟩ := by
    rw [show (2 * n + 2 : ℕ) = 0 + (2 * n + 2) from by ring,
        show (4 : ℕ) = 2 + 2 from by ring,
        show (4 * n + 8 : ℕ) = 2 + 2 + 2 * (2 * n + 2) from by ring,
        show (3 * n + 5) * (n + 2) = ((3 * n + 4) * (n + 1) + 2) + 2 * (2 * n + 2) from by ring]
    exact spiral_loop (2 * n + 2) 0 2 ((3 * n + 4) * (n + 1) + 2)
  exact stepStar_stepPlus_stepPlus (stepStar_trans h1 (stepStar_trans h2 h3)) (stepPlus_stepStar_stepPlus h4a h4b)

-- Main transition
theorem main_trans (n : ℕ) : ⟨(0 : ℕ), (0 : ℕ), (0 : ℕ), 4 * n + 4, (3 * n + 2) * (n + 1)⟩ [fm]⊢⁺ ⟨(0 : ℕ), (0 : ℕ), (0 : ℕ), 4 * n + 8, (3 * n + 5) * (n + 2)⟩ :=
  stepPlus_trans (phase1 n) (phase2 n)

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨0, 0, 0, 4, 2⟩)
  · execute fm 8
  apply progress_nonhalt_simple (fm := fm) (A := ℕ)
    (fun n ↦ ⟨0, 0, 0, 4 * (n + 1), (3 * n + 2) * (n + 1)⟩) 0
  intro n
  refine ⟨n + 1, ?_⟩
  show ⟨(0 : ℕ), (0 : ℕ), (0 : ℕ), 4 * n + 4, (3 * n + 2) * (n + 1)⟩ [fm]⊢⁺
      ⟨(0 : ℕ), (0 : ℕ), (0 : ℕ), 4 * n + 8, (3 * n + 5) * (n + 2)⟩
  exact main_trans n

end Sz22_2003_unofficial_1199
