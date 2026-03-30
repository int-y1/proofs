import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #846: [36/35, 5/22, 49/2, 11/3, 22/7]

Vector representation:
```
 2  2 -1 -1  0
-1  0  1  0 -1
-1  0  0  2  0
 0 -1  0  0  1
 1  0  0 -1  1
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_846

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a, b, c+1, d+1, e⟩ => some ⟨a+2, b+2, c, d, e⟩
  | ⟨a+1, b, c, d, e+1⟩ => some ⟨a, b, c+1, d, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b, c, d+2, e⟩
  | ⟨a, b+1, c, d, e⟩ => some ⟨a, b, c, d, e+1⟩
  | ⟨a, b, c, d+1, e⟩ => some ⟨a+1, b, c, d, e+1⟩
  | _ => none

-- R3 chain: drain a to d.
theorem r3_chain : ∀ k, ∀ a b d, ⟨a + k, b, 0, d, 0⟩ [fm]⊢* ⟨a, b, 0, d + 2 * k, 0⟩ := by
  intro k; induction' k with k ih <;> intro a b d
  · exists 0
  · rw [show a + (k + 1) = (a + k) + 1 from by ring]
    step fm
    apply stepStar_trans (ih a b (d + 2))
    ring_nf; finish

-- R4 chain: drain b to e.
theorem r4_chain : ∀ k, ∀ b d e, ⟨0, b + k, 0, d, e⟩ [fm]⊢* ⟨0, b, 0, d, e + k⟩ := by
  intro k; induction' k with k ih <;> intro b d e
  · exists 0
  · rw [show b + (k + 1) = (b + k) + 1 from by ring]
    step fm
    apply stepStar_trans (ih b d (e + 1))
    ring_nf; finish

-- Interleaved R1+R2 chain.
theorem r1r2_chain : ∀ k, ∀ a b d, ⟨a, b, 1, d + k, k⟩ [fm]⊢* ⟨a + k, b + 2 * k, 1, d, 0⟩ := by
  intro k; induction' k with k ih <;> intro a b d
  · exists 0
  · rw [show d + (k + 1) = (d + k) + 1 from by ring]
    step fm
    step fm
    apply stepStar_trans (ih (a + 1) (b + 2) d)
    ring_nf; finish

-- Whole cycle as ⊢*: (n+2, 2n+2, 0, 0, 0) →* (2n+4, 4n+6, 0, 0, 0)
theorem cycle_star : ⟨n + 2, 2 * n + 2, 0, 0, 0⟩ [fm]⊢* ⟨2 * n + 4, 4 * n + 6, 0, 0, 0⟩ := by
  -- R3 chain: (n+2, 2n+2, 0, 0, 0) →* (0, 2n+2, 0, 2n+4, 0)
  have h1 : ⟨n + 2, 2 * n + 2, 0, 0, 0⟩ [fm]⊢* ⟨0, 2 * n + 2, 0, 2 * n + 4, 0⟩ := by
    rw [show n + 2 = 0 + (n + 2) from by ring,
        show 2 * n + 4 = 0 + 2 * (n + 2) from by ring]
    exact r3_chain (n + 2) 0 (2 * n + 2) 0
  -- R4 chain: (0, 2n+2, 0, 2n+4, 0) →* (0, 0, 0, 2n+4, 2n+2)
  have h2 : ⟨0, 2 * n + 2, 0, 2 * n + 4, 0⟩ [fm]⊢* ⟨0, 0, 0, 2 * n + 4, 2 * n + 2⟩ := by
    have := r4_chain (2 * n + 2) 0 (2 * n + 4) 0
    simp only [Nat.zero_add] at this
    exact this
  -- R5+R2: (0, 0, 0, 2n+4, 2n+2) →* (0, 0, 1, 2n+3, 2n+2)
  have h3 : ⟨0, 0, 0, 2 * n + 4, 2 * n + 2⟩ [fm]⊢* ⟨0, 0, 1, 2 * n + 3, 2 * n + 2⟩ := by
    rw [show 2 * n + 4 = (2 * n + 3) + 1 from by ring]
    step fm  -- R5: (1, 0, 0, 2n+3, 2n+3)
    step fm  -- R2: (0, 0, 1, 2n+3, 2n+2)
    finish
  -- R1+R2 chain: (0, 0, 1, 2n+3, 2n+2) →* (2n+2, 4n+4, 1, 1, 0)
  have h4 : ⟨0, 0, 1, 2 * n + 3, 2 * n + 2⟩ [fm]⊢* ⟨2 * n + 2, 4 * n + 4, 1, 1, 0⟩ := by
    rw [show 2 * n + 3 = 1 + (2 * n + 2) from by ring]
    have := r1r2_chain (2 * n + 2) 0 0 1
    rw [show 0 + (2 * n + 2) = 2 * n + 2 from by ring,
        show 0 + 2 * (2 * n + 2) = 4 * n + 4 from by ring] at this
    exact this
  -- Final R1: (2n+2, 4n+4, 1, 1, 0) →* (2n+4, 4n+6, 0, 0, 0)
  have h5 : ⟨2 * n + 2, 4 * n + 4, 1, 1, 0⟩ [fm]⊢* ⟨2 * n + 4, 4 * n + 6, 0, 0, 0⟩ := by
    rw [show (1 : ℕ) = 0 + 1 from by ring,
        show 2 * n + 4 = 2 * n + 2 + 2 from by ring,
        show 4 * n + 6 = 4 * n + 4 + 2 from by ring]
    step fm
    finish
  exact stepStar_trans h1 (stepStar_trans h2 (stepStar_trans h3 (stepStar_trans h4 h5)))

-- Main transition as ⊢⁺
theorem main_trans : ⟨n + 2, 2 * n + 2, 0, 0, 0⟩ [fm]⊢⁺ ⟨2 * n + 4, 4 * n + 6, 0, 0, 0⟩ := by
  apply stepStar_stepPlus cycle_star
  intro h; simp [Q, Prod.mk.injEq] at h; omega

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨2, 2, 0, 0, 0⟩)
  · execute fm 4
  apply progress_nonhalt_simple (fm := fm) (A := ℕ)
    (fun n ↦ ⟨n + 2, 2 * n + 2, 0, 0, 0⟩) 0
  intro n
  refine ⟨2 * n + 2, ?_⟩
  rw [show 2 * n + 2 + 2 = 2 * n + 4 from by ring,
      show 2 * (2 * n + 2) + 2 = 4 * n + 6 from by ring]
  exact main_trans
