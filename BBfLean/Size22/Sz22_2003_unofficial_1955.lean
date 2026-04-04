import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #1955: [9/70, 77/15, 22/3, 5/11, 21/2]

Vector representation:
```
-1  2 -1 -1  0
 0 -1 -1  1  1
 1 -1  0  0  1
 0  0  1  0 -1
-1  1  0  1  0
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_1955

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a+1, b, c+1, d+1, e⟩ => some ⟨a, b+2, c, d, e⟩
  | ⟨a, b+1, c+1, d, e⟩ => some ⟨a, b, c, d+1, e+1⟩
  | ⟨a, b+1, c, d, e⟩ => some ⟨a+1, b, c, d, e+1⟩
  | ⟨a, b, c, d, e+1⟩ => some ⟨a, b, c+1, d, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b+1, c, d+1, e⟩
  | _ => none

theorem e_to_c : ∀ k, ⟨a, 0, c, 0, e + k⟩ [fm]⊢* ⟨a, 0, c + k, 0, e⟩ := by
  intro k; induction' k with k ih generalizing a c e
  · exists 0
  · rw [Nat.add_succ e k]
    step fm
    apply stepStar_trans (ih (c := c + 1))
    ring_nf; finish

theorem r3_chain : ∀ k, ∀ a b d e, ⟨a, b + k, 0, d, e⟩ [fm]⊢* ⟨a + k, b, 0, d, e + k⟩ := by
  intro k; induction' k with k ih <;> intro a b d e
  · exists 0
  · rw [show b + (k + 1) = (b + k) + 1 from by ring]
    step fm
    apply stepStar_trans (ih (a + 1) b d (e + 1))
    ring_nf; finish

theorem r1_step : ⟨a + 1, b, c + 1, d + 1, e⟩ [fm]⊢ ⟨a, b + 2, c, d, e⟩ := by rfl

theorem r2_step : ∀ a b c e,
    ⟨a, b + 2, c + 1, 0, e⟩ [fm]⊢ ⟨a, b + 1, c, 1, e + 1⟩ := by
  intro a b c e; simp [fm]

theorem r1r2_chain : ∀ k, ∀ a b c e,
    ⟨a + k, b, c + 2 * k, 1, e⟩ [fm]⊢* ⟨a, b + k, c, 1, e + k⟩ := by
  intro k; induction' k with k ih <;> intro a b c e
  · exists 0
  · rw [show a + (k + 1) = (a + k) + 1 from by ring,
        show c + 2 * (k + 1) = (c + 2 * k) + 1 + 1 from by ring]
    apply stepStar_trans (step_stepStar r1_step)
    rw [show (c + 2 * k) + 1 = c + (2 * k + 1) from by ring]
    apply stepStar_trans (step_stepStar (r2_step (a + k) b (c + 2 * k) e))
    rw [show b + (k + 1) = (b + 1) + k from by ring,
        show e + (k + 1) = (e + 1) + k from by ring]
    exact ih a (b + 1) c (e + 1)

theorem r5_step : ∀ n, ⟨n + 1, 0, 2 * n, 0, 0⟩ [fm]⊢ ⟨n, 1, 2 * n, 1, 0⟩ := by
  intro n; simp [fm]

theorem tail_steps : ⟨n + 1, 0, 0, 1, 2 * n + 1⟩ [fm]⊢⁺ ⟨n + 2, 0, 0, 0, 2 * n + 2⟩ := by
  step fm
  step fm
  step fm
  step fm
  ring_nf; finish

theorem main_trans : ∀ n, ⟨n + 1, 0, 0, 0, 2 * n⟩ [fm]⊢⁺ ⟨n + 2, 0, 0, 0, 2 * (n + 1)⟩ := by
  intro n
  rw [show 2 * (n + 1) = 2 * n + 2 from by ring]
  -- Phase 1: e_to_c: (n+1, 0, 0, 0, 2n) →* (n+1, 0, 2n, 0, 0)
  have h1 : ⟨n + 1, 0, 0, 0, 2 * n⟩ [fm]⊢* ⟨n + 1, 0, 2 * n, 0, 0⟩ := by
    rw [show (2 * n : ℕ) = 0 + 2 * n from by ring]
    exact e_to_c (2 * n) (a := n + 1) (c := 0) (e := 0)
  -- Phase 2: R5: (n+1, 0, 2n, 0, 0) → (n, 1, 2n, 1, 0)
  have h2 : ⟨n + 1, 0, 2 * n, 0, 0⟩ [fm]⊢ ⟨n, 1, 2 * n, 1, 0⟩ := r5_step n
  -- Phase 3: r1r2_chain: (n, 1, 2n, 1, 0) →* (0, n+1, 0, 1, n)
  have h3 : ⟨n, 1, 2 * n, 1, 0⟩ [fm]⊢* ⟨0, n + 1, 0, 1, n⟩ := by
    have := r1r2_chain n 0 1 0 0
    simp only [Nat.zero_add] at this
    rw [show (1 : ℕ) + n = n + 1 from by ring] at this
    exact this
  -- Phase 4: r3_chain: (0, n+1, 0, 1, n) →* (n+1, 0, 0, 1, 2n+1)
  have h4 : ⟨0, n + 1, 0, 1, n⟩ [fm]⊢* ⟨n + 1, 0, 0, 1, 2 * n + 1⟩ := by
    have := r3_chain (n + 1) 0 0 1 n
    rw [show 0 + (n + 1) = n + 1 from by ring, show n + (n + 1) = 2 * n + 1 from by ring] at this
    exact this
  -- Phase 5-7: tail: (n+1, 0, 0, 1, 2n+1) →⁺ (n+2, 0, 0, 0, 2n+2)
  have h5 : ⟨n + 1, 0, 0, 1, 2 * n + 1⟩ [fm]⊢⁺ ⟨n + 2, 0, 0, 0, 2 * n + 2⟩ := tail_steps
  -- Compose
  exact stepStar_stepPlus_stepPlus
    (stepStar_trans h1 (stepStar_trans (step_stepStar h2) (stepStar_trans h3 h4))) h5

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨1, 0, 0, 0, 0⟩) (by execute fm 0)
  apply progress_nonhalt_simple (fm := fm) (A := ℕ)
    (fun n ↦ ⟨n + 1, 0, 0, 0, 2 * n⟩) 0
  intro n; exists n + 1; exact main_trans n
