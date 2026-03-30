import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #686: [35/6, 4/55, 11/2, 3/7, 196/11]

Vector representation:
```
-1 -1  1  1  0
 2  0 -1  0 -1
-1  0  0  0  1
 0  1  0 -1  0
 2  0  0  2 -1
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_686

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a+1, b+1, c, d, e⟩ => some ⟨a, b, c+1, d+1, e⟩
  | ⟨a, b, c+1, d, e+1⟩ => some ⟨a+2, b, c, d, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b, c, d, e+1⟩
  | ⟨a, b, c, d+1, e⟩ => some ⟨a, b+1, c, d, e⟩
  | ⟨a, b, c, d, e+1⟩ => some ⟨a+2, b, c, d+2, e⟩
  | _ => none

-- R3 repeated: move a to e.
theorem a_to_e : ∀ k d e, ⟨k, 0, 0, d, e⟩ [fm]⊢* ⟨0, 0, 0, d, e + k⟩ := by
  intro k; induction' k with k ih <;> intro d e
  · simp; exists 0
  · step fm
    apply stepStar_trans (ih d (e + 1))
    ring_nf; finish

-- R4 repeated: move d to b.
theorem d_to_b : ∀ k b e, ⟨0, b, 0, k, e⟩ [fm]⊢* ⟨0, b + k, 0, 0, e⟩ := by
  intro k; induction' k with k ih <;> intro b e
  · exists 0
  · step fm
    apply stepStar_trans (ih (b + 1) e)
    ring_nf; finish

-- R1R1R2 chain: 3-step rounds.
theorem r1r1r2_chain : ∀ k b c d, ⟨2, b + 2 * k, c, d, k⟩ [fm]⊢* ⟨2, b, c + k, d + 2 * k, 0⟩ := by
  intro k; induction' k with k ih <;> intro b c d
  · exists 0
  · rw [show b + 2 * (k + 1) = (b + 2 * k + 1) + 1 from by ring]
    step fm
    step fm
    rw [show c + 1 + 1 = (c + 1) + 1 from by ring,
        show d + 1 + 1 = (d + 1) + 1 from by ring]
    step fm
    apply stepStar_trans (ih b (c + 1) (d + 2))
    ring_nf; finish

-- R3R2 drain: alternating R3 and R2.
theorem r3r2_drain : ∀ k a d, ⟨a + 1, 0, k, d, 0⟩ [fm]⊢* ⟨a + k + 1, 0, 0, d, 0⟩ := by
  intro k; induction' k with k ih <;> intro a d
  · exists 0
  · step fm
    step fm
    rw [show a + 2 = (a + 1) + 1 from by ring]
    apply stepStar_trans (ih (a + 1) d)
    ring_nf; finish

-- Combined phases 1-5 as a single transition.
theorem main_trans (n : ℕ) : (⟨n + 2, 0, 0, 2 * n + 2, 0⟩ : Q) [fm]⊢⁺ ⟨n + 3, 0, 0, 2 * n + 4, 0⟩ := by
  -- Phase 1: a_to_e: (n+2, 0, 0, 2n+2, 0) →* (0, 0, 0, 2n+2, n+2)
  have h1 : (⟨n + 2, 0, 0, 2 * n + 2, 0⟩ : Q) [fm]⊢* ⟨0, 0, 0, 2 * n + 2, n + 2⟩ := by
    have := a_to_e (n + 2) (2 * n + 2) 0
    simp only [Nat.zero_add] at this
    exact this
  -- Phase 2: d_to_b: (0, 0, 0, 2n+2, n+2) →* (0, 2n+2, 0, 0, n+2)
  have h2 : (⟨0, 0, 0, 2 * n + 2, n + 2⟩ : Q) [fm]⊢* ⟨0, 2 * n + 2, 0, 0, n + 2⟩ := by
    have := d_to_b (2 * n + 2) 0 (n + 2)
    simp only [Nat.zero_add] at this
    exact this
  -- Phase 3: R5 step: (0, 2n+2, 0, 0, n+2) → (2, 2n+2, 0, 2, n+1)
  have h3 : (⟨0, 2 * n + 2, 0, 0, n + 2⟩ : Q) [fm]⊢ ⟨2, 2 * n + 2, 0, 2, n + 1⟩ := by
    show (⟨0, 2 * n + 2, 0, 0, (n + 1) + 1⟩ : Q) [fm]⊢ ⟨0 + 2, 2 * n + 2, 0, 0 + 2, n + 1⟩
    simp [fm]
  -- Phase 4: R1R1R2 chain: (2, 2n+2, 0, 2, n+1) →* (2, 0, n+1, 2n+4, 0)
  have h4 : (⟨2, 2 * n + 2, 0, 2, n + 1⟩ : Q) [fm]⊢* ⟨2, 0, n + 1, 2 * n + 4, 0⟩ := by
    have := r1r1r2_chain (n + 1) 0 0 2
    simp only [Nat.zero_add] at this
    convert this using 2; ring_nf
  -- Phase 5: R3R2 drain: (2, 0, n+1, 2n+4, 0) →* (n+3, 0, 0, 2n+4, 0)
  have h5 : (⟨2, 0, n + 1, 2 * n + 4, 0⟩ : Q) [fm]⊢* ⟨n + 3, 0, 0, 2 * n + 4, 0⟩ := by
    have := r3r2_drain (n + 1) 1 (2 * n + 4)
    convert this using 2; ring_nf
  -- Compose all phases
  exact stepStar_stepPlus_stepPlus (stepStar_trans h1 h2)
    (step_stepStar_stepPlus h3 (stepStar_trans h4 h5))

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨2, 0, 0, 2, 0⟩) (by execute fm 2)
  apply progress_nonhalt_simple (fm := fm) (A := ℕ)
    (fun n ↦ ⟨n + 2, 0, 0, 2 * n + 2, 0⟩) 0
  intro n; exists n + 1; exact main_trans n
