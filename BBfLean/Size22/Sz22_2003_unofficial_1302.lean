import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #1302: [63/10, 121/2, 28/33, 5/7, 3/11]

Vector representation:
```
-1  2 -1  1  0
-1  0  0  0  2
 2 -1  0  1 -1
 0  0  1 -1  0
 0  1  0  0 -1
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_1302

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a+1, b, c+1, d, e⟩ => some ⟨a, b+2, c, d+1, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b, c, d, e+2⟩
  | ⟨a, b+1, c, d, e+1⟩ => some ⟨a+2, b, c, d+1, e⟩
  | ⟨a, b, c, d+1, e⟩ => some ⟨a, b, c+1, d, e⟩
  | ⟨a, b, c, d, e+1⟩ => some ⟨a, b+1, c, d, e⟩
  | _ => none

-- R4 repeated: transfer d to c.
theorem d_to_c : ∀ k c d, ⟨0, 0, c, d + k, e⟩ [fm]⊢* ⟨0, 0, c + k, d, e⟩ := by
  intro k; induction' k with k ih <;> intro c d
  · exists 0
  · rw [show d + (k + 1) = (d + k) + 1 from by omega]
    step fm
    apply stepStar_trans (ih (c + 1) d)
    ring_nf; finish

-- R3/R1/R1 chain.
theorem r3r1r1_chain : ∀ k c b d' e, ⟨0, b + 1, c + 2 * k, d', e + k⟩ [fm]⊢* ⟨0, b + 3 * k + 1, c, d' + 3 * k, e⟩ := by
  intro k; induction' k with k ih <;> intro c b d' e
  · exists 0
  · rw [show c + 2 * (k + 1) = c + 2 * k + 2 from by omega,
        show e + (k + 1) = e + k + 1 from by omega]
    show ⟨0, (b) + 1, c + 2 * k + 2, d', (e + k) + 1⟩ [fm]⊢* ⟨0, b + 3 * (k + 1) + 1, c, d' + 3 * (k + 1), e⟩
    step fm
    rw [show c + 2 * k + 2 = (c + 2 * k + 1) + 1 from by omega]
    step fm
    rw [show c + 2 * k + 1 = (c + 2 * k) + 1 from by omega]
    step fm
    rw [show b + 4 = (b + 3) + 1 from by omega]
    apply stepStar_trans (ih c (b + 3) (d' + 3) e)
    ring_nf; finish

-- R3/R2/R2 drain.
theorem r3r2r2_drain : ∀ k b d' e, ⟨0, b + k, 0, d', e + k⟩ [fm]⊢* ⟨0, b, 0, d' + k, e + 4 * k⟩ := by
  intro k; induction' k with k ih <;> intro b d' e
  · exists 0
  · rw [show b + (k + 1) = (b + k) + 1 from by omega,
        show e + (k + 1) = (e + k) + 1 from by omega]
    show ⟨0, (b + k) + 1, 0, d', (e + k) + 1⟩ [fm]⊢* ⟨0, b, 0, d' + (k + 1), e + 4 * (k + 1)⟩
    step fm
    step fm
    step fm
    rw [show e + k + 4 = (e + 4) + k from by omega]
    apply stepStar_trans (ih b (d' + 1) (e + 4))
    ring_nf; finish

-- Even case: all phases composed via have + rw at
theorem even_trans (k : ℕ) : ⟨0, 0, 0, 2 * k, 4 * k + 2⟩ [fm]⊢⁺ ⟨0, 0, 0, 6 * k + 1, 12 * k + 4⟩ := by
  -- Phase 1: d_to_c
  have h1 : ⟨0, 0, 0, 0 + 2 * k, 4 * k + 2⟩ [fm]⊢* ⟨0, 0, 0 + 2 * k, 0, 4 * k + 2⟩ :=
    d_to_c (2 * k) 0 0
  rw [show (0 : ℕ) + 2 * k = 2 * k from by omega] at h1
  -- Phase 2: R5 step
  have h2 : ⟨0, 0, 2 * k, 0, 4 * k + 2⟩ [fm]⊢ ⟨0, 1, 2 * k, 0, 4 * k + 1⟩ := by
    rw [show (4 * k + 2 : ℕ) = (4 * k + 1) + 1 from by omega]; simp [fm]
  -- Phase 3: r3r1r1_chain
  have h3 : ⟨0, 0 + 1, 0 + 2 * k, 0, (3 * k + 1) + k⟩ [fm]⊢* ⟨0, 0 + 3 * k + 1, 0, 0 + 3 * k, 3 * k + 1⟩ :=
    r3r1r1_chain k 0 0 0 (3 * k + 1)
  rw [show (0 : ℕ) + 1 = 1 from by omega,
      show (0 : ℕ) + 2 * k = 2 * k from by omega,
      show (3 * k + 1) + k = 4 * k + 1 from by omega,
      show 0 + 3 * k + 1 = 3 * k + 1 from by omega,
      show (0 : ℕ) + 3 * k = 3 * k from by omega] at h3
  -- Phase 4: drain
  have h4 : ⟨0, 0 + (3 * k + 1), 0, 3 * k, 0 + (3 * k + 1)⟩ [fm]⊢* ⟨0, 0, 0, 3 * k + (3 * k + 1), 0 + 4 * (3 * k + 1)⟩ :=
    r3r2r2_drain (3 * k + 1) 0 (3 * k) 0
  rw [show (0 : ℕ) + (3 * k + 1) = 3 * k + 1 from by omega,
      show 3 * k + (3 * k + 1) = 6 * k + 1 from by omega,
      show (0 : ℕ) + 4 * (3 * k + 1) = 12 * k + 4 from by omega] at h4
  -- Compose: h1 (⊢*) then h2 (⊢) gives ⊢⁺, then h3 (⊢*) and h4 (⊢*) extend it.
  exact stepPlus_stepStar_stepPlus
    (stepPlus_stepStar_stepPlus (stepStar_step_stepPlus h1 h2) h3) h4

-- Odd case
theorem odd_trans (k : ℕ) : ⟨0, 0, 0, 2 * k + 1, 4 * k + 4⟩ [fm]⊢⁺ ⟨0, 0, 0, 6 * k + 4, 12 * k + 10⟩ := by
  -- Phase 1: d_to_c
  have h1 : ⟨0, 0, 0, 0 + (2 * k + 1), 4 * k + 4⟩ [fm]⊢* ⟨0, 0, 0 + (2 * k + 1), 0, 4 * k + 4⟩ :=
    d_to_c (2 * k + 1) 0 0
  rw [show (0 : ℕ) + (2 * k + 1) = 2 * k + 1 from by omega] at h1
  -- Phase 2: R5 step
  have h2 : ⟨0, 0, 2 * k + 1, 0, 4 * k + 4⟩ [fm]⊢ ⟨0, 1, 2 * k + 1, 0, 4 * k + 3⟩ := by
    rw [show (4 * k + 4 : ℕ) = (4 * k + 3) + 1 from by omega]; simp [fm]
  -- Phase 3: r3r1r1_chain
  have h3 : ⟨0, 0 + 1, 1 + 2 * k, 0, (3 * k + 3) + k⟩ [fm]⊢* ⟨0, 0 + 3 * k + 1, 1, 0 + 3 * k, 3 * k + 3⟩ :=
    r3r1r1_chain k 1 0 0 (3 * k + 3)
  rw [show (0 : ℕ) + 1 = 1 from by omega,
      show (1 : ℕ) + 2 * k = 2 * k + 1 from by omega,
      show (3 * k + 3) + k = 4 * k + 3 from by omega,
      show 0 + 3 * k + 1 = 3 * k + 1 from by omega,
      show (0 : ℕ) + 3 * k = 3 * k from by omega] at h3
  -- Phase 4: R3/R1/R2 (3 steps)
  have h4 : ⟨0, 3 * k + 1, 1, 3 * k, 3 * k + 3⟩ [fm]⊢* ⟨0, 3 * k + 2, 0, 3 * k + 2, 3 * k + 4⟩ := by
    rw [show (3 * k + 1 : ℕ) = (3 * k) + 1 from by omega,
        show (3 * k + 3 : ℕ) = (3 * k + 2) + 1 from by omega]
    step fm  -- R3
    step fm  -- R1
    step fm  -- R2
    finish
  -- Phase 5: drain
  have h5 : ⟨0, 0 + (3 * k + 2), 0, 3 * k + 2, 2 + (3 * k + 2)⟩ [fm]⊢* ⟨0, 0, 0, 3 * k + 2 + (3 * k + 2), 2 + 4 * (3 * k + 2)⟩ :=
    r3r2r2_drain (3 * k + 2) 0 (3 * k + 2) 2
  rw [show (0 : ℕ) + (3 * k + 2) = 3 * k + 2 from by omega,
      show 2 + (3 * k + 2) = 3 * k + 4 from by omega,
      show 3 * k + 2 + (3 * k + 2) = 6 * k + 4 from by omega,
      show 2 + 4 * (3 * k + 2) = 12 * k + 10 from by omega] at h5
  -- Compose
  exact stepPlus_stepStar_stepPlus
    (stepPlus_stepStar_stepPlus
      (stepPlus_stepStar_stepPlus (stepStar_step_stepPlus h1 h2) h3) h4) h5

-- Main transition
theorem main_trans (d : ℕ) : ⟨0, 0, 0, d, 2 * d + 2⟩ [fm]⊢⁺ ⟨0, 0, 0, 3 * d + 1, 2 * (3 * d + 1) + 2⟩ := by
  rcases Nat.even_or_odd d with ⟨k, hk⟩ | ⟨k, hk⟩
  · rw [show k + k = 2 * k from by omega] at hk; subst hk
    have := even_trans k
    rw [show 4 * k + 2 = 2 * (2 * k) + 2 from by omega,
        show 6 * k + 1 = 3 * (2 * k) + 1 from by omega,
        show 12 * k + 4 = 2 * (3 * (2 * k) + 1) + 2 from by omega] at this
    exact this
  · subst hk
    have := odd_trans k
    rw [show 4 * k + 4 = 2 * (2 * k + 1) + 2 from by omega,
        show 6 * k + 4 = 3 * (2 * k + 1) + 1 from by omega,
        show 12 * k + 10 = 2 * (3 * (2 * k + 1) + 1) + 2 from by omega] at this
    exact this

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨0, 0, 0, 0, 2⟩) (by execute fm 1)
  apply progress_nonhalt_simple (fm := fm) (A := ℕ)
    (fun d ↦ ⟨0, 0, 0, d, 2 * d + 2⟩) 0
  intro d; exists 3 * d + 1
  exact main_trans d
