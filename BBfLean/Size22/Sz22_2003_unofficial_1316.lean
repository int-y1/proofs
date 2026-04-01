import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #1316: [63/10, 143/2, 4/33, 5/7, 10/13]

Vector representation:
```
-1  2 -1  1  0  0
-1  0  0  0  1  1
 2 -1  0  0 -1  0
 0  0  1 -1  0  0
 1  0  1  0  0 -1
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_1316

def Q := ℕ × ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a+1, b, c+1, d, e, f⟩ => some ⟨a, b+2, c, d+1, e, f⟩
  | ⟨a+1, b, c, d, e, f⟩ => some ⟨a, b, c, d, e+1, f+1⟩
  | ⟨a, b+1, c, d, e+1, f⟩ => some ⟨a+2, b, c, d, e, f⟩
  | ⟨a, b, c, d+1, e, f⟩ => some ⟨a, b, c+1, d, e, f⟩
  | ⟨a, b, c, d, e, f+1⟩ => some ⟨a+1, b, c+1, d, e, f⟩
  | _ => none

-- R1R3R1 chain (even c): each round does R1,R3,R1 consuming 2 from c.
theorem r1r3r1_even : ∀ k, ∀ b d e f,
    ⟨1, b, 2 * k, d, e + k, f⟩ [fm]⊢* ⟨1, b + 3 * k, 0, d + 2 * k, e, f⟩ := by
  intro k; induction' k with k ih <;> intro b d e f
  · exists 0
  · rw [show 2 * (k + 1) = 2 * k + 2 from by ring,
        show e + (k + 1) = (e + k) + 1 from by ring]
    step fm; step fm; step fm
    apply stepStar_trans (ih (b + 3) (d + 2) e f)
    ring_nf; finish

-- R1R3R1 chain (odd c): processes pairs then final R1.
theorem r1r3r1_odd : ∀ k, ∀ b d e f,
    ⟨1, b, 2 * k + 1, d, e + k, f⟩ [fm]⊢* ⟨0, b + 3 * k + 2, 0, d + 2 * k + 1, e, f⟩ := by
  intro k; induction' k with k ih <;> intro b d e f
  · step fm; finish
  · rw [show 2 * (k + 1) + 1 = 2 * k + 3 from by ring,
        show e + (k + 1) = (e + k) + 1 from by ring]
    step fm; step fm; step fm
    apply stepStar_trans (ih (b + 3) (d + 2) e f)
    ring_nf; finish

-- R3R2R2 drain: each round does R3,R2,R2 draining 1 from b.
theorem r3r2r2_drain : ∀ k, ∀ b d e f,
    ⟨0, b + k, 0, d, e + 1, f⟩ [fm]⊢* ⟨0, b, 0, d, e + k + 1, f + 2 * k⟩ := by
  intro k; induction' k with k ih <;> intro b d e f
  · exists 0
  · rw [show b + (k + 1) = (b + k) + 1 from by ring]
    step fm; step fm; step fm
    apply stepStar_trans (ih b d (e + 1) (f + 2))
    ring_nf; finish

-- R4 drain: converts d to c.
theorem r4_drain : ∀ k, ∀ c e f, ⟨0, 0, c, d + k, e, f⟩ [fm]⊢* ⟨0, 0, c + k, d, e, f⟩ := by
  intro k; induction' k with k ih <;> intro c e f
  · exists 0
  · rw [show d + (k + 1) = (d + k) + 1 from by ring]
    step fm
    apply stepStar_trans (ih (c + 1) e f)
    ring_nf; finish

-- Transition 1: odd c to even c.
theorem trans_odd_to_even (m : ℕ) :
    (⟨0, 0, 2 * m + 1, 0, (m + 1) * (2 * m + 3), 3 * (m + 1) * (2 * m + 1) + 1⟩ : Q) [fm]⊢⁺
    ⟨0, 0, 2 * m + 2, 0, (m + 2) * (2 * m + 3), 3 * (m + 1) * (2 * m + 3) + 1⟩ := by
  -- Phase 1: R5 step
  have h1 : (⟨0, 0, 2 * m + 1, 0, (m + 1) * (2 * m + 3), 3 * (m + 1) * (2 * m + 1) + 1⟩ : Q) [fm]⊢
      ⟨1, 0, 2 * (m + 1), 0, (m + 1) * (2 * m + 3), 3 * (m + 1) * (2 * m + 1)⟩ := by
    unfold fm; ring_nf
  -- Phase 2: R1R3R1 even with k = m+1
  have h2 : (⟨1, 0, 2 * (m + 1), 0, (m + 1) * (2 * m + 3), 3 * (m + 1) * (2 * m + 1)⟩ : Q) [fm]⊢*
      ⟨1, 3 * (m + 1), 0, 2 * (m + 1), 2 * (m + 1) * (m + 1), 3 * (m + 1) * (2 * m + 1)⟩ := by
    have := r1r3r1_even (m + 1) 0 0 (2 * (m + 1) * (m + 1)) (3 * (m + 1) * (2 * m + 1))
    simp only [Nat.zero_add] at this
    convert this using 2; ring_nf
  -- Phase 3: R2 step
  have h3 : (⟨1, 3 * (m + 1), 0, 2 * (m + 1), 2 * (m + 1) * (m + 1), 3 * (m + 1) * (2 * m + 1)⟩ : Q) [fm]⊢
      ⟨0, 3 * (m + 1), 0, 2 * (m + 1), 2 * (m + 1) * (m + 1) + 1, 3 * (m + 1) * (2 * m + 1) + 1⟩ := by
    unfold fm; ring_nf
  -- Phase 4: R3R2R2 drain with k = 3(m+1)
  have h4 : (⟨0, 3 * (m + 1), 0, 2 * (m + 1), 2 * (m + 1) * (m + 1) + 1, 3 * (m + 1) * (2 * m + 1) + 1⟩ : Q) [fm]⊢*
      ⟨0, 0, 0, 2 * (m + 1), (m + 2) * (2 * m + 3), 3 * (m + 1) * (2 * m + 3) + 1⟩ := by
    have := r3r2r2_drain (3 * (m + 1)) 0 (2 * (m + 1))
      (2 * (m + 1) * (m + 1)) (3 * (m + 1) * (2 * m + 1) + 1)
    simp only [Nat.zero_add] at this
    convert this using 2; ring_nf
  -- Phase 5: R4 drain with d = 2(m+1)
  have h5 : (⟨0, 0, 0, 2 * (m + 1), (m + 2) * (2 * m + 3), 3 * (m + 1) * (2 * m + 3) + 1⟩ : Q) [fm]⊢*
      ⟨0, 0, 2 * m + 2, 0, (m + 2) * (2 * m + 3), 3 * (m + 1) * (2 * m + 3) + 1⟩ := by
    have := r4_drain (2 * (m + 1)) 0 ((m + 2) * (2 * m + 3))
      (3 * (m + 1) * (2 * m + 3) + 1) (d := 0)
    simp only [Nat.zero_add] at this
    convert this using 2
  -- Compose
  exact step_stepStar_stepPlus h1
    (stepStar_trans (step_stepStar h3)
      (stepStar_trans h4 h5) |> stepStar_trans h2)

-- Transition 2: even c to odd c.
theorem trans_even_to_odd (m : ℕ) :
    (⟨0, 0, 2 * m + 2, 0, (m + 2) * (2 * m + 3), 3 * (m + 1) * (2 * m + 3) + 1⟩ : Q) [fm]⊢⁺
    ⟨0, 0, 2 * m + 3, 0, (m + 2) * (2 * m + 5), 3 * (m + 2) * (2 * m + 3) + 1⟩ := by
  -- Phase 1: R5 step
  have h1 : (⟨0, 0, 2 * m + 2, 0, (m + 2) * (2 * m + 3), 3 * (m + 1) * (2 * m + 3) + 1⟩ : Q) [fm]⊢
      ⟨1, 0, 2 * (m + 1) + 1, 0, (m + 2) * (2 * m + 3), 3 * (m + 1) * (2 * m + 3)⟩ := by
    unfold fm; ring_nf
  -- Phase 2: R1R3R1 odd with k = m+1
  have h2 : (⟨1, 0, 2 * (m + 1) + 1, 0, (m + 2) * (2 * m + 3), 3 * (m + 1) * (2 * m + 3)⟩ : Q) [fm]⊢*
      ⟨0, 3 * m + 5, 0, 2 * m + 3, 2 * m * m + 6 * m + 5, 3 * (m + 1) * (2 * m + 3)⟩ := by
    have := r1r3r1_odd (m + 1) 0 0 (2 * m * m + 6 * m + 5) (3 * (m + 1) * (2 * m + 3))
    simp only [Nat.zero_add] at this
    convert this using 2; ring_nf
  -- Phase 3: R3R2R2 drain with k = 3m+5
  have h3 : (⟨0, 3 * m + 5, 0, 2 * m + 3, 2 * m * m + 6 * m + 5, 3 * (m + 1) * (2 * m + 3)⟩ : Q) [fm]⊢*
      ⟨0, 0, 0, 2 * m + 3, (m + 2) * (2 * m + 5), 3 * (m + 2) * (2 * m + 3) + 1⟩ := by
    have := r3r2r2_drain (3 * m + 5) 0 (2 * m + 3)
      (2 * m * m + 6 * m + 4) (3 * (m + 1) * (2 * m + 3))
    simp only [Nat.zero_add] at this
    convert this using 2; ring_nf
  -- Phase 4: R4 drain
  have h4 : (⟨0, 0, 0, 2 * m + 3, (m + 2) * (2 * m + 5), 3 * (m + 2) * (2 * m + 3) + 1⟩ : Q) [fm]⊢*
      ⟨0, 0, 2 * m + 3, 0, (m + 2) * (2 * m + 5), 3 * (m + 2) * (2 * m + 3) + 1⟩ := by
    have := r4_drain (2 * m + 3) 0 ((m + 2) * (2 * m + 5))
      (3 * (m + 2) * (2 * m + 3) + 1) (d := 0)
    simp only [Nat.zero_add] at this
    convert this using 2
  -- Compose
  exact step_stepStar_stepPlus h1
    (stepStar_trans h2 (stepStar_trans h3 h4))

-- Full two-step transition
theorem main_trans (m : ℕ) :
    (⟨0, 0, 2 * m + 1, 0, (m + 1) * (2 * m + 3), 3 * (m + 1) * (2 * m + 1) + 1⟩ : Q) [fm]⊢⁺
    ⟨0, 0, 2 * m + 3, 0, (m + 2) * (2 * m + 5), 3 * (m + 2) * (2 * m + 3) + 1⟩ :=
  stepPlus_trans (trans_odd_to_even m) (trans_even_to_odd m)

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨0, 0, 1, 0, 3, 4⟩) (by execute fm 10)
  apply progress_nonhalt_simple (fm := fm) (A := ℕ)
    (fun m ↦ ⟨0, 0, 2 * m + 1, 0, (m + 1) * (2 * m + 3), 3 * (m + 1) * (2 * m + 1) + 1⟩) 0
  intro m; exists m + 1
  exact main_trans m

end Sz22_2003_unofficial_1316
