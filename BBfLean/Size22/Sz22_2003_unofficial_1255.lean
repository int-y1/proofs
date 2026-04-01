import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #1255: [5/6, 77/2, 572/35, 3/13, 15/11]

Vector representation:
```
-1 -1  1  0  0  0
-1  0  0  1  1  0
 2  0 -1 -1  1  1
 0  1  0  0  0 -1
 0  1  1  0 -1  0
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_1255

def Q := ℕ × ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a+1, b+1, c, d, e, f⟩ => some ⟨a, b, c+1, d, e, f⟩
  | ⟨a+1, b, c, d, e, f⟩ => some ⟨a, b, c, d+1, e+1, f⟩
  | ⟨a, b, c+1, d+1, e, f⟩ => some ⟨a+2, b, c, d, e+1, f+1⟩
  | ⟨a, b, c, d, e, f+1⟩ => some ⟨a, b+1, c, d, e, f⟩
  | ⟨a, b, c, d, e+1, f⟩ => some ⟨a, b+1, c+1, d, e, f⟩
  | _ => none

-- R4 drain: move f to b
theorem f_to_b : ∀ k b d e, ⟨(0 : ℕ), b, 0, d, e, k⟩ [fm]⊢* ⟨(0 : ℕ), b + k, 0, d, e, 0⟩ := by
  intro k; induction' k with k ih <;> intro b d e
  · exists 0
  · step fm
    apply stepStar_trans (ih (b + 1) d e)
    ring_nf; finish

-- R3R1R1 chain: each round consumes 2 from b, 1 from d, adds 1 to c, e, f
theorem r3r1r1_chain : ∀ k, ∀ b c d e f,
    ⟨(0 : ℕ), b + 2 * k, c + 1, d + k, e, f⟩ [fm]⊢*
    ⟨(0 : ℕ), b, c + k + 1, d, e + k, f + k⟩ := by
  intro k; induction' k with k ih <;> intro b c d e f
  · exists 0
  · rw [show b + 2 * (k + 1) = (b + 2 * k) + 1 + 1 from by ring,
        show d + (k + 1) = (d + k) + 1 from by ring,
        show c + 1 = c + 1 from rfl]
    step fm; step fm; step fm
    apply stepStar_trans (ih b (c + 1) d (e + 1) (f + 1))
    ring_nf; finish

-- R3R2R2 chain: each round consumes 1 from c, adds 1 to d, 3 to e, 1 to f
theorem r3r2r2_chain : ∀ k, ∀ c d e f,
    ⟨(0 : ℕ), (0 : ℕ), c + k, d + 1, e, f⟩ [fm]⊢*
    ⟨(0 : ℕ), (0 : ℕ), c, d + k + 1, e + 3 * k, f + k⟩ := by
  intro k; induction' k with k ih <;> intro c d e f
  · exists 0
  · rw [show c + (k + 1) = (c + k) + 1 from by ring,
        show d + 1 = d + 1 from rfl]
    step fm; step fm; step fm
    rw [show d + 1 + 1 = (d + 1) + 1 from by ring]
    apply stepStar_trans (ih c (d + 1) (e + 3) (f + 1))
    ring_nf; finish

-- Main transition: canonical state n to n+1
-- Canonical state n: (0, 0, 0, n+2, 2n²+6n+5, 2n+2)
theorem main_trans (n : ℕ) :
    ⟨(0 : ℕ), (0 : ℕ), 0, n + 2, 2 * n * n + 6 * n + 5, 2 * n + 2⟩ [fm]⊢⁺
    ⟨(0 : ℕ), (0 : ℕ), 0, n + 3, 2 * n * n + 10 * n + 13, 2 * n + 4⟩ := by
  -- Phase 1: R4 drain f=2n+2 to b
  have h1 : ⟨(0 : ℕ), 0, 0, n + 2, 2 * n * n + 6 * n + 5, 2 * n + 2⟩ [fm]⊢*
      ⟨0, 2 * n + 2, 0, n + 2, 2 * n * n + 6 * n + 5, 0⟩ := by
    have := f_to_b (2 * n + 2) 0 (n + 2) (2 * n * n + 6 * n + 5)
    convert this using 2; ring_nf
  -- Phase 2: R5 step
  have h2 : ⟨(0 : ℕ), 2 * n + 2, 0, n + 2, 2 * n * n + 6 * n + 5, 0⟩ [fm]⊢⁺
      ⟨0, 2 * n + 3, 1, n + 2, 2 * n * n + 6 * n + 4, 0⟩ := by
    rw [show (2 * n * n + 6 * n + 5 : ℕ) = (2 * n * n + 6 * n + 4) + 1 from by ring]
    step fm; finish
  -- Phase 3: R3R1R1 chain (n+1 rounds)
  have h3 : ⟨(0 : ℕ), 2 * n + 3, 1, n + 2, 2 * n * n + 6 * n + 4, 0⟩ [fm]⊢*
      ⟨0, 1, n + 2, 1, 2 * n * n + 7 * n + 5, n + 1⟩ := by
    rw [show (2 * n + 3 : ℕ) = 1 + 2 * (n + 1) from by ring,
        show (1 : ℕ) = 0 + 1 from rfl,
        show (n + 2 : ℕ) = 1 + (n + 1) from by ring]
    have := r3r1r1_chain (n + 1) 1 0 1 (2 * n * n + 6 * n + 4) 0
    convert this using 2; ring_nf
  -- Phase 4: R3 step
  have h4 : ⟨(0 : ℕ), 1, n + 2, 1, 2 * n * n + 7 * n + 5, n + 1⟩ [fm]⊢*
      ⟨2, 1, n + 1, 0, 2 * n * n + 7 * n + 6, n + 2⟩ := by
    rw [show (n + 2 : ℕ) = (n + 1) + 1 from by ring,
        show (1 : ℕ) = 0 + 1 from rfl]
    step fm; finish
  -- Phase 5: R1 step
  have h5 : ⟨(2 : ℕ), 1, n + 1, 0, 2 * n * n + 7 * n + 6, n + 2⟩ [fm]⊢*
      ⟨1, 0, n + 2, 0, 2 * n * n + 7 * n + 6, n + 2⟩ := by
    step fm; finish
  -- Phase 6: R2 step
  have h6 : ⟨(1 : ℕ), 0, n + 2, 0, 2 * n * n + 7 * n + 6, n + 2⟩ [fm]⊢*
      ⟨0, 0, n + 2, 1, 2 * n * n + 7 * n + 7, n + 2⟩ := by
    step fm; finish
  -- Phase 7: R3R2R2 chain (n+2 rounds)
  have h7 : ⟨(0 : ℕ), (0 : ℕ), n + 2, 1, 2 * n * n + 7 * n + 7, n + 2⟩ [fm]⊢*
      ⟨0, 0, 0, n + 3, 2 * n * n + 10 * n + 13, 2 * n + 4⟩ := by
    rw [show (n + 2 : ℕ) = 0 + (n + 2) from by ring,
        show (1 : ℕ) = 0 + 1 from by ring]
    have := r3r2r2_chain (n + 2) 0 0 (2 * n * n + 7 * n + 7) (n + 2)
    convert this using 2; ring_nf
  exact stepStar_stepPlus_stepPlus h1
    (stepPlus_stepStar_stepPlus h2
      (stepStar_trans h3 (stepStar_trans h4 (stepStar_trans h5 (stepStar_trans h6 h7)))))

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨0, 0, 0, 2, 5, 2⟩) (by execute fm 8)
  apply progress_nonhalt_simple (fm := fm) (A := ℕ)
    (fun n ↦ ⟨0, 0, 0, n + 2, 2 * n * n + 6 * n + 5, 2 * n + 2⟩) 0
  intro n
  refine ⟨n + 1, ?_⟩
  rw [show 2 * (n + 1) * (n + 1) + 6 * (n + 1) + 5 = 2 * n * n + 10 * n + 13 from by ring,
      show n + 1 + 2 = n + 3 from by ring,
      show 2 * (n + 1) + 2 = 2 * n + 4 from by ring]
  exact main_trans n

end Sz22_2003_unofficial_1255
