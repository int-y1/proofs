import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #386: [2/15, 99/14, 25/2, 7/11, 42/5]

Vector representation:
```
 1 -1 -1  0  0
-1  2  0 -1  1
-1  0  2  0  0
 0  0  0  1 -1
 1  1 -1  1  0
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_386

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a, b+1, c+1, d, e⟩ => some ⟨a+1, b, c, d, e⟩
  | ⟨a+1, b, c, d+1, e⟩ => some ⟨a, b+2, c, d, e+1⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b, c+2, d, e⟩
  | ⟨a, b, c, d, e+1⟩ => some ⟨a, b, c, d+1, e⟩
  | ⟨a, b, c+1, d, e⟩ => some ⟨a+1, b+1, c, d+1, e⟩
  | _ => none

theorem r2r1r1_loop (k : ℕ) : ∀ a c d e,
    ⟨a+2, 0, c+2*k, d+k, e⟩ [fm]⊢* ⟨a+k+2, 0, c, d, k+e⟩ := by
  induction' k with k ih <;> intro a c d e
  · simp; exists 0
  rw [show c + 2 * (k + 1) = (c + 2) + 2 * k from by ring,
      show d + (k + 1) = (d + 1) + k from by ring]
  apply stepStar_trans (ih a (c + 2) (d + 1) e)
  step fm; step fm; step fm
  ring_nf; finish

theorem r3_repeat (k : ℕ) : ∀ c e,
    ⟨k, 0, c, 0, e⟩ [fm]⊢* ⟨0, 0, c+2*k, 0, e⟩ := by
  induction' k with k ih <;> intro c e
  · simp; exists 0
  step fm
  apply stepStar_trans (ih (c + 2) e)
  ring_nf; finish

theorem r4_repeat (k : ℕ) : ∀ c d,
    ⟨0, 0, c, d, k⟩ [fm]⊢* ⟨0, 0, c, d+k, 0⟩ := by
  induction' k with k ih <;> intro c d
  · simp; exists 0
  step fm
  apply stepStar_trans (ih c (d + 1))
  ring_nf; finish

theorem main_trans (n : ℕ) :
    ⟨n+2, 2, 0, 0, n+2⟩ [fm]⊢⁺ ⟨n+3, 2, 0, 0, n+3⟩ := by
  -- Phase 0: (n+2, 2, 0, 0, n+2) -> (n+3, 0, 0, 0, n+2) in 3 steps
  have h0 : ⟨n+2, 2, 0, 0, n+2⟩ [fm]⊢⁺ ⟨n+3, 0, 0, 0, n+2⟩ := by
    step fm; step fm; step fm; finish
  -- Phase 1: R3 repeated (n+3) times
  have h1 : ⟨n+3, 0, 0, 0, n+2⟩ [fm]⊢* ⟨0, 0, 2*n+6, 0, n+2⟩ := by
    have := r3_repeat (n+3) 0 (n+2)
    simp only [Nat.zero_add] at this
    convert this using 2
  -- Phase 2: R4 repeated (n+2) times
  have h2 : ⟨0, 0, 2*n+6, 0, n+2⟩ [fm]⊢* ⟨0, 0, 2*n+6, n+2, 0⟩ := by
    have := r4_repeat (n+2) (2*n+6) 0
    simp only [Nat.zero_add] at this; exact this
  -- Phase 3: R5 once, then R1 once
  have h3 : ⟨0, 0, 2*n+6, n+2, 0⟩ [fm]⊢* ⟨2, 0, 2*n+4, n+3, 0⟩ := by
    rw [show 2 * n + 6 = (2 * n + 5) + 1 from by ring]
    step fm; step fm
    ring_nf; finish
  -- Phase 4: R2,R1,R1 loop (n+2) times
  have h4 : ⟨2, 0, 2*n+4, n+3, 0⟩ [fm]⊢* ⟨n+4, 0, 0, 1, n+2⟩ := by
    have := r2r1r1_loop (n+2) 0 0 1 0
    simp only [Nat.zero_add, Nat.add_zero] at this
    convert this using 2; ring_nf
  -- Phase 5: Final R2
  have h5 : ⟨n+4, 0, 0, 1, n+2⟩ [fm]⊢* ⟨n+3, 2, 0, 0, n+3⟩ := by
    step fm; finish
  exact stepPlus_stepStar_stepPlus h0
    (stepStar_trans h1 (stepStar_trans h2 (stepStar_trans h3 (stepStar_trans h4 h5))))

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨0+2, 2, 0, 0, 0+2⟩) (by execute fm 16)
  exact progress_nonhalt_simple (fm := fm) (A := ℕ)
    (fun n ↦ ⟨n+2, 2, 0, 0, n+2⟩) 0
    (fun n ↦ ⟨n+1, main_trans n⟩)

end Sz22_2003_unofficial_386
