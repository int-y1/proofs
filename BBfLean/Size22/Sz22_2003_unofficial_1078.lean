import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #1078: [5/6, 196/55, 121/2, 3/7, 6/11]

Vector representation:
```
-1 -1  1  0  0
 2  0 -1  2 -1
-1  0  0  0  2
 0  1  0 -1  0
 1  1  0  0 -1
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_1078

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a+1, b+1, c, d, e⟩ => some ⟨a, b, c+1, d, e⟩
  | ⟨a, b, c+1, d, e+1⟩ => some ⟨a+2, b, c, d+2, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b, c, d, e+2⟩
  | ⟨a, b, c, d+1, e⟩ => some ⟨a, b+1, c, d, e⟩
  | ⟨a, b, c, d, e+1⟩ => some ⟨a+1, b+1, c, d, e⟩
  | _ => none

private theorem r3_drain : ∀ k, ∀ d e,
    ⟨k, (0 : ℕ), 0, d, e⟩ [fm]⊢* ⟨0, 0, 0, d, e + 2 * k⟩ := by
  intro k; induction' k with k ih <;> intro d e
  · ring_nf; finish
  · rw [show e + 2 * (k + 1) = (e + 2) + 2 * k from by ring]
    step fm; exact ih d (e + 2)

private theorem r4_chain : ∀ k, ∀ b d e,
    ⟨(0 : ℕ), b, 0, d + k, e⟩ [fm]⊢* ⟨0, b + k, 0, d, e⟩ := by
  intro k; induction' k with k ih <;> intro b d e
  · ring_nf; finish
  · rw [show d + (k + 1) = (d + k) + 1 from by ring,
        show b + (k + 1) = (b + 1) + k from by ring]
    step fm; exact ih (b + 1) d e

private theorem r2_chain : ∀ k, ∀ a d e,
    ⟨a, (0 : ℕ), k, d, e + k⟩ [fm]⊢* ⟨a + 2 * k, 0, 0, d + 2 * k, e⟩ := by
  intro k; induction' k with k ih <;> intro a d e
  · ring_nf; finish
  · rw [show e + (k + 1) = (e + k) + 1 from by ring,
        show a + 2 * (k + 1) = (a + 2) + 2 * k from by ring,
        show d + 2 * (k + 1) = (d + 2) + 2 * k from by ring]
    step fm; exact ih (a + 2) (d + 2) e

private theorem r1r1r2_chain : ∀ k, ∀ c d,
    ⟨(2 : ℕ), 2 * k, c, d, 2 * k + c⟩ [fm]⊢*
    ⟨2, 0, c + k, d + 2 * k, k + c⟩ := by
  intro k; induction' k with k ih <;> intro c d
  · ring_nf; finish
  · rw [show 2 * (k + 1) = (2 * k + 1) + 1 from by ring,
        show (2 * k + 1) + 1 + c = (2 * k + 1) + (c + 1) from by ring]
    step fm
    rw [show 2 * k + 1 + (c + 1) = (2 * k + c + 1) + 1 from by ring]
    step fm; step fm
    rw [show 2 * k + c + 1 = 2 * k + (c + 1) from by ring]
    have h := ih (c + 1) (d + 2)
    convert stepStar_trans h _ using 1; ring_nf; finish

private theorem process_phase (a : ℕ) :
    ⟨(2 : ℕ), 2 * a, 0, 2, 2 * a⟩ [fm]⊢* ⟨2 * a + 2, 0, 0, 4 * a + 2, 0⟩ := by
  have h1 := r1r1r2_chain a 0 2
  have h2 := r2_chain a 2 (2 * a + 2) 0
  apply stepStar_trans
  · convert h1 using 1
  · convert h2 using 1; ring_nf

private theorem main_trans (a : ℕ) :
    ⟨a + 1, (0 : ℕ), 0, 2 * a, 0⟩ [fm]⊢⁺ ⟨2 * a + 2, 0, 0, 4 * a + 2, 0⟩ := by
  rcases a with _ | a
  · execute fm 4
  · have h1 : ⟨a + 2, (0 : ℕ), 0, 2 * a + 2, 0⟩ [fm]⊢*
              ⟨0, 0, 0, 2 * a + 2, 2 * a + 4⟩ := by
      have := r3_drain (a + 2) (2 * a + 2) 0
      convert this using 1; ring_nf
    have h2 : ⟨(0 : ℕ), 0, 0, 2 * a + 2, 2 * a + 4⟩ [fm]⊢*
              ⟨0, 2 * a + 2, 0, 0, 2 * a + 4⟩ := by
      have := r4_chain (2 * a + 2) 0 0 (2 * a + 4)
      convert this using 1; ring_nf
    have h3 : ⟨(0 : ℕ), 2 * a + 2, 0, 0, 2 * a + 4⟩ [fm]⊢⁺
              ⟨2, 2 * a + 2, 0, 2, 2 * a + 2⟩ := by
      rw [show 2 * a + 4 = (2 * a + 3) + 1 from by ring]
      step fm
      rw [show 2 * a + 3 = (2 * a + 2) + 1 from by ring]
      step fm; step fm; ring_nf; finish
    have h4 : ⟨(2 : ℕ), 2 * a + 2, 0, 2, 2 * a + 2⟩ [fm]⊢*
              ⟨2 * a + 4, 0, 0, 4 * a + 6, 0⟩ := by
      have := process_phase (a + 1)
      convert this using 1
    rw [show 2 * (a + 1) + 2 = 2 * a + 4 from by ring,
        show 4 * (a + 1) + 2 = 4 * a + 6 from by ring]
    exact stepStar_stepPlus_stepPlus h1
      (stepStar_stepPlus_stepPlus h2
        (stepPlus_stepStar_stepPlus h3 h4))

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨1, 0, 0, 0, 0⟩) (by execute fm 0)
  apply progress_nonhalt_simple (fm := fm) (A := ℕ)
    (fun a ↦ ⟨a + 1, 0, 0, 2 * a, 0⟩) 0
  intro a; exists 2 * a + 1
  have h := main_trans a
  convert h using 1; ring_nf

end Sz22_2003_unofficial_1078
