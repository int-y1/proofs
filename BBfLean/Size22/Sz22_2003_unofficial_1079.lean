import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #1079: [5/6, 196/55, 1331/2, 3/7, 5/11]

Vector representation:
```
-1 -1  1  0  0
 2  0 -1  2 -1
-1  0  0  0  3
 0  1  0 -1  0
 0  0  1  0 -1
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_1079

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a+1, b+1, c, d, e⟩ => some ⟨a, b, c+1, d, e⟩
  | ⟨a, b, c+1, d, e+1⟩ => some ⟨a+2, b, c, d+2, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b, c, d, e+3⟩
  | ⟨a, b, c, d+1, e⟩ => some ⟨a, b+1, c, d, e⟩
  | ⟨a, b, c, d, e+1⟩ => some ⟨a, b, c+1, d, e⟩
  | _ => none

private theorem r4_chain : ∀ k, ∀ b d e,
    ⟨(0 : ℕ), b, 0, d + k, e⟩ [fm]⊢* ⟨0, b + k, 0, d, e⟩ := by
  intro k; induction' k with k ih <;> intro b d e
  · ring_nf; finish
  · rw [show d + (k + 1) = (d + k) + 1 from by ring,
        show b + (k + 1) = (b + 1) + k from by ring]
    step fm; exact ih (b + 1) d e

private theorem r3_drain : ∀ k, ∀ d e,
    ⟨k, (0 : ℕ), 0, d, e⟩ [fm]⊢* ⟨0, 0, 0, d, e + 3 * k⟩ := by
  intro k; induction' k with k ih <;> intro d e
  · ring_nf; finish
  · rw [show e + 3 * (k + 1) = (e + 3) + 3 * k from by ring]
    step fm; exact ih d (e + 3)

private theorem r2_chain : ∀ k, ∀ a d e,
    ⟨a, (0 : ℕ), k, d, e + k⟩ [fm]⊢* ⟨a + 2 * k, 0, 0, d + 2 * k, e⟩ := by
  intro k; induction' k with k ih <;> intro a d e
  · ring_nf; finish
  · rw [show e + (k + 1) = (e + k) + 1 from by ring,
        show a + 2 * (k + 1) = (a + 2) + 2 * k from by ring,
        show d + 2 * (k + 1) = (d + 2) + 2 * k from by ring]
    step fm; exact ih (a + 2) (d + 2) e

private theorem process_phase : ∀ b, ∀ c D E,
    ⟨(2 : ℕ), b, c, D, b + c + E⟩ [fm]⊢* ⟨b + 2 * c + 2, 0, 0, D + 2 * b + 2 * c, E⟩ := by
  intro b; induction' b using Nat.strongRecOn with b IH; intro c D E
  rcases b with _ | _ | b
  · -- b = 0
    rw [show (0 : ℕ) + c + E = E + c from by ring,
        show (0 : ℕ) + 2 * c + 2 = 2 + 2 * c from by ring,
        show D + 2 * 0 + 2 * c = D + 2 * c from by ring]
    exact r2_chain c 2 D E
  · -- b = 1
    rw [show (1 : ℕ) + c + E = (c + E) + 1 from by ring]
    step fm
    rw [show (1 : ℕ) + 2 * c + 2 = 2 * (c + 1) + 1 from by ring,
        show D + 2 * 1 + 2 * c = D + 2 * (c + 1) from by ring]
    convert r2_chain (c + 1) 1 D E using 2; ring_nf
  · -- b + 2
    rw [show (b + 2 : ℕ) + c + E = (b + c + E) + 1 + 1 from by ring]
    step fm; step fm; step fm
    rw [show (b + 2) + 2 * c + 2 = b + 2 * c + 4 from by ring,
        show D + 2 * (b + 2) + 2 * c = D + 2 * b + 2 * c + 4 from by ring]
    have h := IH b (by omega) (c + 1) (D + 2) E
    rw [show b + (c + 1) + E = b + c + E + 1 from by ring,
        show b + 2 * (c + 1) + 2 = b + 2 * c + 4 from by ring,
        show (D + 2) + 2 * b + 2 * (c + 1) = D + 2 * b + 2 * c + 4 from by ring] at h
    exact h

private theorem main_trans (d : ℕ) :
    ⟨(0 : ℕ), 0, 0, d, 2 * d + 3⟩ [fm]⊢⁺ ⟨0, 0, 0, 2 * d + 2, 4 * d + 7⟩ := by
  -- Phase 1: R4 chain
  have h1 : ⟨(0 : ℕ), 0, 0, d, 2 * d + 3⟩ [fm]⊢* ⟨0, d, 0, 0, 2 * d + 3⟩ := by
    have := r4_chain d 0 0 (2 * d + 3)
    simp only [Nat.zero_add] at this; exact this
  apply stepStar_stepPlus_stepPlus h1
  -- Phase 2: R5 step
  rw [show 2 * d + 3 = (2 * d + 2) + 1 from by ring]
  step fm
  -- Phase 3: R2 step
  rw [show 2 * d + 2 = (2 * d + 1) + 1 from by ring]
  step fm
  -- Phase 4: process phase
  have h4 : ⟨(2 : ℕ), d, 0, 2, 2 * d + 1⟩ [fm]⊢* ⟨d + 2, 0, 0, 2 * d + 2, d + 1⟩ := by
    have := process_phase d 0 2 (d + 1)
    rw [show d + 0 + (d + 1) = 2 * d + 1 from by ring,
        show d + 2 * 0 + 2 = d + 2 from by ring,
        show 2 + 2 * d + 2 * 0 = 2 * d + 2 from by ring] at this
    exact this
  -- Phase 5: R3 drain
  have h5 : ⟨d + 2, (0 : ℕ), 0, 2 * d + 2, d + 1⟩ [fm]⊢*
             ⟨0, 0, 0, 2 * d + 2, 4 * d + 7⟩ := by
    have := r3_drain (d + 2) (2 * d + 2) (d + 1)
    rw [show d + 1 + 3 * (d + 2) = 4 * d + 7 from by ring] at this
    exact this
  exact stepStar_trans h4 h5

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨0, 0, 0, 0, 3⟩) (by execute fm 1)
  apply progress_nonhalt_simple (fm := fm) (A := ℕ)
    (fun d ↦ ⟨0, 0, 0, d, 2 * d + 3⟩) 0
  intro d; exists 2 * d + 2
  rw [show 2 * (2 * d + 2) + 3 = 4 * d + 7 from by ring]
  exact main_trans d

end Sz22_2003_unofficial_1079
