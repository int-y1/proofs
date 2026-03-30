import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #1073: [5/6, 196/55, 121/2, 3/7, 14/11]

Vector representation:
```
-1 -1  1  0  0
 2  0 -1  2 -1
-1  0  0  0  2
 0  1  0 -1  0
 1  0  0  1 -1
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_1073

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a+1, b+1, c, d, e⟩ => some ⟨a, b, c+1, d, e⟩
  | ⟨a, b, c+1, d, e+1⟩ => some ⟨a+2, b, c, d+2, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b, c, d, e+2⟩
  | ⟨a, b, c, d+1, e⟩ => some ⟨a, b+1, c, d, e⟩
  | ⟨a, b, c, d, e+1⟩ => some ⟨a+1, b, c, d+1, e⟩
  | _ => none

private theorem r4_chain : ∀ k, ∀ b d e,
    ⟨(0 : ℕ), b, 0, d + k, e⟩ [fm]⊢* ⟨0, b + k, 0, d, e⟩ := by
  intro k; induction' k with k ih <;> intro b d e
  · ring_nf; finish
  · rw [show d + (k + 1) = (d + k) + 1 from by ring,
        show b + (k + 1) = (b + 1) + k from by ring]
    step fm; exact ih (b + 1) d e

private theorem r3_drain : ∀ k, ∀ d e,
    ⟨k, (0 : ℕ), 0, d, e⟩ [fm]⊢* ⟨0, 0, 0, d, e + 2 * k⟩ := by
  intro k; induction' k with k ih <;> intro d e
  · ring_nf; finish
  · rw [show e + 2 * (k + 1) = (e + 2) + 2 * k from by ring]
    step fm; exact ih d (e + 2)

private theorem r2_chain_b0 : ∀ k, ∀ a c d e,
    ⟨a, (0 : ℕ), c + k, d, e + k⟩ [fm]⊢* ⟨a + 2 * k, 0, c, d + 2 * k, e⟩ := by
  intro k; induction' k with k ih <;> intro a c d e
  · ring_nf; finish
  · rw [show c + (k + 1) = (c + k) + 1 from by ring,
        show e + (k + 1) = (e + k) + 1 from by ring,
        show a + 2 * (k + 1) = (a + 2) + 2 * k from by ring,
        show d + 2 * (k + 1) = (d + 2) + 2 * k from by ring]
    step fm; exact ih (a + 2) c (d + 2) e

private theorem process_phase : ∀ b, ∀ c d,
    ⟨(2 : ℕ), b, c, d, b + c + 1⟩ [fm]⊢* ⟨b + 2 * c + 2, 0, 0, d + 2 * b + 2 * c, 1⟩ := by
  intro b; induction' b using Nat.strongRecOn with b IH; intro c d
  rcases b with _ | _ | b
  · -- b = 0: use r2_chain_b0
    have := r2_chain_b0 c 2 0 d 1
    rw [show (0 : ℕ) + c + 1 = 1 + c from by ring,
        show (0 : ℕ) + 2 * c + 2 = 2 + 2 * c from by ring,
        show d + 2 * 0 + 2 * c = d + 2 * c from by ring]
    convert this using 2; ring_nf
  · -- b = 1: R1, R2, then r2_chain_b0
    rw [show (1 : ℕ) + c + 1 = (c + 1) + 1 from by ring]
    step fm; step fm
    rw [show (1 : ℕ) + 2 * c + 2 = 3 + 2 * c from by ring,
        show d + 2 * 1 + 2 * c = (d + 2) + 2 * c from by ring]
    convert r2_chain_b0 c 3 0 (d + 2) 1 using 2; ring_nf
  · -- b + 2: R1, R1, R2 (3 steps), then recurse with b
    have h1 : ⟨(2 : ℕ), b + 2, c, d, b + 2 + c + 1⟩ [fm]⊢*
              ⟨2, b, c + 1, d + 2, b + c + 2⟩ := by
      step fm; step fm; step fm; ring_nf; finish
    have h2 := IH b (by omega) (c + 1) (d + 2)
    rw [show b + (c + 1) + 1 = b + c + 2 from by ring,
        show b + 2 * (c + 1) + 2 = b + 2 * c + 4 from by ring,
        show (d + 2) + 2 * b + 2 * (c + 1) = d + 2 * b + 2 * c + 4 from by ring] at h2
    rw [show (b + 2) + 2 * c + 2 = b + 2 * c + 4 from by ring,
        show d + 2 * (b + 2) + 2 * c = d + 2 * b + 2 * c + 4 from by ring]
    exact stepStar_trans h1 h2

private theorem main_trans (d : ℕ) :
    ⟨(0 : ℕ), 0, 0, d, d + 2⟩ [fm]⊢⁺ ⟨0, 0, 0, 2 * d + 1, 2 * d + 3⟩ := by
  rcases d with _ | d
  · execute fm 2
  · have h1 : ⟨(0 : ℕ), 0, 0, d + 1, d + 3⟩ [fm]⊢* ⟨0, d + 1, 0, 0, d + 3⟩ := by
      convert r4_chain (d + 1) 0 0 (d + 3) using 2; ring_nf
    apply stepStar_stepPlus_stepPlus h1
    rw [show d + 3 = (d + 2) + 1 from by ring]
    step fm
    rw [show d + 2 = (d + 1) + 1 from by ring]
    step fm; step fm
    -- After R5, R1, R2: state is (2, d, 0, 3, d+1). Goal is ⊢* to target.
    have h2 : ⟨(2 : ℕ), d, 0, 3, d + 1⟩ [fm]⊢* ⟨d + 2, 0, 0, 2 * d + 3, 1⟩ := by
      have := process_phase d 0 3
      rw [show d + 0 + 1 = d + 1 from by ring,
          show d + 2 * 0 + 2 = d + 2 from by ring,
          show 3 + 2 * d + 2 * 0 = 2 * d + 3 from by ring] at this
      exact this
    have h3 : ⟨d + 2, (0 : ℕ), 0, 2 * d + 3, 1⟩ [fm]⊢*
              ⟨0, 0, 0, 2 * d + 3, 2 * d + 5⟩ := by
      have := r3_drain (d + 2) (2 * d + 3) 1
      rw [show 1 + 2 * (d + 2) = 2 * d + 5 from by ring] at this
      exact this
    rw [show 2 * (d + 1) + 1 = 2 * d + 3 from by ring,
        show 2 * (d + 1) + 3 = 2 * d + 5 from by ring]
    exact stepStar_trans h2 h3

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨0, 0, 0, 0, 2⟩) (by execute fm 1)
  apply progress_nonhalt_simple (fm := fm) (A := ℕ)
    (fun d ↦ ⟨0, 0, 0, d, d + 2⟩) 0
  intro d; exists 2 * d + 1
  exact main_trans d

end Sz22_2003_unofficial_1073
