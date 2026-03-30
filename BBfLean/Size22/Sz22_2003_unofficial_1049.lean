import BBfLean.FM
import Mathlib.Tactic.Ring

namespace Sz22_2003_unofficial_1049

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a+2, b+1, c, d, e⟩ => some ⟨a, b, c+1, d, e⟩
  | ⟨a+1, b, c+1, d, e⟩ => some ⟨a, b+1, c, d+2, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b, c, d, e+1⟩
  | ⟨a, b, c, d+1, e⟩ => some ⟨a+1, b, c, d, e⟩
  | ⟨a, b, c, d, e+1⟩ => some ⟨a+2, b, c+1, d, e⟩
  | _ => none

-- R5/R1 chain: (0, b+k, c, 0, e+k) ⊢* (0, b, c+2*k, 0, e)
theorem r5r1_chain : ∀ k, ∀ b c e,
    ⟨(0 : ℕ), b + k, c, 0, e + k⟩ [fm]⊢* ⟨0, b, c + 2 * k, 0, e⟩ := by
  intro k; induction' k with k ih <;> intro b c e
  · ring_nf; finish
  · rw [show b + (k + 1) = (b + k) + 1 from by ring,
        show e + (k + 1) = (e + k) + 1 from by ring]
    step fm; step fm
    have := ih b (c + 2) e
    convert this using 2; ring_nf

-- R4/R2 chain: (0, j, k, d+1, e) ⊢* (0, j+k, 0, d+1+k, e)
theorem r4r2_chain : ∀ k, ∀ j d e,
    ⟨(0 : ℕ), j, k, d + 1, e⟩ [fm]⊢* ⟨0, j + k, 0, d + 1 + k, e⟩ := by
  intro k; induction' k with k ih <;> intro j d e
  · ring_nf; finish
  · step fm; step fm
    have := ih (j + 1) (d + 1) e
    convert this using 2; ring_nf

-- R4/R3 chain: (0, b, 0, k, e) ⊢* (0, b, 0, 0, e+k)
theorem r4r3_chain : ∀ k, ∀ b e,
    ⟨(0 : ℕ), b, 0, k, e⟩ [fm]⊢* ⟨0, b, 0, 0, e + k⟩ := by
  intro k; induction' k with k ih <;> intro b e
  · ring_nf; finish
  · step fm; step fm
    have := ih b (e + 1)
    convert this using 2; ring_nf

theorem main_trans (b r : ℕ) :
    ⟨(0 : ℕ), b + 1, 0, 0, b + r + 3⟩ [fm]⊢⁺
    ⟨0, 2 * b + 3, 0, 0, 2 * b + r + 6⟩ := by
  -- Phase 1: R5/R1 chain (b+1 rounds)
  have h1 : ⟨(0 : ℕ), b + 1, 0, 0, b + r + 3⟩ [fm]⊢*
      ⟨0, 0, 2 * b + 2, 0, r + 2⟩ := by
    have := r5r1_chain (b + 1) 0 0 (r + 2)
    convert this using 2; ring_nf
  -- Phase 2: R5 step + two R2 steps
  have h2 : ⟨(0 : ℕ), 0, 2 * b + 2, 0, r + 2⟩ [fm]⊢⁺
      ⟨0, 2, 2 * b + 1, 4, r + 1⟩ := by
    rw [show r + 2 = (r + 1) + 1 from by ring,
        show 2 * b + 2 = (2 * b + 1) + 1 from by ring]
    step fm
    rw [show (2 * b + 1) + 1 + 1 = ((2 * b + 1) + 1) + 1 from by ring]
    step fm
    rw [show (2 * b + 1) + 1 = (2 * b + 1) + 1 from rfl]
    step fm
    finish
  -- Phase 3: R4/R2 chain (2*b+1 rounds)
  have h3 : ⟨(0 : ℕ), 2, 2 * b + 1, 4, r + 1⟩ [fm]⊢*
      ⟨0, 2 * b + 3, 0, 2 * b + 5, r + 1⟩ := by
    have := r4r2_chain (2 * b + 1) 2 3 (r + 1)
    convert this using 2; ring_nf
  -- Phase 4: R4/R3 chain (2*b+5 rounds)
  have h4 : ⟨(0 : ℕ), 2 * b + 3, 0, 2 * b + 5, r + 1⟩ [fm]⊢*
      ⟨0, 2 * b + 3, 0, 0, 2 * b + r + 6⟩ := by
    have := r4r3_chain (2 * b + 5) (2 * b + 3) (r + 1)
    convert this using 2; ring_nf
  exact stepStar_stepPlus_stepPlus h1
    (stepPlus_stepStar_stepPlus h2 (stepStar_trans h3 h4))

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨0, 1, 0, 0, 3⟩) (by execute fm 8)
  apply progress_nonhalt_simple (fm := fm) (A := ℕ × ℕ)
    (fun ⟨b, r⟩ ↦ ⟨0, b + 1, 0, 0, b + r + 3⟩) ⟨0, 0⟩
  intro ⟨b, r⟩
  refine ⟨⟨2 * b + 2, r + 1⟩, ?_⟩
  convert main_trans b r using 2; ring_nf

end Sz22_2003_unofficial_1049
