import BBfLean.FM
import Mathlib.Tactic.Ring

namespace Sz22_2003_unofficial_1075

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a+1, b+1, c, d, e⟩ => some ⟨a, b, c+1, d, e⟩
  | ⟨a, b, c+1, d, e+1⟩ => some ⟨a+2, b, c, d+2, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b, c, d, e+2⟩
  | ⟨a, b, c, d+1, e⟩ => some ⟨a, b+1, c, d, e⟩
  | ⟨a, b, c, d, e+1⟩ => some ⟨a, b, c+2, d, e⟩
  | _ => none

private theorem r4_drain : ∀ k b d e,
    ⟨(0 : ℕ), b, 0, d + k, e⟩ [fm]⊢* ⟨0, b + k, 0, d, e⟩ := by
  intro k; induction' k with k ih <;> intro b d e
  · ring_nf; finish
  · rw [show d + (k + 1) = (d + k) + 1 from by ring,
        show b + (k + 1) = (b + 1) + k from by ring]
    step fm; exact ih (b + 1) d e

private theorem r3_drain : ∀ k d e,
    ⟨k, (0 : ℕ), 0, d, e⟩ [fm]⊢* ⟨0, 0, 0, d, e + 2 * k⟩ := by
  intro k; induction' k with k ih <;> intro d e
  · ring_nf; finish
  · rw [show e + 2 * (k + 1) = (e + 2) + 2 * k from by ring]
    step fm; exact ih d (e + 2)

private theorem r2_chain : ∀ k a d e,
    ⟨a, (0 : ℕ), k, d, e + k⟩ [fm]⊢* ⟨a + 2 * k, 0, 0, d + 2 * k, e⟩ := by
  intro k; induction' k with k ih <;> intro a d e
  · ring_nf; finish
  · rw [show e + (k + 1) = (e + k) + 1 from by ring,
        show a + 2 * (k + 1) = (a + 2) + 2 * k from by ring,
        show d + 2 * (k + 1) = (d + 2) + 2 * k from by ring]
    step fm; exact ih (a + 2) (d + 2) e

private theorem r2r1r1_chain : ∀ k b c d e,
    ⟨(0 : ℕ), b + 2 * k, c + 1, d, e + k⟩ [fm]⊢* ⟨0, b, c + 1 + k, d + 2 * k, e⟩ := by
  intro k; induction' k with k ih <;> intro b c d e
  · ring_nf; finish
  · rw [show b + 2 * (k + 1) = (b + 2 * k) + 1 + 1 from by ring,
        show e + (k + 1) = (e + k) + 1 from by ring,
        show c + 1 + (k + 1) = (c + 1 + 1) + k from by ring,
        show d + 2 * (k + 1) = (d + 2) + 2 * k from by ring]
    step fm; step fm; step fm
    exact ih b (c + 1) (d + 2) e

private theorem phase1 (d r : ℕ) :
    ⟨(0 : ℕ), 0, 0, 2 * d, 2 * d + r + 3⟩ [fm]⊢*
    ⟨0, 2 * d, 0, 0, 2 * d + r + 3⟩ := by
  have h := r4_drain (2 * d) 0 0 (2 * d + r + 3)
  simp only [Nat.zero_add] at h; exact h

private theorem phase2 (d r : ℕ) :
    ⟨(0 : ℕ), 2 * d, 0, 0, 2 * d + r + 3⟩ [fm]⊢⁺
    ⟨0, 2 * d, 2, 0, 2 * d + r + 2⟩ := by
  rw [show 2 * d + r + 3 = (2 * d + r + 2) + 1 from by ring]
  step fm; finish

private theorem phase3 (d r : ℕ) :
    ⟨(0 : ℕ), 2 * d, 2, 0, 2 * d + r + 2⟩ [fm]⊢*
    ⟨0, 0, d + 2, 2 * d, d + r + 2⟩ := by
  have h := r2r1r1_chain d 0 1 0 (d + r + 2)
  simp only [Nat.zero_add] at h
  rw [show d + r + 2 + d = 2 * d + r + 2 from by ring,
      show 1 + 1 + d = d + 2 from by ring] at h
  exact h

private theorem phase4 (d r : ℕ) :
    ⟨(0 : ℕ), 0, d + 2, 2 * d, d + r + 2⟩ [fm]⊢*
    ⟨2 * d + 4, 0, 0, 4 * d + 4, r⟩ := by
  have h := r2_chain (d + 2) 0 (2 * d) r
  simp only [Nat.zero_add] at h
  rw [show r + (d + 2) = d + r + 2 from by ring] at h
  convert h using 2; ring_nf

private theorem phase5 (d r : ℕ) :
    ⟨2 * d + 4, (0 : ℕ), 0, 4 * d + 4, r⟩ [fm]⊢*
    ⟨0, 0, 0, 4 * d + 4, 4 * d + r + 8⟩ := by
  have h := r3_drain (2 * d + 4) (4 * d + 4) r
  rw [show r + 2 * (2 * d + 4) = 4 * d + r + 8 from by ring] at h
  exact h

private theorem main_trans (d r : ℕ) :
    ⟨(0 : ℕ), 0, 0, 2 * d, 2 * d + r + 3⟩ [fm]⊢⁺
    ⟨0, 0, 0, 4 * d + 4, 4 * d + r + 8⟩ :=
  stepStar_stepPlus_stepPlus (phase1 d r)
    (stepPlus_stepStar_stepPlus (phase2 d r)
      (stepStar_trans (phase3 d r)
        (stepStar_trans (phase4 d r) (phase5 d r))))

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨0, 0, 0, 4, 7⟩) (by execute fm 8)
  apply progress_nonhalt_simple (fm := fm) (A := ℕ × ℕ)
    (fun ⟨d, r⟩ ↦ ⟨0, 0, 0, 2 * d, 2 * d + r + 3⟩) ⟨2, 0⟩
  intro ⟨d, r⟩; exists ⟨2 * d + 2, r + 1⟩
  show ⟨(0 : ℕ), 0, 0, 2 * d, 2 * d + r + 3⟩ [fm]⊢⁺
       ⟨0, 0, 0, 2 * (2 * d + 2), 2 * (2 * d + 2) + (r + 1) + 3⟩
  rw [show 2 * (2 * d + 2) = 4 * d + 4 from by ring,
      show 4 * d + 4 + (r + 1) + 3 = 4 * d + r + 8 from by ring]
  exact main_trans d r

end Sz22_2003_unofficial_1075
