import BBfLean.FM
import Mathlib.Tactic.Ring

namespace Sz22_2003_unofficial_1603

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a, b+1, c+1, d, e⟩ => some ⟨a, b, c, d+1, e+1⟩
  | ⟨a, b+1, c, d, e⟩ => some ⟨a+1, b, c, d+1, e⟩
  | ⟨a+1, b, c, d+1, e+1⟩ => some ⟨a, b+2, c, d, e⟩
  | ⟨a, b, c, d+1, e⟩ => some ⟨a, b, c+1, d, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b+1, c, d, e+1⟩
  | _ => none

theorem d_to_c : ∀ k, ∀ a c d, ⟨a, 0, c, d + k, 0⟩ [fm]⊢* ⟨a, 0, c + k, d, 0⟩ := by
  intro k; induction' k with k h <;> intro a c d
  · exists 0
  rw [show d + (k + 1) = (d + k) + 1 from by ring]
  step fm
  apply stepStar_trans (h _ _ _)
  ring_nf; finish

theorem r3r1r1_chain : ∀ k, ∀ d, ⟨k + 1, 0, 2 * k + 1, d + 1, d + 2⟩ [fm]⊢*
    ⟨1, 0, 1, d + k + 1, d + k + 2⟩ := by
  intro k; induction' k with k h <;> intro d
  · exists 0
  rw [show 2 * (k + 1) + 1 = 2 * k + 1 + 2 from by ring]
  step fm; step fm; step fm
  apply stepStar_trans (h _)
  ring_nf; finish

theorem drain_chain : ∀ k, ∀ a d, ⟨a + 1, 0, 0, d + 1, k + 1⟩ [fm]⊢*
    ⟨a + k + 1, 0, 0, d + k + 1, 1⟩ := by
  intro k; induction' k with k h <;> intro a d
  · exists 0
  rw [show (k + 1) + 1 = k + 1 + 1 from by ring]
  step fm; step fm; step fm
  apply stepStar_trans (h _ _)
  ring_nf; finish

theorem main_trans (n : ℕ) : ⟨n + 2, 0, 0, 2 * n + 2, 0⟩ [fm]⊢⁺
    ⟨n + 3, 0, 0, 2 * n + 4, 0⟩ := by
  have h1 : ⟨n + 2, 0, 0, 2 * n + 2, 0⟩ [fm]⊢* ⟨n + 2, 0, 2 * n + 2, 0, 0⟩ := by
    have := d_to_c (2 * n + 2) (n + 2) 0 0
    simp only [Nat.zero_add] at this; exact this
  have h2a : ⟨n + 2, 0, 2 * n + 2, 0, 0⟩ [fm]⊢⁺ ⟨n + 1, 0, 2 * n + 1, 1, 2⟩ := by
    rw [show 2 * n + 2 = (2 * n) + 1 + 1 from by ring]
    step fm; step fm; finish
  have h2b : ⟨n + 1, 0, 2 * n + 1, 1, 2⟩ [fm]⊢* ⟨1, 0, 1, n + 1, n + 2⟩ := by
    have := r3r1r1_chain n 0
    simp only [Nat.zero_add] at this; exact this
  have h2c : ⟨1, 0, 1, n + 1, n + 2⟩ [fm]⊢* ⟨1, 0, 0, n + 2, n + 2⟩ := by
    step fm; step fm; step fm; finish
  have h3a : ⟨1, 0, 0, n + 2, n + 2⟩ [fm]⊢* ⟨n + 2, 0, 0, 2 * n + 3, 1⟩ := by
    rw [show n + 2 = (n + 1) + 1 from by ring]
    have := drain_chain (n + 1) 0 (n + 1)
    simp only [Nat.zero_add] at this
    apply stepStar_trans this
    ring_nf; finish
  have h3b : ⟨n + 2, 0, 0, 2 * n + 3, 1⟩ [fm]⊢* ⟨n + 3, 0, 0, 2 * n + 4, 0⟩ := by
    rw [show 2 * n + 3 = (2 * n + 2) + 1 from by ring]
    step fm; step fm; step fm; ring_nf; finish
  exact stepStar_stepPlus_stepPlus h1
    (stepPlus_stepStar_stepPlus h2a
      (stepStar_trans h2b (stepStar_trans h2c (stepStar_trans h3a h3b))))

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨2, 0, 0, 2, 0⟩) (by execute fm 5)
  apply progress_nonhalt_simple (fm := fm) (A := ℕ)
    (fun n ↦ ⟨n + 2, 0, 0, 2 * n + 2, 0⟩) 0
  intro n; exists n + 1
  exact main_trans n

end Sz22_2003_unofficial_1603
