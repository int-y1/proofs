import BBfLean.FM
import Mathlib.Tactic.Ring

namespace Sz22_2003_unofficial_1059

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a+1, b+2, c, d, e⟩ => some ⟨a, b, c+1, d, e⟩
  | ⟨a, b, c+1, d+1, e⟩ => some ⟨a+2, b, c, d, e+1⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b, c, d+1, e+1⟩
  | ⟨a, b, c, d, e+1⟩ => some ⟨a, b+1, c, d, e⟩
  | ⟨a, b, c, d+1, e⟩ => some ⟨a+1, b, c+1, d, e⟩
  | _ => none

theorem r4_drain : ∀ k b d,
    ⟨(0 : ℕ), b, 0, d, k⟩ [fm]⊢* ⟨0, b + k, 0, d, 0⟩ := by
  intro k; induction' k with k ih <;> intro b d
  · ring_nf; finish
  · rw [show b + (k + 1) = (b + 1) + k from by ring]
    step fm; exact ih (b + 1) d

theorem r2r1r1_chain : ∀ k, ∀ b c d e,
    ⟨(0 : ℕ), b + 4 * k, c + 1, d + k, e⟩ [fm]⊢*
    ⟨0, b, c + 1 + k, d, e + k⟩ := by
  intro k; induction' k with k ih <;> intro b c d e
  · ring_nf; finish
  · rw [show b + 4 * (k + 1) = b + 4 * k + 4 from by ring,
        show d + (k + 1) = (d + k) + 1 from by ring,
        show c + 1 + (k + 1) = c + 2 + k from by ring,
        show e + (k + 1) = (e + 1) + k from by ring]
    have : ⟨(0 : ℕ), b + 4 * k + 4, c + 1, (d + k) + 1, e⟩ [fm]⊢*
           ⟨0, b + 4 * k, c + 2, d + k, e + 1⟩ := by
      step fm; step fm; step fm; ring_nf; finish
    have h := ih b (c + 1) d (e + 1)
    rw [show c + 1 + 1 + k = c + 2 + k from by ring] at h
    exact stepStar_trans this h

theorem r2r3_chain : ∀ k, ∀ a c e,
    ⟨a, (1 : ℕ), c + k + 1, 1, e⟩ [fm]⊢*
    ⟨a + k, 1, c + 1, 1, e + 2 * k⟩ := by
  intro k; induction' k with k ih <;> intro a c e
  · ring_nf; finish
  · rw [show c + (k + 1) + 1 = (c + k + 1) + 1 from by ring,
        show a + (k + 1) = (a + 1) + k from by ring,
        show e + 2 * (k + 1) = (e + 2) + 2 * k from by ring]
    have : ⟨a, (1 : ℕ), (c + k + 1) + 1, 1, e⟩ [fm]⊢*
           ⟨a + 1, 1, c + k + 1, 1, e + 2⟩ := by
      step fm
      rw [show a + 2 = (a + 1) + 1 from by ring]
      step fm; ring_nf; finish
    exact stepStar_trans this (ih (a + 1) c (e + 2))

theorem r3_drain : ∀ k, ∀ d e,
    ⟨k, (1 : ℕ), 0, d, e⟩ [fm]⊢* ⟨0, 1, 0, d + k, e + k⟩ := by
  intro k; induction' k with k ih <;> intro d e
  · ring_nf; finish
  · rw [show d + (k + 1) = (d + 1) + k from by ring,
        show e + (k + 1) = (e + 1) + k from by ring]
    step fm; exact ih (d + 1) (e + 1)

theorem main_trans (n : ℕ) :
    ⟨(0 : ℕ), 1, 0, n + 2, 4 * n + 4⟩ [fm]⊢⁺
    ⟨0, 1, 0, n + 3, 4 * n + 8⟩ := by
  -- Phase 1: R4 drain
  apply stepStar_stepPlus_stepPlus
  · show ⟨(0 : ℕ), 1, 0, n + 2, 4 * n + 4⟩ [fm]⊢*
         ⟨0, 4 * n + 5, 0, n + 2, 0⟩
    have h := r4_drain (4 * n + 4) 1 (n + 2)
    convert h using 2; ring_nf
  -- Phase 2: R5, R1
  apply stepStar_stepPlus_stepPlus
  · show ⟨(0 : ℕ), 4 * n + 5, 0, n + 2, 0⟩ [fm]⊢*
         ⟨0, 4 * n + 3, 2, n + 1, 0⟩
    rw [show (4 * n + 5 : ℕ) = (4 * n + 3) + 2 from by ring,
        show n + 2 = (n + 1) + 1 from by ring]
    step fm
    rw [show (4 * n + 3 : ℕ) = (4 * n + 1) + 2 from by ring]
    step fm; finish
  -- Phase 3: R2,R1,R1 chain (n rounds)
  apply stepStar_stepPlus_stepPlus
  · show ⟨(0 : ℕ), 4 * n + 3, 2, n + 1, 0⟩ [fm]⊢*
         ⟨0, 3, n + 2, 1, n⟩
    have h := r2r1r1_chain n 3 1 1 0
    convert h using 2; ring_nf
  -- Phase 4: R2, R1
  apply stepStar_stepPlus_stepPlus
  · show ⟨(0 : ℕ), 3, n + 2, 1, n⟩ [fm]⊢*
         ⟨1, 1, n + 2, 0, n + 1⟩
    rw [show (n + 2 : ℕ) = (n + 1) + 1 from by ring]
    step fm
    rw [show (3 : ℕ) = 1 + 2 from by ring,
        show n + 1 + 1 = n + 2 from by ring]
    step fm; finish
  -- Phase 5: R3
  apply stepStar_stepPlus_stepPlus
  · show ⟨(1 : ℕ), 1, n + 2, 0, n + 1⟩ [fm]⊢*
         ⟨0, 1, n + 2, 1, n + 2⟩
    step fm; ring_nf; finish
  -- Phase 6: R2,R3 chain (n+1 rounds), then final R2
  apply stepStar_stepPlus_stepPlus
  · show ⟨(0 : ℕ), 1, n + 2, 1, n + 2⟩ [fm]⊢*
         ⟨n + 3, 1, 0, 0, 3 * n + 5⟩
    apply stepStar_trans
    · show ⟨(0 : ℕ), 1, n + 2, 1, n + 2⟩ [fm]⊢*
           ⟨n + 1, 1, 1, 1, 3 * n + 4⟩
      have h := r2r3_chain (n + 1) 0 0 (n + 2)
      convert h using 2; ring_nf
    · show ⟨(n + 1 : ℕ), 1, 1, 1, 3 * n + 4⟩ [fm]⊢*
           ⟨n + 3, 1, 0, 0, 3 * n + 5⟩
      step fm; ring_nf; finish
  -- Phase 7: R3 drain
  apply stepStar_stepPlus
  · show ⟨(n + 3 : ℕ), 1, 0, 0, 3 * n + 5⟩ [fm]⊢*
         ⟨0, 1, 0, n + 3, 4 * n + 8⟩
    have h := r3_drain (n + 3) 0 (3 * n + 5)
    convert h using 2; ring_nf
  · intro heq; simp [Q] at heq

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨0, 1, 0, 2, 4⟩) (by execute fm 7)
  apply progress_nonhalt_simple (fm := fm) (A := ℕ)
    (fun n ↦ ⟨0, 1, 0, n + 2, 4 * n + 4⟩) 0
  intro n
  exact ⟨n + 1, main_trans n⟩

end Sz22_2003_unofficial_1059
