import BBfLean.FM
import Mathlib.Tactic.Ring

namespace Sz22_2003_unofficial_1080

def Q := ℕ × ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a+1, b+1, c, d, e, f⟩ => some ⟨a, b, c+1, d, e, f⟩
  | ⟨a, b, c+1, d, e+1, f⟩ => some ⟨a+2, b, c, d+2, e, f⟩
  | ⟨a+1, b, c, d, e, f⟩ => some ⟨a, b, c, d, e+2, f+1⟩
  | ⟨a, b, c, d+1, e, f⟩ => some ⟨a, b+1, c, d, e, f⟩
  | ⟨a, b, c, d, e, f+1⟩ => some ⟨a, b, c+1, d, e, f⟩
  | _ => none

theorem r4_chain : ∀ k b e f,
    ⟨(0 : ℕ), b, 0, k, e, f⟩ [fm]⊢* ⟨0, b + k, 0, 0, e, f⟩ := by
  intro k; induction' k with k ih <;> intro b e f
  · ring_nf; finish
  · rw [show b + (k + 1) = (b + 1) + k from by ring]
    step fm
    apply stepStar_trans (ih (b + 1) e f)
    ring_nf; finish

theorem r3_chain : ∀ k d e f,
    ⟨k, (0 : ℕ), 0, d, e, f⟩ [fm]⊢* ⟨0, 0, 0, d, e + 2 * k, f + k⟩ := by
  intro k; induction' k with k ih <;> intro d e f
  · ring_nf; finish
  · rw [show e + 2 * (k + 1) = (e + 2) + 2 * k from by ring,
        show f + (k + 1) = (f + 1) + k from by ring]
    step fm
    apply stepStar_trans (ih d (e + 2) (f + 1))
    ring_nf; finish

theorem r2_chain : ∀ k a d e f,
    ⟨a, (0 : ℕ), k, d, k + e, f⟩ [fm]⊢* ⟨a + 2 * k, 0, 0, d + 2 * k, e, f⟩ := by
  intro k; induction' k with k ih <;> intro a d e f
  · ring_nf; finish
  · rw [show a + 2 * (k + 1) = (a + 2) + 2 * k from by ring,
        show d + 2 * (k + 1) = (d + 2) + 2 * k from by ring,
        show (k + 1 : ℕ) + e = (k + e) + 1 from by ring]
    step fm
    apply stepStar_trans (ih (a + 2) (d + 2) e f)
    ring_nf; finish

theorem r2r1r1_chain : ∀ k c d e f,
    ⟨(0 : ℕ), 2 * k, c + 1, d, e + k, f⟩ [fm]⊢*
    ⟨0, 0, c + 1 + k, d + 2 * k, e, f⟩ := by
  intro k; induction' k with k ih <;> intro c d e f
  · ring_nf; finish
  · rw [show 2 * (k + 1) = (2 * k + 1) + 1 from by ring,
        show e + (k + 1) = (e + k) + 1 from by ring,
        show c + 1 + (k + 1) = (c + 1 + 1) + k from by ring,
        show d + ((2 * k + 1) + 1) = (d + 2) + 2 * k from by ring]
    step fm; step fm; step fm
    apply stepStar_trans (ih (c + 1) (d + 2) e f)
    ring_nf; finish

theorem main_transition (K E F : ℕ) :
    ⟨(0 : ℕ), 0, 0, 2 * K, (2 * K + E) + 1, (K + F) + 1⟩ [fm]⊢⁺
    ⟨0, 0, 0, 4 * K + 2, (4 * K + E) + 4, (3 * K + F) + 2⟩ := by
  -- Phase 1: R4 chain: (0,0,0,2K,...) ⊢* (0,2K,0,0,...)
  have h1 := r4_chain (2 * K) 0 ((2 * K + E) + 1) ((K + F) + 1)
  -- Phase 2: R5 (1 step)
  have h2 : ⟨(0 : ℕ), 0 + 2 * K, 0, 0, (2 * K + E) + 1, (K + F) + 1⟩ [fm]⊢
      ⟨0, 0 + 2 * K, 1, 0, (2 * K + E) + 1, K + F⟩ := by
    simp [fm]
  -- Phase 3: R2R1R1 chain (K rounds)
  have h3_raw := r2r1r1_chain K 0 0 (K + E + 1) (K + F)
  have h3 : ⟨(0 : ℕ), 0 + 2 * K, 1, 0, (2 * K + E) + 1, K + F⟩ [fm]⊢*
      ⟨0, 0, K + 1, 2 * K, K + E + 1, K + F⟩ := by
    convert h3_raw using 2; all_goals ring_nf
  -- Phase 4: R2 chain (K+1 times)
  have h4_raw := r2_chain (K + 1) 0 (2 * K) E (K + F)
  have h4 : ⟨(0 : ℕ), 0, K + 1, 2 * K, K + E + 1, K + F⟩ [fm]⊢*
      ⟨2 * K + 2, 0, 0, 4 * K + 2, E, K + F⟩ := by
    convert h4_raw using 2; all_goals ring_nf
  -- Phase 5: R3 chain (2K+2 times)
  have h5_raw := r3_chain (2 * K + 2) (4 * K + 2) E (K + F)
  have h5 : ⟨2 * K + 2, (0 : ℕ), 0, 4 * K + 2, E, K + F⟩ [fm]⊢*
      ⟨0, 0, 0, 4 * K + 2, (4 * K + E) + 4, (3 * K + F) + 2⟩ := by
    convert h5_raw using 2; all_goals ring_nf
  -- Compose
  exact stepPlus_stepStar_stepPlus
    (stepPlus_stepStar_stepPlus
      (stepPlus_stepStar_stepPlus
        (stepStar_step_stepPlus h1 h2) h3) h4) h5

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨0, 0, 0, 0, 2, 1⟩)
  · execute fm 1
  apply progress_nonhalt_simple (fm := fm) (A := ℕ × ℕ × ℕ)
    (fun ⟨K, E, F⟩ ↦ ⟨0, 0, 0, 2 * K, (2 * K + E) + 1, (K + F) + 1⟩) ⟨0, 1, 0⟩
  intro ⟨K, E, F⟩
  exact ⟨⟨2 * K + 1, E + 1, K + F⟩, by
    show ⟨(0 : ℕ), 0, 0, 2 * K, (2 * K + E) + 1, (K + F) + 1⟩ [fm]⊢⁺
      ⟨0, 0, 0, 2 * (2 * K + 1), (2 * (2 * K + 1) + (E + 1)) + 1,
       ((2 * K + 1) + (K + F)) + 1⟩
    convert main_transition K E F using 2; all_goals ring_nf⟩

end Sz22_2003_unofficial_1080
