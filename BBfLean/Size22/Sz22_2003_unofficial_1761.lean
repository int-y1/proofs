import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #1761: [9/10, 22/21, 343/2, 5/11, 22/7]

Vector representation:
```
-1  2 -1  0  0
 1 -1  0 -1  1
-1  0  0  3  0
 0  0  1  0 -1
 1  0  0 -1  1
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_1761

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a+1, b, c+1, d, e⟩ => some ⟨a, b+2, c, d, e⟩
  | ⟨a, b+1, c, d+1, e⟩ => some ⟨a+1, b, c, d, e+1⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b, c, d+3, e⟩
  | ⟨a, b, c, d, e+1⟩ => some ⟨a, b, c+1, d, e⟩
  | ⟨a, b, c, d+1, e⟩ => some ⟨a+1, b, c, d, e+1⟩
  | _ => none

theorem e_to_c : ∀ k, ∀ c d, ⟨0, 0, c, d, k⟩ [fm]⊢* ⟨0, 0, c + k, d, 0⟩ := by
  intro k; induction' k with k ih <;> intro c d
  · exists 0
  · apply stepStar_trans
      (step_stepStar (show fm ⟨0, 0, c, d, k + 1⟩ = some ⟨0, 0, c + 1, d, k⟩ from by simp [fm]))
    apply stepStar_trans (ih (c + 1) d); ring_nf; finish

theorem r3_drain : ∀ A, ∀ d e, ⟨A, 0, 0, d, e⟩ [fm]⊢* ⟨0, 0, 0, d + 3 * A, e⟩ := by
  intro A; induction' A with A ih <;> intro d e
  · exists 0
  · step fm; apply stepStar_trans (ih (d + 3) e); ring_nf; finish

theorem r2r1_chain : ∀ k, ∀ B D E,
    ⟨0, B + 1, k, D + k, E⟩ [fm]⊢* ⟨0, B + 1 + k, 0, D, E + k⟩ := by
  intro k; induction' k with k ih <;> intro B D E
  · exists 0
  · step fm; step fm
    show ⟨0, (B + 1) + 1, k, D + k, E + 1⟩ [fm]⊢* ⟨0, B + 1 + (k + 1), 0, D, E + (k + 1)⟩
    apply stepStar_trans (ih (B + 1) D (E + 1)); ring_nf; finish

theorem r2r3_drain : ∀ B, ∀ A D E,
    ⟨A, B, 0, D + 1, E⟩ [fm]⊢* ⟨0, 0, 0, D + 1 + 2 * B + 3 * A, E + B⟩ := by
  intro B; induction' B with B ih <;> intro A D E
  · exact r3_drain A (D + 1) E
  · step fm
    rcases D with _ | D'
    · step fm
      show ⟨A, B, 0, 2 + 1, E + 1⟩ [fm]⊢* ⟨0, 0, 0, 0 + 1 + 2 * (B + 1) + 3 * A, E + (B + 1)⟩
      apply stepStar_trans (ih A 2 (E + 1)); ring_nf; finish
    · apply stepStar_trans (ih (A + 1) D' (E + 1)); ring_nf; finish

theorem main_trans : ∀ F e,
    ⟨0, 0, 0, e + F + 1, e⟩ [fm]⊢⁺ ⟨0, 0, 0, 2 * e + F + 3, 2 * e + 1⟩ := by
  intro F e; rcases e with _ | e
  · step fm; step fm; finish
  · have h1 : ⟨0, 0, 0, e + 1 + F + 1, e + 1⟩ [fm]⊢* ⟨0, 0, 0 + (e + 1), e + 1 + F + 1, 0⟩ :=
      e_to_c (e + 1) 0 (e + 1 + F + 1)
    simp only [Nat.zero_add] at h1
    have h2 : ⟨0, 0, e + 1, e + 1 + F + 1, 0⟩ [fm]⊢ ⟨1, 0, e + 1, e + 1 + F, 1⟩ := by simp [fm]
    have h3 : ⟨1, 0, e + 1, e + 1 + F, 1⟩ [fm]⊢ ⟨0, 2, e, e + 1 + F, 1⟩ := by simp [fm]
    have h4 : ⟨0, 2, e, e + 1 + F, 1⟩ [fm]⊢* ⟨0, e + 2, 0, F + 1, e + 1⟩ := by
      rw [show e + 1 + F = (F + 1) + e from by ring]
      have := r2r1_chain e 1 (F + 1) 1
      rw [show 1 + 1 + e = e + 2 from by ring, show 1 + e = e + 1 from by ring] at this
      exact this
    have h5 : ⟨0, e + 2, 0, F + 1, e + 1⟩ [fm]⊢*
        ⟨0, 0, 0, F + 1 + 2 * (e + 2) + 3 * 0, e + 1 + (e + 2)⟩ :=
      r2r3_drain (e + 2) 0 F (e + 1)
    apply stepStar_stepPlus_stepPlus (c₂ := ⟨0, 0, e + 1, e + 1 + F + 1, 0⟩) h1
    apply step_stepPlus_stepPlus h2
    apply step_stepStar_stepPlus h3
    apply stepStar_trans h4
    apply stepStar_trans h5
    ring_nf; finish

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨0, 0, 0, 3, 0⟩) (by unfold c₀; execute fm 1)
  apply progress_nonhalt_simple (fm := fm) (A := ℕ × ℕ)
    (fun ⟨F, e⟩ ↦ ⟨0, 0, 0, e + F + 1, e⟩) ⟨2, 0⟩
  intro ⟨F, e⟩
  refine ⟨⟨F + 1, 2 * e + 1⟩, ?_⟩
  show ⟨0, 0, 0, e + F + 1, e⟩ [fm]⊢⁺ ⟨0, 0, 0, 2 * e + 1 + (F + 1) + 1, 2 * e + 1⟩
  rw [show 2 * e + 1 + (F + 1) + 1 = 2 * e + F + 3 from by ring]
  exact main_trans F e
