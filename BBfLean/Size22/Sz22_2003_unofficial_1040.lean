import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #1040: [45/2, 4/105, 11/5, 91/33, 5/13]

This Fractran program doesn't halt.

Canonical form: (0, 2*f + 2*n + 4, n + 2, 0, 0, f) with recurrence (n, f) -> (n+1, f+n+1).

Author: Claude
-/

namespace Sz22_2003_unofficial_1040

def Q := ℕ × ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a+1, b, c, d, e, f⟩ => some ⟨a, b+2, c+1, d, e, f⟩
  | ⟨a, b+1, c+1, d+1, e, f⟩ => some ⟨a+2, b, c, d, e, f⟩
  | ⟨a, b, c+1, d, e, f⟩ => some ⟨a, b, c, d, e+1, f⟩
  | ⟨a, b+1, c, d, e+1, f⟩ => some ⟨a, b, c, d+1, e, f+1⟩
  | ⟨a, b, c, d, e, f+1⟩ => some ⟨a, b, c+1, d, e, f⟩
  | _ => none

theorem r3_chain (k : ℕ) : ∀ b c e f,
    ⟨(0 : ℕ), b, c + k, 0, e, f⟩ [fm]⊢* ⟨0, b, c, 0, e + k, f⟩ := by
  induction' k with k ih <;> intro b c e f
  · ring_nf; finish
  · rw [show c + (k + 1) = (c + k) + 1 from by ring,
        show e + (k + 1) = (e + 1) + k from by ring]
    step fm
    apply stepStar_trans (ih b c (e + 1) f)
    ring_nf; finish

theorem r4_chain (k : ℕ) : ∀ b d f,
    ⟨(0 : ℕ), b + k, 0, d, k, f⟩ [fm]⊢* ⟨0, b, 0, d + k, 0, f + k⟩ := by
  induction' k with k ih <;> intro b d f
  · ring_nf; finish
  · rw [show b + (k + 1) = (b + k) + 1 from by ring,
        show d + (k + 1) = (d + 1) + k from by ring,
        show f + (k + 1) = (f + 1) + k from by ring]
    step fm
    apply stepStar_trans (ih b (d + 1) (f + 1))
    ring_nf; finish

theorem r2r1r1_chain (k : ℕ) : ∀ b c f,
    ⟨(0 : ℕ), b + k, c + 1, k, 0, f⟩ [fm]⊢* ⟨0, b + 4 * k, c + 1 + k, 0, 0, f⟩ := by
  induction' k with k ih <;> intro b c f
  · ring_nf; finish
  · rw [show b + (k + 1) = (b + k) + 1 from by ring]
    step fm; step fm; step fm
    rw [show b + k + 2 + 2 = (b + 4) + k from by ring,
        show c + 1 + (k + 1) = (c + 1) + 1 + k from by ring,
        show b + 4 * (k + 1) = (b + 4) + 4 * k from by ring]
    exact ih (b + 4) (c + 1) f

private theorem tuple_eq {a₁ a₂ b₁ b₂ c₁ c₂ d₁ d₂ e₁ e₂ f₁ f₂ : ℕ}
    (ha : a₁ = a₂) (hb : b₁ = b₂) (hc : c₁ = c₂) (hd : d₁ = d₂) (he : e₁ = e₂) (hf : f₁ = f₂) :
    (⟨a₁, b₁, c₁, d₁, e₁, f₁⟩ : Q) = ⟨a₂, b₂, c₂, d₂, e₂, f₂⟩ := by
  subst ha; subst hb; subst hc; subst hd; subst he; subst hf; rfl

theorem phase1 (n f : ℕ) :
    ⟨(0 : ℕ), 2 * f + 2 * n + 4, n + 2, 0, 0, f⟩ [fm]⊢*
    ⟨0, 2 * f + 2 * n + 4, 0, 0, n + 2, f⟩ := by
  have h := r3_chain (n + 2) (2 * f + 2 * n + 4) 0 0 f
  simp only [Nat.zero_add] at h
  exact h

theorem phase2 (n f : ℕ) :
    ⟨(0 : ℕ), 2 * f + 2 * n + 4, 0, 0, n + 2, f⟩ [fm]⊢*
    ⟨0, 2 * f + n + 2, 0, n + 2, 0, f + n + 2⟩ := by
  have h := r4_chain (n + 2) (2 * f + n + 2) 0 f
  simp only [Nat.zero_add] at h
  rw [show 2 * f + 2 * n + 4 = (2 * f + n + 2) + (n + 2) from by ring,
      show f + n + 2 = f + (n + 2) from by ring]
  exact h

theorem phase3 (n f : ℕ) :
    ⟨(0 : ℕ), 2 * f + n + 2, 0, n + 2, 0, f + n + 2⟩ [fm]⊢
    ⟨0, 2 * f + n + 2, 1, n + 2, 0, f + n + 1⟩ := by
  rw [show f + n + 2 = (f + n + 1) + 1 from by ring]
  show fm ⟨0, 2 * f + n + 2, 0, n + 2, 0, (f + n + 1) + 1⟩ =
    some ⟨0, 2 * f + n + 2, 0 + 1, n + 2, 0, f + n + 1⟩
  unfold fm; simp only

theorem phase4 (n f : ℕ) :
    ⟨(0 : ℕ), 2 * f + n + 2, 1, n + 2, 0, f + n + 1⟩ [fm]⊢*
    ⟨0, 2 * f + 4 * n + 8, n + 3, 0, 0, f + n + 1⟩ := by
  have h := r2r1r1_chain (n + 2) (2 * f) 0 (f + n + 1)
  simp only [Nat.zero_add] at h
  have hsrc : (⟨0, 2 * f + (n + 2), 1, n + 2, 0, f + n + 1⟩ : Q) =
      ⟨0, 2 * f + n + 2, 1, n + 2, 0, f + n + 1⟩ :=
    tuple_eq rfl (by ring) rfl rfl rfl rfl
  have htgt : (⟨0, 2 * f + 4 * (n + 2), 1 + (n + 2), 0, 0, f + n + 1⟩ : Q) =
      ⟨0, 2 * f + 4 * n + 8, n + 3, 0, 0, f + n + 1⟩ :=
    tuple_eq rfl (by ring) (by ring) rfl rfl rfl
  rw [← hsrc, ← htgt]
  exact h

theorem main_trans (n f : ℕ) :
    ⟨(0 : ℕ), 2 * f + 2 * n + 4, n + 2, 0, 0, f⟩ [fm]⊢⁺
    ⟨0, 2 * (f + n + 1) + 2 * (n + 1) + 4, n + 3, 0, 0, f + n + 1⟩ := by
  have hp4 : ⟨(0 : ℕ), 2 * f + n + 2, 1, n + 2, 0, f + n + 1⟩ [fm]⊢*
      ⟨0, 2 * (f + n + 1) + 2 * (n + 1) + 4, n + 3, 0, 0, f + n + 1⟩ := by
    have h := phase4 n f
    have htgt : (⟨0, 2 * f + 4 * n + 8, n + 3, 0, 0, f + n + 1⟩ : Q) =
        ⟨0, 2 * (f + n + 1) + 2 * (n + 1) + 4, n + 3, 0, 0, f + n + 1⟩ :=
      tuple_eq rfl (by ring) rfl rfl rfl rfl
    rw [htgt] at h
    exact h
  exact stepPlus_stepStar_stepPlus
    (stepStar_stepPlus_stepPlus (phase1 n f) (stepStar_step_stepPlus (phase2 n f) (phase3 n f)))
    hp4

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨0, 4, 2, 0, 0, 0⟩) (by execute fm 7)
  apply progress_nonhalt_simple (fm := fm) (A := ℕ × ℕ)
    (fun ⟨n, f⟩ ↦ ⟨0, 2 * f + 2 * n + 4, n + 2, 0, 0, f⟩) ⟨0, 0⟩
  intro ⟨n, f⟩
  exact ⟨⟨n + 1, f + n + 1⟩, main_trans n f⟩

end Sz22_2003_unofficial_1040
