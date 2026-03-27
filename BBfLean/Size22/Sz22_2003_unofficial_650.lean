import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #650: [35/6, 143/2, 8/55, 3/7, 14/13]

Vector representation:
```
-1 -1  1  1  0  0
-1  0  0  0  1  1
 3  0 -1  0 -1  0
 0  1  0 -1  0  0
 1  0  0  1  0 -1
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_650

def Q := ℕ × ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a+1, b+1, c, d, e, f⟩ => some ⟨a, b, c+1, d+1, e, f⟩
  | ⟨a+1, b, c, d, e, f⟩ => some ⟨a, b, c, d, e+1, f+1⟩
  | ⟨a, b, c+1, d, e+1, f⟩ => some ⟨a+3, b, c, d, e, f⟩
  | ⟨a, b, c, d+1, e, f⟩ => some ⟨a, b+1, c, d, e, f⟩
  | ⟨a, b, c, d, e, f+1⟩ => some ⟨a+1, b, c, d+1, e, f⟩
  | _ => none

-- R4 repeated: transfer d to b
theorem d_to_b : ∀ k, ∀ b d e f, ⟨0, b, 0, d + k, e, f⟩ [fm]⊢* ⟨0, b + k, 0, d, e, f⟩ := by
  intro k; induction' k with k ih <;> intro b d e f
  · exists 0
  rw [show d + (k + 1) = (d + k) + 1 from by ring]
  step fm
  apply stepStar_trans (ih _ _ _ _)
  ring_nf; finish

-- R3/R2 loop: c rounds of R3 then R2*3
theorem r3r2_loop : ∀ k, ∀ c d e f, ⟨0, 0, c + k, d, e + k, f⟩ [fm]⊢* ⟨0, 0, c, d, e + 3 * k, f + 3 * k⟩ := by
  intro k; induction' k with k ih <;> intro c d e f
  · exists 0
  rw [show c + (k + 1) = (c + k) + 1 from by ring,
      show e + (k + 1) = (e + k) + 1 from by ring]
  step fm; step fm; step fm; step fm
  rw [show e + k + 1 + 1 + 1 = (e + 3) + k from by ring]
  apply stepStar_trans (ih c d (e + 3) (f + 3))
  ring_nf; finish

-- Helper to close stepStar goals where both sides are equal up to omega
private theorem stepStar_refl_omega {a b c d e f a' b' c' d' e' f' : ℕ}
    (h1 : a = a') (h2 : b = b') (h3 : c = c') (h4 : d = d') (h5 : e = e') (h6 : f = f') :
    (⟨a, b, c, d, e, f⟩ : Q) [fm]⊢* ⟨a', b', c', d', e', f'⟩ := by
  subst h1; subst h2; subst h3; subst h4; subst h5; subst h6; exists 0

-- Inner phase: from (3, B, C, D, E, F) to (0, 0, 0, D+B, E+B+2*C+3, F+2*B+3*C+3)
-- Requires E >= B + C
theorem inner_phase : ∀ B, ∀ C D E F, E ≥ B + C →
    ⟨3, B, C, D, E, F⟩ [fm]⊢* ⟨0, 0, 0, D + B, E + B + 2 * C + 3, F + 2 * B + 3 * C + 3⟩ := by
  intro B; induction' B using Nat.strongRecOn with B ih; intro C D E F hE
  rcases B with _ | _ | _ | B
  · -- B = 0: R2*3 then r3r2_loop C
    step fm; step fm; step fm
    obtain ⟨E', rfl⟩ : ∃ E', E = E' + C := ⟨E - C, by omega⟩
    rw [show E' + C + 1 + 1 + 1 = (E' + 3) + C from by ring,
        show F + 1 + 1 + 1 = F + 3 from by ring]
    have h := r3r2_loop C 0 D (E' + 3) (F + 3)
    simp only [Nat.zero_add] at h
    apply stepStar_trans h
    apply stepStar_refl_omega <;> ring
  · -- B = 1: R1, R2*2, then r3r2_loop (C+1)
    step fm; step fm; step fm
    obtain ⟨E', rfl⟩ : ∃ E', E = E' + (C + 1) := ⟨E - C - 1, by omega⟩
    rw [show E' + (C + 1) + 1 + 1 = (E' + 2) + (C + 1) from by ring,
        show F + 1 + 1 = F + 2 from by ring]
    have h := r3r2_loop (C + 1) 0 (D + 1) (E' + 2) (F + 2)
    simp only [Nat.zero_add] at h
    apply stepStar_trans h
    apply stepStar_refl_omega <;> ring
  · -- B = 2: R1*2, R2, then r3r2_loop (C+2)
    step fm; step fm; step fm
    obtain ⟨E', rfl⟩ : ∃ E', E = E' + (C + 2) := ⟨E - C - 2, by omega⟩
    rw [show E' + (C + 2) + 1 = (E' + 1) + (C + 2) from by ring,
        show F + 1 = F + 1 from rfl]
    have h := r3r2_loop (C + 2) 0 (D + 2) (E' + 1) (F + 1)
    simp only [Nat.zero_add] at h
    apply stepStar_trans h
    apply stepStar_refl_omega <;> ring
  · -- B = B' + 3: R1*3, R3, then recurse
    rw [show (3 : ℕ) = 2 + 1 from rfl]
    step fm
    rw [show (2 : ℕ) = 1 + 1 from rfl]
    step fm; step fm
    rw [show C + 1 + 1 + 1 = (C + 2) + 1 from by ring]
    obtain ⟨E', rfl⟩ : ∃ E', E = E' + 1 := ⟨E - 1, by omega⟩
    step fm
    apply stepStar_trans (ih B (by omega) (C + 2) (D + 3) E' F (by omega))
    apply stepStar_refl_omega <;> omega

-- Main transition
theorem main_trans (hE : e ≥ d + 2) (hF : f ≥ 1) :
    ⟨0, 0, 0, d + 1, e, f⟩ [fm]⊢⁺ ⟨0, 0, 0, d + 2, e + d + 2, f + 2 * (d + 1)⟩ := by
  -- Phase 1: R4*(d+1)
  rw [show d + 1 = 0 + (d + 1) from by ring]
  apply stepStar_stepPlus_stepPlus (d_to_b (d + 1) 0 0 e f)
  simp only [Nat.zero_add]
  -- Phase 2: R5, R1, R3
  obtain ⟨f', rfl⟩ : ∃ f', f = f' + 1 := ⟨f - 1, by omega⟩
  obtain ⟨e', rfl⟩ : ∃ e', e = e' + 1 := ⟨e - 1, by omega⟩
  step fm; step fm; step fm
  -- State: (3, d, 0, 2, e', f'), goal is ⊢*
  -- Phase 3: inner_phase
  have h := inner_phase d 0 2 e' f' (by omega)
  simp only [Nat.mul_zero, Nat.add_zero] at h
  apply stepStar_trans h
  apply stepStar_refl_omega <;> omega

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨0, 0, 0, 1, 2, 1⟩) (by execute fm 3)
  apply progress_nonhalt (fm := fm)
    (P := fun q ↦ ∃ d e f, q = ⟨0, 0, 0, d + 1, e, f⟩ ∧ e ≥ d + 2 ∧ f ≥ 1)
  · intro c ⟨d, e, f, hq, hE, hF⟩; subst hq
    exact ⟨⟨0, 0, 0, d + 2, e + d + 2, f + 2 * (d + 1)⟩,
           ⟨d + 1, e + d + 2, f + 2 * (d + 1), rfl, by omega, by omega⟩,
           main_trans hE hF⟩
  · exact ⟨0, 2, 1, rfl, by omega, by omega⟩
