import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #1318: [63/10, 143/2, 4/33, 5/7, 15/13]

Vector representation:
```
-1  2 -1  1  0  0
-1  0  0  0  1  1
 2 -1  0  0 -1  0
 0  0  1 -1  0  0
 0  1  1  0  0 -1
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_1318

def Q := ℕ × ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a+1, b, c+1, d, e, f⟩ => some ⟨a, b+2, c, d+1, e, f⟩
  | ⟨a+1, b, c, d, e, f⟩ => some ⟨a, b, c, d, e+1, f+1⟩
  | ⟨a, b+1, c, d, e+1, f⟩ => some ⟨a+2, b, c, d, e, f⟩
  | ⟨a, b, c, d+1, e, f⟩ => some ⟨a, b, c+1, d, e, f⟩
  | ⟨a, b, c, d, e, f+1⟩ => some ⟨a, b+1, c+1, d, e, f⟩
  | _ => none

theorem d_to_c : ∀ D c e f, ⟨(0 : ℕ), (0 : ℕ), c, D, e, f⟩ [fm]⊢*
    ⟨(0 : ℕ), (0 : ℕ), c + D, 0, e, f⟩ := by
  intro D; induction' D with D ih
  · intro c e f; exists 0
  · intro c e f
    step fm
    apply stepStar_trans (ih (c + 1) e f)
    ring_nf; finish

theorem r3r1r1_chain : ∀ k B C D E F, ⟨(0 : ℕ), B + 1, C + 2 * k, D, E + k, F⟩ [fm]⊢*
    ⟨(0 : ℕ), B + 3 * k + 1, C, D + 2 * k, E, F⟩ := by
  intro k; induction' k with k ih
  · intro B C D E F; simp; exists 0
  · intro B C D E F
    rw [show C + 2 * (k + 1) = (C + 2) + 2 * k from by ring,
        show E + (k + 1) = (E + 1) + k from by ring]
    apply stepStar_trans (ih B (C + 2) D (E + 1) F)
    rw [show B + 3 * k + 1 = (B + 3 * k) + 1 from by ring]
    step fm; step fm; step fm
    rw [show B + 3 * k + 4 = B + 3 * (k + 1) + 1 from by ring,
        show D + 2 * k + 2 = D + 2 * (k + 1) from by ring]
    finish

theorem r3r2r2_chain : ∀ k D E F, ⟨(0 : ℕ), k, (0 : ℕ), D, E + 1, F⟩ [fm]⊢*
    ⟨(0 : ℕ), (0 : ℕ), (0 : ℕ), D, E + k + 1, F + 2 * k⟩ := by
  intro k; induction' k with k ih
  · intro D E F; simp; exists 0
  · intro D E F
    rw [show (k + 1 : ℕ) = k + 1 from rfl]
    step fm; step fm; step fm
    rw [show E + 2 = (E + 1) + 1 from by ring]
    apply stepStar_trans (ih D (E + 1) (F + 2))
    rw [show E + 1 + k + 1 = E + (k + 1) + 1 from by ring,
        show F + 2 + 2 * k = F + 2 * (k + 1) from by ring]
    finish

theorem c1_handle : ∀ B D E F, ⟨(0 : ℕ), B + 1, 1, D, E + 1, F⟩ [fm]⊢*
    ⟨(0 : ℕ), B + 2, (0 : ℕ), D + 1, E + 1, F + 1⟩ := by
  intro B D E F
  step fm; step fm; step fm; finish

theorem transition_odd (m : ℕ) (E F : ℕ) :
    ⟨(0 : ℕ), (0 : ℕ), 0, 2 * m + 1, E + m + 2, F + 1⟩ [fm]⊢⁺
    ⟨(0 : ℕ), (0 : ℕ), 0, 2 * m + 2, E + 3 * m + 5, F + 6 * m + 8⟩ := by
  apply stepStar_stepPlus_stepPlus (d_to_c (2 * m + 1) 0 (E + m + 2) (F + 1))
  rw [show 0 + (2 * m + 1) = 2 * m + 1 from by ring]
  step fm
  rw [show 2 * m + 1 + 1 = (2 * m) + 2 from by ring,
      show E + m + 2 = (E + m + 1) + 1 from by ring]
  step fm
  step fm; step fm
  rw [show (4 : ℕ) = 3 + 1 from by ring,
      show 2 * m = 0 + 2 * m from by ring,
      show E + m + 1 = (E + 1) + m from by ring]
  apply stepStar_trans (r3r1r1_chain m 3 0 2 (E + 1) F)
  rw [show 3 + 3 * m + 1 = 3 * m + 4 from by ring,
      show 2 + 2 * m = 2 * m + 2 from by ring]
  apply stepStar_trans (r3r2r2_chain (3 * m + 4) (2 * m + 2) E F)
  ring_nf; finish

theorem transition_even (m : ℕ) (E F : ℕ) :
    ⟨(0 : ℕ), (0 : ℕ), 0, 2 * m + 2, E + m + 2, F + 1⟩ [fm]⊢⁺
    ⟨(0 : ℕ), (0 : ℕ), 0, 2 * m + 3, E + 3 * m + 6, F + 6 * m + 11⟩ := by
  apply stepStar_stepPlus_stepPlus (d_to_c (2 * m + 2) 0 (E + m + 2) (F + 1))
  rw [show 0 + (2 * m + 2) = 2 * m + 2 from by ring]
  step fm
  rw [show 2 * m + 2 + 1 = (2 * m + 1) + 2 from by ring,
      show E + m + 2 = (E + m + 1) + 1 from by ring]
  step fm
  step fm; step fm
  rw [show (4 : ℕ) = 3 + 1 from by ring,
      show 2 * m + 1 = 1 + 2 * m from by ring,
      show E + m + 1 = (E + 1) + m from by ring]
  apply stepStar_trans (r3r1r1_chain m 3 1 2 (E + 1) F)
  rw [show 3 + 3 * m + 1 = (3 * m + 3) + 1 from by ring,
      show 2 + 2 * m = 2 * m + 2 from by ring]
  apply stepStar_trans (c1_handle (3 * m + 3) (2 * m + 2) E F)
  rw [show 3 * m + 3 + 2 = 3 * m + 5 from by ring,
      show 2 * m + 2 + 1 = 2 * m + 3 from by ring]
  apply stepStar_trans (r3r2r2_chain (3 * m + 5) (2 * m + 3) E (F + 1))
  ring_nf; finish

theorem main_transition (d e f : ℕ) (hd : d ≥ 1) (he : 2 * e ≥ d + 3) (hf : f ≥ 1) :
    ⟨(0 : ℕ), (0 : ℕ), 0, d, e, f⟩ [fm]⊢⁺
    ⟨(0 : ℕ), (0 : ℕ), 0, d + 1, e + d + 2, f + 3 * d + 4⟩ := by
  obtain ⟨F, rfl⟩ : ∃ F, f = F + 1 := ⟨f - 1, by omega⟩
  rcases Nat.even_or_odd d with ⟨K, hK⟩ | ⟨K, hK⟩
  · rw [show K + K = 2 * K from by ring] at hK
    obtain ⟨m, rfl⟩ : ∃ m, K = m + 1 := ⟨K - 1, by omega⟩
    subst hK
    obtain ⟨E, rfl⟩ : ∃ E, e = E + m + 2 := ⟨e - m - 2, by omega⟩
    have h := transition_even m E F
    rw [show 2 * (m + 1) = 2 * m + 2 from by ring,
        show 2 * m + 2 + 1 = 2 * m + 3 from by ring,
        show (E + m + 2) + (2 * m + 2) + 2 = E + 3 * m + 6 from by ring,
        show (F + 1) + 3 * (2 * m + 2) + 4 = F + 6 * m + 11 from by ring]
    exact h
  · subst hK
    obtain ⟨E, rfl⟩ : ∃ E, e = E + K + 2 := ⟨e - K - 2, by omega⟩
    have h := transition_odd K E F
    rw [show 2 * K + 1 + 1 = 2 * K + 2 from by ring,
        show (E + K + 2) + (2 * K + 1) + 2 = E + 3 * K + 5 from by ring,
        show (F + 1) + 3 * (2 * K + 1) + 4 = F + 6 * K + 8 from by ring]
    exact h

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨0, 0, 0, 1, 3, 5⟩) (by execute fm 11)
  apply progress_nonhalt (fm := fm)
    (P := fun q ↦ ∃ d e f, q = ⟨0, 0, 0, d, e, f⟩ ∧ d ≥ 1 ∧ 2 * e ≥ d + 3 ∧ f ≥ 1)
  · intro c ⟨d, e, f, hq, hd, he, hf⟩; subst hq
    refine ⟨⟨0, 0, 0, d + 1, e + d + 2, f + 3 * d + 4⟩,
      ⟨d + 1, e + d + 2, f + 3 * d + 4, rfl, ?_, ?_, ?_⟩,
      main_transition d e f hd he hf⟩
    · omega
    · omega
    · omega
  · exact ⟨1, 3, 5, rfl, by omega, by omega, by omega⟩

end Sz22_2003_unofficial_1318
