import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #1861: [9/35, 22/5, 25/33, 7/11, 55/2]

Vector representation:
```
 0  2 -1 -1  0
 1  0 -1  0  1
 0 -1  2  0 -1
 0  0  0  1 -1
-1  0  1  0  1
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_1861

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a, b, c+1, d+1, e⟩ => some ⟨a, b+2, c, d, e⟩
  | ⟨a, b, c+1, d, e⟩ => some ⟨a+1, b, c, d, e+1⟩
  | ⟨a, b+1, c, d, e+1⟩ => some ⟨a, b, c+2, d, e⟩
  | ⟨a, b, c, d, e+1⟩ => some ⟨a, b, c, d+1, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b, c+1, d, e+1⟩
  | _ => none

theorem e_to_d : ∀ k, ⟨a, 0, 0, d, e + k⟩ [fm]⊢* ⟨a, 0, 0, d + k, e⟩ := by
  intro k; induction' k with k ih generalizing d e
  · exists 0
  · rw [show e + (k + 1) = (e + k) + 1 from by ring]
    step fm
    apply stepStar_trans (ih (d := d + 1) (e := e))
    rw [show d + 1 + k = d + (k + 1) from by ring]; finish

theorem opening : ⟨a + 1, 0, 0, E + 2, 0⟩ [fm]⊢⁺ ⟨a, 1, 2, E + 1, 0⟩ := by
  step fm; step fm; step fm; finish

theorem inner_step : ⟨a + 1, b, 2, D + 3, 0⟩ [fm]⊢⁺ ⟨a, b + 5, 2, D, 0⟩ := by
  step fm; step fm; step fm; step fm; step fm; finish

theorem inner_loop : ∀ k, ⟨a + k, b, 2, D + 3 * k, 0⟩ [fm]⊢* ⟨a, b + 5 * k, 2, D, 0⟩ := by
  intro k; induction' k with k ih generalizing a b D
  · exists 0
  · rw [show a + (k + 1) = (a + 1) + k from by ring,
        show D + 3 * (k + 1) = (D + 3) + 3 * k from by ring]
    apply stepStar_trans (ih (a := a + 1) (b := b) (D := D + 3))
    have : (a + 1, b + 5 * k, 2, D + 3, 0) [fm]⊢⁺ (a, b + 5 * k + 5, 2, D, 0) :=
      inner_step (a := a) (b := b + 5 * k) (D := D)
    rw [show b + 5 * (k + 1) = b + 5 * k + 5 from by ring]
    exact stepPlus_stepStar this

theorem d1_ending : ⟨a, b, 2, 1, 0⟩ [fm]⊢⁺ ⟨a + 1, b + 1, 2, 0, 0⟩ := by
  step fm; step fm; step fm; finish

theorem d2_ending : ⟨a + 1, b, 2, 2, 0⟩ [fm]⊢⁺ ⟨a + 1, b + 3, 2, 0, 1⟩ := by
  step fm; step fm; step fm; step fm; step fm; finish

theorem b_drain_round : ⟨a, b + 1, 2, 0, e⟩ [fm]⊢⁺ ⟨a + 2, b, 2, 0, e + 1⟩ := by
  step fm; step fm; step fm; finish

theorem b_drain_loop : ∀ B, ⟨a, B, 2, 0, e⟩ [fm]⊢* ⟨a + 2 * B, 0, 2, 0, e + B⟩ := by
  intro B; induction' B with B ih generalizing a e
  · exists 0
  · apply stepStar_trans (stepPlus_stepStar (b_drain_round (a := a) (b := B) (e := e)))
    rw [show a + 2 * (B + 1) = (a + 2) + 2 * B from by ring,
        show e + (B + 1) = (e + 1) + B from by ring]
    exact ih (a := a + 2) (e := e + 1)

theorem b_drain : ∀ B, ⟨a, B, 2, 0, e⟩ [fm]⊢* ⟨a + 2 * B + 2, 0, 0, 0, e + B + 2⟩ := by
  intro B; apply stepStar_trans (b_drain_loop B)
  step fm; step fm; ring_nf; finish

-- Main macro-step for E ≡ 2 mod 3 (E = 3n+2):
-- Phases: e_to_d, opening, inner_loop(n), d1_ending, b_drain
theorem case_mod2 :
    ⟨A + n + 1, 0, 0, 0, 3 * n + 2⟩ [fm]⊢⁺ ⟨A + 10 * n + 7, 0, 0, 0, 5 * n + 4⟩ := by
  rw [show (3 * n + 2 : ℕ) = 0 + (3 * n + 2) from by ring]
  apply stepStar_stepPlus_stepPlus
    (e_to_d (3 * n + 2) (a := A + n + 1) (d := 0) (e := 0))
  rw [show 0 + (3 * n + 2) = 3 * n + 2 from by ring,
      show A + n + 1 = (A + n) + 1 from by ring,
      show (3 * n + 2 : ℕ) = 3 * n + 2 from rfl]
  apply stepPlus_stepStar_stepPlus (opening (a := A + n) (E := 3 * n))
  rw [show 3 * n + 1 = 1 + 3 * n from by ring]
  apply stepStar_trans (inner_loop n (a := A) (b := 1) (D := 1))
  apply stepStar_trans (stepPlus_stepStar (d1_ending (a := A) (b := 1 + 5 * n)))
  rw [show 1 + 5 * n + 1 = 5 * n + 2 from by ring]
  apply stepStar_trans (b_drain (5 * n + 2) (a := A + 1) (e := 0))
  ring_nf; finish

-- Main macro-step for E ≡ 1 mod 3 (E = 3n+4):
-- Phases: e_to_d, opening, inner_loop(n+1), b_drain
theorem case_mod1 :
    ⟨A + n + 2, 0, 0, 0, 3 * n + 4⟩ [fm]⊢⁺ ⟨A + 10 * n + 14, 0, 0, 0, 5 * n + 8⟩ := by
  rw [show (3 * n + 4 : ℕ) = 0 + (3 * n + 4) from by ring]
  apply stepStar_stepPlus_stepPlus
    (e_to_d (3 * n + 4) (a := A + n + 2) (d := 0) (e := 0))
  rw [show 0 + (3 * n + 4) = (3 * n + 2) + 2 from by ring,
      show A + n + 2 = (A + n + 1) + 1 from by ring]
  apply stepPlus_stepStar_stepPlus (opening (a := A + n + 1) (E := 3 * n + 2))
  rw [show 3 * n + 2 + 1 = 0 + 3 * (n + 1) from by ring,
      show A + n + 1 = A + (n + 1) from by ring]
  apply stepStar_trans (inner_loop (n + 1) (a := A) (b := 1) (D := 0))
  rw [show 1 + 5 * (n + 1) = 5 * n + 6 from by ring]
  apply stepStar_trans (b_drain (5 * n + 6) (a := A) (e := 0))
  ring_nf; finish

-- Main macro-step for E ≡ 0 mod 3 (E = 3n+3):
-- Phases: e_to_d, opening, inner_loop(n), d2_ending, b_drain
theorem case_mod0 :
    ⟨A + n + 2, 0, 0, 0, 3 * n + 3⟩ [fm]⊢⁺ ⟨A + 10 * n + 11, 0, 0, 0, 5 * n + 7⟩ := by
  rw [show (3 * n + 3 : ℕ) = 0 + (3 * n + 3) from by ring]
  apply stepStar_stepPlus_stepPlus
    (e_to_d (3 * n + 3) (a := A + n + 2) (d := 0) (e := 0))
  rw [show 0 + (3 * n + 3) = (3 * n + 1) + 2 from by ring,
      show A + n + 2 = (A + n + 1) + 1 from by ring]
  apply stepPlus_stepStar_stepPlus (opening (a := A + n + 1) (E := 3 * n + 1))
  rw [show 3 * n + 1 + 1 = 2 + 3 * n from by ring,
      show A + n + 1 = (A + 1) + n from by ring]
  apply stepStar_trans (inner_loop n (a := A + 1) (b := 1) (D := 2))
  apply stepStar_trans (stepPlus_stepStar (d2_ending (a := A) (b := 1 + 5 * n)))
  rw [show 1 + 5 * n + 3 = 5 * n + 4 from by ring]
  apply stepStar_trans (b_drain (5 * n + 4) (a := A + 1) (e := 1))
  ring_nf; finish

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨7, 0, 0, 0, 4⟩) (by execute fm 18)
  apply progress_nonhalt (fm := fm)
    (P := fun q ↦ ∃ a e, q = ⟨a, 0, 0, 0, e⟩ ∧ e ≥ 2 ∧ a ≥ e)
  · intro c ⟨a, e, hq, he, ha⟩; subst hq
    obtain ⟨n, rfl | rfl | rfl⟩ : ∃ n, e = 3 * n ∨ e = 3 * n + 1 ∨ e = 3 * n + 2 :=
      ⟨e / 3, by omega⟩
    · -- e = 3n, e ≥ 2 means n ≥ 1
      obtain ⟨n, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
      obtain ⟨m, rfl⟩ : ∃ m, a = m + (n + 2) := ⟨a - (n + 2), by omega⟩
      exact ⟨⟨m + 10 * n + 11, 0, 0, 0, 5 * n + 7⟩,
        ⟨m + 10 * n + 11, 5 * n + 7, rfl, by omega, by omega⟩,
        show ⟨m + n + 2, 0, 0, 0, 3 * n + 3⟩ [fm]⊢⁺ _ from case_mod0⟩
    · -- e = 3n+1, e ≥ 2 means n ≥ 1
      obtain ⟨n, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
      obtain ⟨m, rfl⟩ : ∃ m, a = m + (n + 2) := ⟨a - (n + 2), by omega⟩
      exact ⟨⟨m + 10 * n + 14, 0, 0, 0, 5 * n + 8⟩,
        ⟨m + 10 * n + 14, 5 * n + 8, rfl, by omega, by omega⟩,
        show ⟨m + n + 2, 0, 0, 0, 3 * n + 4⟩ [fm]⊢⁺ _ from case_mod1⟩
    · -- e = 3n+2
      obtain ⟨m, rfl⟩ : ∃ m, a = m + (n + 1) := ⟨a - (n + 1), by omega⟩
      exact ⟨⟨m + 10 * n + 7, 0, 0, 0, 5 * n + 4⟩,
        ⟨m + 10 * n + 7, 5 * n + 4, rfl, by omega, by omega⟩,
        show ⟨m + n + 1, 0, 0, 0, 3 * n + 2⟩ [fm]⊢⁺ _ from case_mod2⟩
  · exact ⟨7, 4, rfl, by omega, by omega⟩

end Sz22_2003_unofficial_1861
