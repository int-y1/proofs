import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #1110: [5/6, 4/35, 539/2, 3/7, 245/11]

Vector representation:
```
-1 -1  1  0  0
 2  0 -1 -1  0
-1  0  0  2  1
 0  1  0 -1  0
 0  0  1  2 -1
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_1110

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a+1, b+1, c, d, e⟩ => some ⟨a, b, c+1, d, e⟩
  | ⟨a, b, c+1, d+1, e⟩ => some ⟨a+2, b, c, d, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b, c, d+2, e+1⟩
  | ⟨a, b, c, d+1, e⟩ => some ⟨a, b+1, c, d, e⟩
  | ⟨a, b, c, d, e+1⟩ => some ⟨a, b, c+1, d+2, e⟩
  | _ => none

theorem d_to_b : ∀ k, ⟨0, b, 0, d + k, e⟩ [fm]⊢* ⟨0, b + k, 0, d, e⟩ := by
  intro k; induction' k with k ih generalizing b d
  · exists 0
  · rw [Nat.add_succ d k]; step fm
    apply stepStar_trans (ih (b := b + 1)); ring_nf; finish

theorem tail_step : ⟨a + 1, 0, c + 2, 0, e⟩ [fm]⊢* ⟨a + 4, 0, c, 0, e + 1⟩ := by
  step fm; step fm; step fm; ring_nf; finish

theorem tail_even : ∀ k, ⟨a + 1, 0, 2 * k, 0, e⟩ [fm]⊢* ⟨a + 3 * k + 1, 0, 0, 0, e + k⟩ := by
  intro k; induction' k with k ih generalizing a e
  · exists 0
  · rw [show 2 * (k + 1) = 2 * k + 2 from by ring]
    apply stepStar_trans (tail_step (a := a) (c := 2 * k) (e := e))
    rw [show a + 4 = (a + 3) + 1 from by ring]
    apply stepStar_trans (ih (a := a + 3) (e := e + 1)); ring_nf; finish

theorem tail_odd : ∀ k, ⟨a + 1, 0, 2 * k + 1, 0, e⟩ [fm]⊢*
    ⟨a + 3 * k + 2, 0, 0, 1, e + k + 1⟩ := by
  intro k; induction' k with k ih generalizing a e
  · step fm; step fm; ring_nf; finish
  · rw [show 2 * (k + 1) + 1 = (2 * k + 1) + 2 from by ring]
    apply stepStar_trans (tail_step (a := a) (c := 2 * k + 1) (e := e))
    rw [show a + 4 = (a + 3) + 1 from by ring]
    apply stepStar_trans (ih (a := a + 3) (e := e + 1)); ring_nf; finish

theorem chain_step :
    ⟨0, b + 4, c, 0, e + 1⟩ [fm]⊢* ⟨0, b, c + 3, 0, e⟩ := by
  step fm; step fm; step fm; step fm; step fm; step fm; step fm
  ring_nf; finish

theorem end_b0 : ⟨0, 0, c + 1, 0, e + 1⟩ [fm]⊢⁺ ⟨4, 0, c, 0, e⟩ := by
  step fm; step fm; step fm; ring_nf; finish

theorem end_b1 : ⟨0, 1, c, 0, e + 1⟩ [fm]⊢⁺ ⟨3, 0, c, 0, e⟩ := by
  step fm; step fm; step fm; step fm; ring_nf; finish

theorem end_b2 : ⟨0, 2, c, 0, e + 1⟩ [fm]⊢⁺ ⟨2, 0, c + 1, 0, e⟩ := by
  step fm; step fm; step fm; step fm; step fm; ring_nf; finish

theorem end_b3 : ⟨0, 3, c, 0, e + 1⟩ [fm]⊢⁺ ⟨4, 0, c, 0, e + 1⟩ := by
  step fm; step fm; step fm; step fm; step fm; step fm; step fm; step fm; step fm
  ring_nf; finish

theorem case_d0 : ⟨0, 0, 0, 0, e + 1⟩ [fm]⊢⁺ ⟨2, 0, 0, 1, e⟩ := by
  step fm; step fm; ring_nf; finish

theorem case_d1 : ⟨0, 0, 0, 1, e + 1⟩ [fm]⊢⁺ ⟨3, 0, 0, 0, e⟩ := by
  execute fm 5

-- Helper: dispatch tail based on parity of c, producing state with a' >= 1
private theorem tail_dispatch (A : ℕ) (hA : A ≥ 1) (c e : ℕ) :
    ∃ a' d' e', a' ≥ 1 ∧ 2 * a' + 4 * e' ≥ d' + 2 ∧
    ⟨A, 0, c, 0, e⟩ [fm]⊢* ⟨a', 0, 0, d', e'⟩ := by
  obtain ⟨A', rfl⟩ : ∃ A', A = A' + 1 := ⟨A - 1, by omega⟩
  rcases Nat.even_or_odd c with ⟨K, hK⟩ | ⟨K, hK⟩
  · rw [show K + K = 2 * K from by ring] at hK; subst hK
    exact ⟨A' + 3 * K + 1, 0, e + K, by omega, by omega, tail_even K⟩
  · subst hK
    exact ⟨A' + 3 * K + 2, 1, e + K + 1, by omega, by omega, tail_odd K⟩

-- Middle phase: from (0, b, c, 0, e+1) with b+c >= 1 and 4*(e+1) >= b+2
-- reach (a', 0, 0, d', e') with a' >= 1 and invariant maintained.
theorem middle_phase : ∀ b, ∀ c e, b + c ≥ 1 → 4 * (e + 1) ≥ b + 2 →
    ∃ a' d' e', a' ≥ 1 ∧ 2 * a' + 4 * e' ≥ d' + 2 ∧
    ⟨0, b, c, 0, e + 1⟩ [fm]⊢⁺ ⟨a', 0, 0, d', e'⟩ := by
  intro b; induction' b using Nat.strongRecOn with b IH
  intro c e hbc hbe
  rcases b with _ | _ | _ | _ | b
  · -- b = 0, c >= 1
    rcases c with _ | c
    · omega
    have ⟨a', d', e', ha', hinv, htail⟩ := tail_dispatch 4 (by omega) c e
    exact ⟨a', d', e', ha', hinv, stepPlus_stepStar_stepPlus end_b0 htail⟩
  · -- b = 1
    have ⟨a', d', e', ha', hinv, htail⟩ := tail_dispatch 3 (by omega) c e
    exact ⟨a', d', e', ha', hinv, stepPlus_stepStar_stepPlus end_b1 htail⟩
  · -- b = 2
    have ⟨a', d', e', ha', hinv, htail⟩ := tail_dispatch 2 (by omega) (c + 1) e
    exact ⟨a', d', e', ha', hinv, stepPlus_stepStar_stepPlus end_b2 htail⟩
  · -- b = 3
    have ⟨a', d', e', ha', hinv, htail⟩ := tail_dispatch 4 (by omega) c (e + 1)
    refine ⟨a', d', e', ha', hinv, stepPlus_stepStar_stepPlus end_b3 ?_⟩
    exact htail
  · -- b = b + 4
    rw [show b + 1 + 1 + 1 + 1 = b + 4 from by ring]
    -- chain_step: (0, b+4, c, 0, e+1) →* (0, b, c+3, 0, e)
    -- Need e >= 1 for IH (e = e'+1). 4*(e+1) >= (b+4)+2 = b+6, so 4e+4 >= b+6, 4e >= b+2.
    -- For IH: need 4*((e-1)+1) >= b+2, i.e., 4*e >= b+2. We have 4*(e+1) >= b+6, so 4*e >= b+2. Good.
    -- Also need e-1+1 form, i.e., e >= 1. 4*e >= b+2 >= 2, so e >= 1.
    obtain ⟨e', rfl⟩ : ∃ e', e = e' + 1 := ⟨e - 1, by omega⟩
    have hchain : ⟨0, b + 4, c, 0, (e' + 1) + 1⟩ [fm]⊢* ⟨0, b, c + 3, 0, e' + 1⟩ := by
      rw [show (e' + 1) + 1 = e' + 1 + 1 from by ring]; exact chain_step
    have ⟨a', d', e'', ha', hinv, hstep⟩ := IH b (by omega) (c + 3) e' (by omega) (by omega)
    exact ⟨a', d', e'', ha', hinv, stepStar_stepPlus_stepPlus hchain hstep⟩

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨0, 0, 0, 2, 1⟩)
  · execute fm 1
  apply progress_nonhalt (fm := fm)
    (P := fun q ↦ ∃ a d e, q = ⟨a, 0, 0, d, e⟩ ∧ a + e ≥ 1 ∧ 2 * a + 4 * e ≥ d + 2)
  · intro c ⟨a, d, e, hq, hae, hinv⟩; subst hq
    rcases (show a ≥ 1 ∨ (a = 0 ∧ e ≥ 1) from by omega) with ha | ⟨rfl, he⟩
    · -- a >= 1: R3 step
      obtain ⟨a', rfl⟩ : ∃ a', a = a' + 1 := ⟨a - 1, by omega⟩
      exact ⟨⟨a', 0, 0, d + 2, e + 1⟩,
        ⟨a', d + 2, e + 1, rfl, by omega, by omega⟩,
        by (step fm; finish)⟩
    · -- a = 0, e >= 1
      obtain ⟨e', rfl⟩ : ∃ e', e = e' + 1 := ⟨e - 1, by omega⟩
      rcases d with _ | d
      · -- d = 0
        exact ⟨⟨2, 0, 0, 1, e'⟩, ⟨2, 1, e', rfl, by omega, by omega⟩, case_d0⟩
      · -- d >= 1: d_to_b then middle_phase
        have hdb : ⟨0, 0, 0, 0 + (d + 1), e' + 1⟩ [fm]⊢* ⟨0, 0 + (d + 1), 0, 0, e' + 1⟩ :=
          d_to_b (d + 1) (b := 0) (d := 0)
        simp only [Nat.zero_add] at hdb
        have ⟨a', d', e'', ha', hinv', hstep⟩ :=
          middle_phase (d + 1) 0 e' (by omega) (by omega)
        exact ⟨⟨a', 0, 0, d', e''⟩,
          ⟨a', d', e'', rfl, by omega, hinv'⟩,
          stepStar_stepPlus_stepPlus hdb hstep⟩
  · exact ⟨0, 2, 1, rfl, by omega, by omega⟩

end Sz22_2003_unofficial_1110
