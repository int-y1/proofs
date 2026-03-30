import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #1089: [5/6, 297/35, 4/5, 7/11, 55/2]

Vector representation:
```
-1 -1  1  0  0
 0  3 -1 -1  1
 2  0 -1  0  0
 0  0  0  1 -1
-1  0  1  0  1
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_1089

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a+1, b+1, c, d, e⟩ => some ⟨a, b, c+1, d, e⟩
  | ⟨a, b, c+1, d+1, e⟩ => some ⟨a, b+3, c, d, e+1⟩
  | ⟨a, b, c+1, d, e⟩ => some ⟨a+2, b, c, d, e⟩
  | ⟨a, b, c, d, e+1⟩ => some ⟨a, b, c, d+1, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b, c+1, d, e+1⟩
  | _ => none

theorem r3_chain : ∀ c, ⟨a, 0, c, 0, e⟩ [fm]⊢* ⟨a + 2 * c, 0, 0, 0, e⟩ := by
  intro c; induction' c with c ih generalizing a
  · exists 0
  · step fm
    apply stepStar_trans (ih (a := a + 2))
    ring_nf; finish

theorem e_to_d : ∀ e, ⟨a, 0, 0, d, e⟩ [fm]⊢* ⟨a, 0, 0, d + e, 0⟩ := by
  intro e; induction' e with e ih generalizing a d
  · exists 0
  · step fm
    apply stepStar_trans (ih (a := a) (d := d + 1))
    ring_nf; finish

theorem r2_cascade :
    ∀ k, ⟨0, b, c + k, d + k, e⟩ [fm]⊢* ⟨0, b + 3 * k, c, d, e + k⟩ := by
  intro k; induction' k with k ih generalizing b c d e
  · simp; exists 0
  · rw [show c + (k + 1) = (c + k) + 1 from by ring,
        show d + (k + 1) = (d + k) + 1 from by ring]
    step fm
    apply stepStar_trans (ih (b := b + 3) (c := c) (d := d) (e := e + 1))
    ring_nf; finish

theorem r2_cascade' (hc : C ≥ D) :
    ⟨0, b, C, D, e⟩ [fm]⊢* ⟨0, b + 3 * D, C - D, 0, e + D⟩ := by
  have := r2_cascade D (b := b) (c := C - D) (d := 0) (e := e)
  simp only [Nat.sub_add_cancel hc, Nat.zero_add] at this
  exact this

theorem drain_b_d0 :
    ∀ B, ∀ A C E, (B ≥ 1 → A ≥ 1 ∨ C ≥ 1) →
      ⟨A, B, C, 0, E⟩ [fm]⊢* ⟨A + B + 2 * C, 0, 0, 0, E⟩ := by
  intro B; induction' B with B ih <;> intro A C E hpre
  · exact r3_chain C (a := A) (e := E)
  · rcases hpre (by omega) with hA | hC
    · obtain ⟨A', rfl⟩ : ∃ A', A = A' + 1 := ⟨A - 1, by omega⟩
      step fm
      apply stepStar_trans (ih A' (C + 1) E (by intro _; right; omega))
      ring_nf; finish
    · obtain ⟨C', rfl⟩ : ∃ C', C = C' + 1 := ⟨C - 1, by omega⟩
      rcases (show A ≥ 1 ∨ A = 0 from by omega) with hA | rfl
      · obtain ⟨A', rfl⟩ : ∃ A', A = A' + 1 := ⟨A - 1, by omega⟩
        step fm
        apply stepStar_trans (ih A' (C' + 2) E (by intro _; right; omega))
        ring_nf; finish
      · step fm
        step fm
        apply stepStar_trans (ih 1 (C' + 1) E (by intro _; left; omega))
        ring_nf; finish

theorem mixed_phase :
    ∀ D, ∀ A C E, C ≥ 1 → A + C ≥ D + 1 →
      ⟨A, 0, C, D, E⟩ [fm]⊢* ⟨A + 2 * C + D, 0, 0, 0, E + D⟩ := by
  intro D; induction' D using Nat.strongRecOn with D ih
  intro A C E hC hAC
  rcases D with _ | D
  · simp; exact r3_chain C (a := A) (e := E)
  · obtain ⟨C', rfl⟩ : ∃ C', C = C' + 1 := ⟨C - 1, by omega⟩
    rcases (show A ≥ 3 ∨ A = 2 ∨ A = 1 ∨ A = 0 from by omega) with hA | rfl | rfl | rfl
    · -- A >= 3: R2, R3, R5, R5 super-round then IH on D
      obtain ⟨A', rfl⟩ : ∃ A', A = A' + 3 := ⟨A - 3, by omega⟩
      step fm; step fm; step fm; step fm
      apply stepStar_trans (ih D (by omega) A' (C' + 3) (E + 1) (by omega) (by omega))
      ring_nf; finish
    · -- A = 2: R2, R1, R1 -> (0, 1, C'+1+1, D, E+1)
      step fm; step fm; step fm
      apply stepStar_trans (r2_cascade' (b := 1) (e := E + 1) (by omega))
      apply stepStar_trans (drain_b_d0 (1 + 3 * D) 0 (C' + 1 + 1 - D) (E + 1 + D)
        (by intro _; right; omega))
      rw [show 0 + (1 + 3 * D) + 2 * (C' + 1 + 1 - D) = 2 + 2 * (C' + 1) + (D + 1) from by omega]
      ring_nf; finish
    · -- A = 1: R2, R1 -> (0, 2, C'+1, D, E+1)
      step fm; step fm
      apply stepStar_trans (r2_cascade' (b := 2) (e := E + 1) (by omega))
      apply stepStar_trans (drain_b_d0 (2 + 3 * D) 0 (C' + 1 - D) (E + 1 + D)
        (by intro _; right; omega))
      rw [show 0 + (2 + 3 * D) + 2 * (C' + 1 - D) = 1 + 2 * (C' + 1) + (D + 1) from by omega]
      ring_nf; finish
    · -- A = 0: R2 -> (0, 3, C', D, E+1)
      step fm
      apply stepStar_trans (r2_cascade' (b := 3) (e := E + 1) (by omega))
      apply stepStar_trans (drain_b_d0 (3 + 3 * D) 0 (C' - D) (E + 1 + D)
        (by intro _; right; omega))
      rw [show 0 + (3 + 3 * D) + 2 * (C' - D) = 0 + 2 * (C' + 1) + (D + 1) from by omega]
      ring_nf; finish

theorem main_transition :
    ∀ d a, a ≥ d + 1 → ⟨a, 0, 0, d, 0⟩ [fm]⊢⁺ ⟨a + d + 1, 0, 0, d + 1, 0⟩ := by
  intro d a ha
  obtain ⟨a', rfl⟩ : ∃ a', a = a' + 1 := ⟨a - 1, by omega⟩
  step fm
  apply stepStar_trans (mixed_phase d a' 1 1 (by omega) (by omega))
  rw [show a' + 2 * 1 + d = a' + d + 2 from by ring,
      show 1 + d = d + 1 from by ring]
  apply stepStar_trans (e_to_d (d + 1) (a := a' + d + 2) (d := 0))
  ring_nf; finish

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨2, 0, 0, 1, 0⟩)
  · execute fm 3
  apply progress_nonhalt (fm := fm)
    (P := fun q ↦ ∃ a d, q = ⟨a, 0, 0, d, 0⟩ ∧ a ≥ d + 1)
  · intro c ⟨a, d, hq, ha⟩; subst hq
    exact ⟨⟨a + d + 1, 0, 0, d + 1, 0⟩,
      ⟨a + d + 1, d + 1, rfl, by omega⟩,
      main_transition d a ha⟩
  · exact ⟨2, 1, rfl, by omega⟩

end Sz22_2003_unofficial_1089
