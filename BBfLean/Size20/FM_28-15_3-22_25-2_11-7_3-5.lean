import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# [28/15, 3/22, 25/2, 11/7, 3/5]

Vector representation:
```
 2 -1 -1  1  0
-1  1  0  0 -1
-1  0  2  0  0
 0  0  0 -1  1
 0  1 -1  0  0
```

This is a sz20 machine that doesn't halt.
-/

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a, b+1, c+1, d, e⟩ => some ⟨a+2, b, c, d+1, e⟩
  | ⟨a+1, b, c, d, e+1⟩ => some ⟨a, b+1, c, d, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b, c+2, d, e⟩
  | ⟨a, b, c, d+1, e⟩ => some ⟨a, b, c, d, e+1⟩
  | ⟨a, b, c+1, d, e⟩ => some ⟨a, b+1, c, d, e⟩
  | _ => none

theorem acd_to_cd : ⟨a, 0, c, d, 0⟩ [fm]⊢* ⟨0, 0, c+2*a, d, 0⟩ := by
  have many_step : ∀ k a c d, ⟨a+k, 0, c, d, 0⟩ [fm]⊢* ⟨a, 0, c+2*k, d, 0⟩ := by
    intro k; induction' k with k h <;> intro a c d
    · exists 0
    rw [← Nat.add_assoc]
    step fm
    apply stepStar_trans (h _ _ _)
    ring_nf; finish
  have h := many_step a 0 c d
  rw [zero_add] at h
  exact h

theorem cd_to_ce : ⟨0, 0, c, d, 0⟩ [fm]⊢* ⟨0, 0, c, 0, d⟩ := by
  have many_step : ∀ k c d e, ⟨0, 0, c, d+k, e⟩ [fm]⊢* ⟨0, 0, c, d, e+k⟩ := by
    intro k; induction' k with k h <;> intro c d e
    · exists 0
    rw [← Nat.add_assoc]
    step fm
    apply stepStar_trans (h _ _ _)
    ring_nf; finish
  have h := many_step d c 0 0
  rw [zero_add] at h
  exact h

theorem ce_to_acd : ⟨0, 0, c+e+2, 0, e⟩ [fm]⊢⁺ ⟨e+2, 0, c, e+1, 0⟩ := by
  step fm
  have many_step : ∀ k a c d e, ⟨a, 1, c+k, d, e+k⟩ [fm]⊢* ⟨a+k, 1, c, d+k, e⟩ := by
    intro k; induction' k with k h <;> intro a c d e
    · exists 0
    rw [← Nat.add_assoc, ← Nat.add_assoc]
    step fm; step fm
    apply stepStar_trans (h _ _ _ _)
    ring_nf; finish
  rw [Nat.add_right_comm]
  nth_rw 2 [← Nat.zero_add e]
  apply stepStar_trans (many_step e _ _ _ _)
  step fm
  ring_nf; finish

theorem acd_to_acd : ⟨d+1, 0, c, d, 0⟩ [fm]⊢⁺ ⟨d+2, 0, c+d, d+1, 0⟩ := by
  apply stepStar_stepPlus_stepPlus acd_to_cd
  apply stepStar_stepPlus_stepPlus cd_to_ce
  rw [(by ring : c + 2 * (d + 1) = c + d + d + 2)]
  apply stepPlus_stepStar_stepPlus ce_to_acd
  ring_nf; finish

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨1, 0, 0, 0, 0⟩) (by finish)
  apply progress_nonhalt_simple (fm := fm) (A := ℕ × ℕ) (fun ⟨c, d⟩ ↦ ⟨d+1, 0, c, d, 0⟩) ⟨0, 0⟩
  intro ⟨c, d⟩
  exists ⟨c+d, d+1⟩
  apply acd_to_acd
