import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# [4/15, 3/14, 275/2, 7/11, 3/5]

Vector representation:
```
 2 -1 -1  0  0
-1  1  0 -1  0
-1  0  2  0  1
 0  0  0  1 -1
 0  1 -1  0  0
```

This is a sz20 machine that doesn't halt.
-/

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a, b+1, c+1, d, e⟩ => some ⟨a+2, b, c, d, e⟩
  | ⟨a+1, b, c, d+1, e⟩ => some ⟨a, b+1, c, d, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b, c+2, d, e+1⟩
  | ⟨a, b, c, d, e+1⟩ => some ⟨a, b, c, d+1, e⟩
  | ⟨a, b, c+1, d, e⟩ => some ⟨a, b+1, c, d, e⟩
  | _ => none

theorem ac_to_ce : ⟨a, 0, c, 0, 0⟩ [fm]⊢* ⟨0, 0, c+2*a, 0, a⟩ := by
  have many_step : ∀ k a c e, ⟨a+k, 0, c, 0, e⟩ [fm]⊢* ⟨a, 0, c+2*k, 0, e+k⟩ := by
    intro k; induction' k with k h <;> intro a c e
    · exists 0
    rw [← Nat.add_assoc]
    step fm
    apply stepStar_trans (h _ _ _)
    ring_nf; finish
  have h := many_step a 0 c 0
  rw [zero_add] at h
  exact h

theorem ce_to_cd : ⟨0, 0, c, 0, e⟩ [fm]⊢* ⟨0, 0, c, e, 0⟩ := by
  have many_step : ∀ k c d e, ⟨0, 0, c, d, e+k⟩ [fm]⊢* ⟨0, 0, c, d+k, e⟩ := by
    intro k; induction' k with k h <;> intro c d e
    · exists 0
    rw [← Nat.add_assoc]
    step fm
    apply stepStar_trans (h _ _ _)
    ring_nf; finish
  have h := many_step e c 0 0
  rw [zero_add] at h
  exact h

theorem cd_to_ac : ⟨0, 0, c+d+2, d, 0⟩ [fm]⊢⁺ ⟨d+2, 0, c, 0, 0⟩ := by
  step fm
  have many_step : ∀ k a c d, ⟨a, 1, c+k, d+k, 0⟩ [fm]⊢* ⟨a+k, 1, c, d, 0⟩ := by
    intro k; induction' k with k h <;> intro a c d
    · exists 0
    rw [← Nat.add_assoc, ← Nat.add_assoc]
    step fm
    step fm
    apply stepStar_trans (h _ _ _)
    ring_nf; finish
  have h := many_step d 0 (c+1) 0
  simp only [Nat.add_right_comm, zero_add] at h
  apply stepStar_trans h
  step fm
  finish

theorem ac_to_ac : ⟨a+2, 0, c, 0, 0⟩ [fm]⊢⁺ ⟨a+4, 0, c+a, 0, 0⟩ := by
  apply stepStar_stepPlus_stepPlus ac_to_ce
  apply stepStar_stepPlus_stepPlus ce_to_cd
  apply stepStar_stepPlus_stepPlus _ cd_to_ac
  ring_nf; finish

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨5, 0, 0, 0, 0⟩) (by execute fm 20)
  apply progress_nonhalt_simple (fm := fm) (A := ℕ × ℕ) (fun ⟨a, c⟩ ↦ ⟨a+2, 0, c, 0, 0⟩) ⟨3, 0⟩
  intro ⟨a, c⟩
  exists ⟨a+2, c+a⟩
  apply ac_to_ac
