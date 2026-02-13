import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz20_6 #4: [5/6, 44/35, 49/2, 3/11, 5/7]

Vector representation:
```
-1 -1  1  0  0
 2  0 -1 -1  1
-1  0  0  2  0
 0  1  0  0 -1
 0  0  1 -1  0
```

This Fractran program doesn't halt.
-/

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a+1, b+1, c, d, e⟩ => some ⟨a, b, c+1, d, e⟩
  | ⟨a, b, c+1, d+1, e⟩ => some ⟨a+2, b, c, d, e+1⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b, c, d+2, e⟩
  | ⟨a, b, c, d, e+1⟩ => some ⟨a, b+1, c, d, e⟩
  | ⟨a, b, c, d+1, e⟩ => some ⟨a, b, c+1, d, e⟩
  | _ => none

theorem ade_to_de : ⟨a, 0, 0, d, e⟩ [fm]⊢* ⟨0, 0, 0, d+2*a, e⟩ := by
  have many_step : ∀ k a d e, ⟨a+k, 0, 0, d, e⟩ [fm]⊢* ⟨a, 0, 0, d+2*k, e⟩ := by
    intro k; induction' k with k h <;> intro a d e
    · exists 0
    rw [← Nat.add_assoc]
    step fm
    apply stepStar_trans (h _ _ _)
    ring_nf; finish
  have h := many_step a 0 d e
  rw [zero_add] at h
  exact h

theorem de_to_bd : ⟨0, 0, 0, d, e⟩ [fm]⊢* ⟨0, e, 0, d, 0⟩ := by
  have many_step : ∀ k b d e, ⟨0, b, 0, d, e+k⟩ [fm]⊢* ⟨0, b+k, 0, d, e⟩ := by
    intro k; induction' k with k h <;> intro b d e
    · exists 0
    rw [← Nat.add_assoc]
    step fm
    apply stepStar_trans (h _ _ _)
    ring_nf; finish
  have h := many_step e 0 d 0
  rw [zero_add] at h
  exact h

theorem bd_odd_to_a1cde : ⟨0, 2*b+1, 0, d+b+2, 0⟩ [fm]⊢⁺ ⟨1, 0, b+1, d, b+1⟩ := by
  step fm
  have many_step : ∀ k c d e, ⟨0, 2*k+1, c+1, d+k, e⟩ [fm]⊢* ⟨0, 1, c+k+1, d, e+k⟩ := by
    intro k; induction' k with k h <;> intro c d e
    · exists 0
    rw [← Nat.add_assoc, Nat.mul_add]
    step fm; step fm; step fm
    apply stepStar_trans (h _ _ _)
    ring_nf; finish
  rw [add_right_comm]
  apply stepStar_trans (many_step _ _ _ _)
  step fm; step fm
  ring_nf; finish

theorem bd_even_to_cde : ⟨0, 2*b, 0, d+b+2, 0⟩ [fm]⊢⁺ ⟨0, 0, b+1, d+1, b⟩ := by
  step fm
  have many_step : ∀ k c d e, ⟨0, 2*k, c+1, d+k, e⟩ [fm]⊢* ⟨0, 0, c+k+1, d, e+k⟩ := by
    intro k; induction' k with k h <;> intro c d e
    · exists 0
    rw [← Nat.add_assoc, Nat.mul_add]
    step fm; step fm; step fm
    apply stepStar_trans (h _ _ _)
    ring_nf; finish
  rw [add_right_comm]
  apply stepStar_trans (many_step _ _ _ _)
  ring_nf; finish

theorem acde_to_ade : ⟨a, 0, c, d+c, e⟩ [fm]⊢* ⟨a+2*c, 0, 0, d, e+c⟩ := by
  have many_step : ∀ k a d e, ⟨a, 0, k, d+k, e⟩ [fm]⊢* ⟨a+2*k, 0, 0, d, e+k⟩ := by
    intro k; induction' k with k h <;> intro a d e
    · exists 0
    rw [← Nat.add_assoc]
    step fm
    apply stepStar_trans (h _ _ _)
    ring_nf; finish
  apply stepStar_trans (many_step _ _ _ _)
  ring_nf; finish

theorem ade_to_ade : ⟨e*2+1, 0, 0, d, e*2⟩ [fm]⊢⁺ ⟨e*2+3, 0, 0, d+e*4+1, e*2+2⟩ := by
  apply stepStar_stepPlus_stepPlus ade_to_de
  apply stepStar_stepPlus_stepPlus de_to_bd
  rw [(by ring : d + 2 * (e * 2 + 1) = d + 2*e + e + e + 2), Nat.mul_comm e 2]
  apply stepPlus_stepStar_stepPlus bd_even_to_cde
  apply stepStar_trans acde_to_ade
  apply stepStar_trans ade_to_de
  apply stepStar_trans de_to_bd
  refine stepPlus_stepStar ?_
  rw [(by ring : e + (e + 1) = 2*e+1),
    (by ring : d + 2 * e + 2 * (0 + 2 * (e + 1)) = d+4*e+1+e+1+e+2)]
  apply stepPlus_stepStar_stepPlus bd_odd_to_a1cde
  apply stepStar_trans acde_to_ade
  ring_nf; finish

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨1, 0, 0, 0, 0⟩) (by finish)
  apply progress_nonhalt_simple (fm := fm) (A := ℕ × ℕ) (fun ⟨d, e⟩ ↦ ⟨e*2+1, 0, 0, d, e*2⟩) ⟨0, 0⟩
  intro ⟨d, e⟩
  exists ⟨d+e*4+1, e+1⟩
  simp only [Nat.add_mul]
  apply ade_to_ade
