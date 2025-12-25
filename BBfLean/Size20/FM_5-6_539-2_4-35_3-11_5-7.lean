import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# [5/6, 539/2, 4/35, 3/11, 5/7]

Vector representation:
```
-1 -1  1  0  0
-1  0  0  2  1
 2  0 -1 -1  0
 0  1  0  0 -1
 0  0  1 -1  0
```

This is a sz20 machine that doesn't halt.
-/

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a+1, b+1, c, d, e⟩ => some ⟨a, b, c+1, d, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b, c, d+2, e+1⟩
  | ⟨a, b, c+1, d+1, e⟩ => some ⟨a+2, b, c, d, e⟩
  | ⟨a, b, c, d, e+1⟩ => some ⟨a, b+1, c, d, e⟩
  | ⟨a, b, c, d+1, e⟩ => some ⟨a, b, c+1, d, e⟩
  | _ => none

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

theorem bd_to_a1cd : ⟨0, 2*b+1, 0, d+b+2, 0⟩ [fm]⊢⁺ ⟨1, 0, b+1, d, 0⟩ := by
  step fm
  have many_step : ∀ k c d, ⟨0, 2*k+1, c+1, d+k, 0⟩ [fm]⊢* ⟨0, 1, c+k+1, d, 0⟩ := by
    intro k; induction' k with k h <;> intro c d
    · exists 0
    rw [← Nat.add_assoc, Nat.mul_add]
    step fm; step fm; step fm
    apply stepStar_trans (h _ _)
    ring_nf; finish
  rw [add_right_comm]
  apply stepStar_trans (many_step _ _ _)
  step fm; step fm
  ring_nf; finish

theorem a1cd_to_de : ⟨1, 0, c, d, 0⟩ [fm]⊢* ⟨0, 0, 0, d+3*c+2, 2*c+1⟩ := by
  have many_step : ∀ k c d e, ⟨1, 0, c+k, d, e⟩ [fm]⊢* ⟨1, 0, c, d+3*k, e+2*k⟩ := by
    intro k; induction' k with k h <;> intro c d e
    · exists 0
    rw [← Nat.add_assoc]
    step fm; step fm; step fm
    apply stepStar_trans (h _ _ _)
    ring_nf; finish
  apply stepStar_trans (Nat.zero_add c ▸ many_step c 0 d 0)
  step fm
  ring_nf; finish

theorem de_to_de : ⟨0, 0, 0, d+e+2, 2*e+1⟩ [fm]⊢⁺ ⟨0, 0, 0, d+3*e+5, 2*e+3⟩ := by
  apply stepStar_stepPlus_stepPlus de_to_bd
  apply stepPlus_stepStar_stepPlus bd_to_a1cd
  apply stepStar_trans a1cd_to_de
  ring_nf; finish

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨0, 0, 0, 5, 3⟩) (by execute fm 9)
  apply progress_nonhalt_simple (fm := fm) (A := ℕ × ℕ) (fun ⟨d, e⟩ ↦ ⟨0, 0, 0, d+e+2, 2*e+1⟩) ⟨2, 1⟩
  intro ⟨d, e⟩
  exists ⟨d+2*e+2, e+1⟩
  simp only [(by ring : d + 2 * e + 2 + (e + 1) + 2 = d+3*e+5)]
  apply de_to_de
