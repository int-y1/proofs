import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz20_6 #2: [5/6, 4/35, 539/2, 3/11, 5/7]

Vector representation:
```
-1 -1  1  0  0
 2  0 -1 -1  0
-1  0  0  2  1
 0  1  0  0 -1
 0  0  1 -1  0
```

This Fractran program doesn't halt.
-/

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a+1, b+1, c, d, e⟩ => some ⟨a, b, c+1, d, e⟩
  | ⟨a, b, c+1, d+1, e⟩ => some ⟨a+2, b, c, d, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b, c, d+2, e+1⟩
  | ⟨a, b, c, d, e+1⟩ => some ⟨a, b+1, c, d, e⟩
  | ⟨a, b, c, d+1, e⟩ => some ⟨a, b, c+1, d, e⟩
  | _ => none

theorem ad_to_de : ⟨a, 0, 0, d, 0⟩ [fm]⊢* ⟨0, 0, 0, d+2*a, a⟩ := by
  have many_step : ∀ k a d e, ⟨a+k, 0, 0, d, e⟩ [fm]⊢* ⟨a, 0, 0, d+2*k, e+k⟩ := by
    intro k; induction' k with k h <;> intro a d e
    · exists 0
    rw [← Nat.add_assoc]
    step fm
    apply stepStar_trans (h _ _ _)
    ring_nf; finish
  have h := many_step a 0 d 0
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

theorem a1cd_to_ad : ⟨1, 0, c, d+c, 0⟩ [fm]⊢* ⟨2*c+1, 0, 0, d, 0⟩ := by
  have many_step : ∀ k a d, ⟨a, 0, k, d+k, 0⟩ [fm]⊢* ⟨a+2*k, 0, 0, d, 0⟩ := by
    intro k; induction' k with k h <;> intro a d
    · exists 0
    rw [← Nat.add_assoc]
    step fm
    apply stepStar_trans (h _ _)
    ring_nf; finish
  apply stepStar_trans (many_step _ _ _)
  ring_nf; finish

theorem ad_to_ad : ⟨2*a+3, 0, 0, d, 0⟩ [fm]⊢⁺ ⟨2*a+5, 0, 0, d+2*a+1, 0⟩ := by
  apply stepStar_stepPlus_stepPlus ad_to_de
  apply stepStar_stepPlus_stepPlus de_to_bd
  rw [(by ring : d + 2 * (2 * a + 3) = ((d+2*a+1) + a + 2) + a + 3), (by ring : 2*a+3 = 2*(a+1)+1)]
  apply stepPlus_stepStar_stepPlus bd_to_a1cd
  apply stepStar_trans a1cd_to_ad
  finish

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨5, 0, 0, 0, 0⟩) (by execute fm 20)
  apply progress_nonhalt_simple (fm := fm) (A := ℕ × ℕ) (fun ⟨a, d⟩ ↦ ⟨2*a+3, 0, 0, d, 0⟩) ⟨1, 0⟩
  intro ⟨a, d⟩
  exists ⟨a+1, d+2*a+1⟩
  apply ad_to_ad
