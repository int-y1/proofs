import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #91: [1/30, 2/77, 1323/2, 5/7, 22/3]

Vector representation:
```
-1 -1 -1  0  0
 1  0  0 -1 -1
-1  3  0  2  0
 0  0  1 -1  0
 1 -1  0  0  1
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_91

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a+1, b+1, c+1, d, e⟩ => some ⟨a, b, c, d, e⟩
  | ⟨a, b, c, d+1, e+1⟩ => some ⟨a+1, b, c, d, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b+3, c, d+2, e⟩
  | ⟨a, b, c, d+1, e⟩ => some ⟨a, b, c+1, d, e⟩
  | ⟨a, b+1, c, d, e⟩ => some ⟨a+1, b, c, d, e+1⟩
  | _ => none

theorem r4_chain : ∀ k, ∀ b c, ⟨0, b, c, k, 0⟩ [fm]⊢* ⟨0, b, c + k, 0, 0⟩ := by
  intro k; induction' k with k ih <;> intro b c
  · simp; exists 0
  step fm
  apply stepStar_trans (ih b (c + 1))
  ring_nf; finish

theorem r5r1_chain : ∀ k, ∀ b e, ⟨0, b + 2 * k, k, 0, e⟩ [fm]⊢* ⟨0, b, 0, 0, e + k⟩ := by
  intro k; induction' k with k ih <;> intro b e
  · simp; exists 0
  rw [show b + 2 * (k + 1) = (b + 2 * k) + 2 from by ring]
  step fm; step fm
  apply stepStar_trans (ih b (e + 1))
  ring_nf; finish

theorem r2r2r3_chain : ∀ k, ∀ j B E,
    ⟨j, B, 0, 2, E + 2 * k⟩ [fm]⊢* ⟨j + k, B + 3 * k, 0, 2, E⟩ := by
  intro k; induction' k with k ih <;> intro j B E
  · simp; exists 0
  rw [show E + 2 * (k + 1) = (E + 2 * k) + 2 from by ring]
  step fm; step fm
  rw [show j + 1 + 1 = (j + 1) + 1 from by ring]
  step fm
  apply stepStar_trans (ih (j + 1) (B + 3) E)
  ring_nf; finish

theorem r3_chain : ∀ k, ∀ B d, ⟨k, B, 0, d, 0⟩ [fm]⊢* ⟨0, B + 3 * k, 0, d + 2 * k, 0⟩ := by
  intro k; induction' k with k ih <;> intro B d
  · simp; exists 0
  step fm
  apply stepStar_trans (ih (B + 3) (d + 2))
  ring_nf; finish

theorem main_odd (r m : ℕ) :
    ⟨0, r + 4 * m + 3, 0, 2 * m + 1, 0⟩ [fm]⊢⁺ ⟨0, r + 6 * m + 9, 0, 2 * m + 4, 0⟩ := by
  apply step_stepStar_stepPlus
  · show fm ⟨0, r + 4 * m + 3, 0, 2 * m + 1, 0⟩ =
         some ⟨0, r + 4 * m + 3, 1, 2 * m, 0⟩
    simp [fm]
  apply stepStar_trans (c₂ := ⟨0, r + 4 * m + 3, 2 * m + 1, 0, 0⟩)
  · have h := r4_chain (2 * m) (r + 4 * m + 3) 1
    rw [show 1 + 2 * m = 2 * m + 1 from by ring] at h; exact h
  apply stepStar_trans (c₂ := ⟨0, r + 1, 0, 0, 2 * m + 1⟩)
  · have h := r5r1_chain (2 * m + 1) (r + 1) 0
    simp only [Nat.zero_add] at h
    rw [show r + 1 + 2 * (2 * m + 1) = r + 4 * m + 3 from by ring] at h; exact h
  apply stepStar_trans (c₂ := ⟨0, r + 3, 0, 2, 2 * m + 2⟩)
  · step fm; step fm; ring_nf; finish
  apply stepStar_trans (c₂ := ⟨m + 1, r + 3 * m + 6, 0, 2, 0⟩)
  · have h := r2r2r3_chain (m + 1) 0 (r + 3) 0
    simp only [Nat.zero_add] at h
    rw [show r + 3 + 3 * (m + 1) = r + 3 * m + 6 from by ring] at h
    refine stepStar_trans ?_ h; ring_nf; finish
  have h := r3_chain (m + 1) (r + 3 * m + 6) 2
  rw [show r + 3 * m + 6 + 3 * (m + 1) = r + 6 * m + 9 from by ring,
      show 2 + 2 * (m + 1) = 2 * m + 4 from by ring] at h; exact h

theorem main_even (r m : ℕ) :
    ⟨0, r + 4 * m + 5, 0, 2 * m + 2, 0⟩ [fm]⊢⁺ ⟨0, r + 6 * m + 12, 0, 2 * m + 5, 0⟩ := by
  apply step_stepStar_stepPlus
  · show fm ⟨0, r + 4 * m + 5, 0, 2 * m + 2, 0⟩ =
         some ⟨0, r + 4 * m + 5, 1, 2 * m + 1, 0⟩
    simp [fm]
  apply stepStar_trans (c₂ := ⟨0, r + 4 * m + 5, 2 * m + 2, 0, 0⟩)
  · have h := r4_chain (2 * m + 1) (r + 4 * m + 5) 1
    rw [show 1 + (2 * m + 1) = 2 * m + 2 from by ring] at h; exact h
  apply stepStar_trans (c₂ := ⟨0, r + 1, 0, 0, 2 * m + 2⟩)
  · have h := r5r1_chain (2 * m + 2) (r + 1) 0
    simp only [Nat.zero_add] at h
    rw [show r + 1 + 2 * (2 * m + 2) = r + 4 * m + 5 from by ring] at h; exact h
  apply stepStar_trans (c₂ := ⟨0, r + 3, 0, 2, 2 * m + 3⟩)
  · step fm; step fm; ring_nf; finish
  apply stepStar_trans (c₂ := ⟨m + 1, r + 3 * m + 6, 0, 2, 1⟩)
  · have h := r2r2r3_chain (m + 1) 0 (r + 3) 1
    simp only [Nat.zero_add] at h
    rw [show r + 3 + 3 * (m + 1) = r + 3 * m + 6 from by ring] at h
    refine stepStar_trans ?_ h; ring_nf; finish
  apply stepStar_trans (c₂ := ⟨m + 1, r + 3 * m + 9, 0, 3, 0⟩)
  · step fm; step fm; ring_nf; finish
  have h := r3_chain (m + 1) (r + 3 * m + 9) 3
  rw [show r + 3 * m + 9 + 3 * (m + 1) = r + 6 * m + 12 from by ring,
      show 3 + 2 * (m + 1) = 2 * m + 5 from by ring] at h; exact h

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨0, 12, 0, 5, 0⟩) (by execute fm 25)
  apply progress_nonhalt (fm := fm)
    (P := fun q ↦ ∃ b d, q = ⟨0, b, 0, d, 0⟩ ∧ b > 2 * d ∧ d ≥ 1)
  · intro c ⟨b, d, hq, hb, hd⟩; subst hq
    rcases Nat.even_or_odd d with ⟨K, hK⟩ | ⟨K, hK⟩
    · have hK1 : K ≥ 1 := by omega
      obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le hK1
      have hd_eq : d = 2 * m + 2 := by omega
      subst hd_eq
      have hr : b = (b - 4 * m - 5) + 4 * m + 5 := by omega
      rw [hr]
      exact ⟨_, ⟨_, _, rfl, by omega, by omega⟩, main_even _ m⟩
    · have hd_eq : d = 2 * K + 1 := by omega
      subst hd_eq
      have hr : b = (b - 4 * K - 3) + 4 * K + 3 := by omega
      rw [hr]
      exact ⟨_, ⟨_, _, rfl, by omega, by omega⟩, main_odd _ K⟩
  · exact ⟨12, 5, rfl, by omega, by omega⟩

end Sz22_2003_unofficial_91
