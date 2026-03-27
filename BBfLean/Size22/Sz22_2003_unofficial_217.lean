import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #217: [1/90, 14/3, 9/77, 5/7, 363/2]

Vector representation:
```
-1 -2 -1  0  0
 1 -1  0  1  0
 0  2  0 -1 -1
 0  0  1 -1  0
-1  1  0  0  2
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_217

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a+1, b+2, c+1, d, e⟩ => some ⟨a, b, c, d, e⟩
  | ⟨a, b+1, c, d, e⟩ => some ⟨a+1, b, c, d+1, e⟩
  | ⟨a, b, c, d+1, e+1⟩ => some ⟨a, b+2, c, d, e⟩
  | ⟨a, b, c, d+1, e⟩ => some ⟨a, b, c+1, d, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b+1, c, d, e+2⟩
  | _ => none

theorem d_to_c : ∀ k a c d, (⟨a, 0, c, d + k, 0⟩ : Q) [fm]⊢* ⟨a, 0, c + k, d, 0⟩ := by
  intro k; induction' k with k ih <;> intro a c d
  · exists 0
  rw [show d + (k + 1) = (d + k) + 1 from by ring]
  step fm
  apply stepStar_trans (ih _ _ _)
  ring_nf; finish

theorem drain_step : ∀ a c e, (⟨a + 1, 0, c + 1, 0, e⟩ : Q) [fm]⊢* ⟨a, 0, c, 0, e + 1⟩ := by
  intro a c e
  step fm; step fm; step fm; step fm; finish

theorem drain : ∀ k a e, (⟨a + k, 0, k, 0, e⟩ : Q) [fm]⊢* ⟨a, 0, 0, 0, e + k⟩ := by
  intro k; induction' k with k ih <;> intro a e
  · exists 0
  rw [show a + (k + 1) = (a + k) + 1 from by ring,
      show (k + 1 : ℕ) = k + 1 from rfl]
  apply stepStar_trans (drain_step _ _ _)
  apply stepStar_trans (ih _ _)
  ring_nf; finish

theorem kickstart : ∀ a e, (⟨a + 1, 0, 0, 0, e + 1⟩ : Q) [fm]⊢⁺ ⟨a + 3, 0, 0, 2, e + 2⟩ := by
  intro a e
  step fm; step fm; step fm; step fm; step fm; finish

theorem grow_step : ∀ a d e, (⟨a, 0, 0, d + 1, e + 1⟩ : Q) [fm]⊢* ⟨a + 2, 0, 0, d + 2, e⟩ := by
  intro a d e
  step fm; step fm; step fm; finish

theorem grow : ∀ k a d e, (⟨a, 0, 0, d + 1, e + k⟩ : Q) [fm]⊢* ⟨a + 2 * k, 0, 0, d + k + 1, e⟩ := by
  intro k; induction' k with k ih <;> intro a d e
  · exists 0
  rw [show e + (k + 1) = (e + k) + 1 from by ring]
  apply stepStar_trans (grow_step _ _ _)
  apply stepStar_trans (ih _ _ _)
  ring_nf; finish

theorem main_trans (a d : ℕ) (hd : d ≥ 1) (ha : a ≥ d + 1) :
    (⟨a, 0, 0, d, 0⟩ : Q) [fm]⊢⁺ ⟨a + d + 4, 0, 0, d + 3, 0⟩ := by
  obtain ⟨d', rfl⟩ : ∃ d', d = d' + 1 := ⟨d - 1, by omega⟩
  obtain ⟨a', rfl⟩ : ∃ a', a = a' + d' + 2 := ⟨a - d' - 2, by omega⟩
  rw [show a' + d' + 2 + (d' + 1) + 4 = a' + 2 * d' + 7 from by ring,
      show d' + 1 + 3 = d' + 4 from by ring]
  apply stepStar_stepPlus_stepPlus (c₂ := ⟨a' + 1, 0, 0, 0, d' + 1⟩)
  · apply stepStar_trans (c₂ := ⟨a' + d' + 2, 0, d' + 1, 0, 0⟩)
    · have h := d_to_c (d' + 1) (a' + d' + 2) 0 0
      simp only [Nat.zero_add] at h; exact h
    · rw [show a' + d' + 2 = (a' + 1) + (d' + 1) from by ring]
      have h := drain (d' + 1) (a' + 1) 0
      simp only [Nat.zero_add] at h; exact h
  apply stepPlus_stepStar_stepPlus (c₂ := ⟨a' + 3, 0, 0, 2, d' + 2⟩)
  · exact kickstart a' d'
  · have h := grow (d' + 2) (a' + 3) 1 0
    simp only [Nat.zero_add,
      (by ring : (a' + 3) + 2 * (d' + 2) = a' + 2 * d' + 7),
      (by ring : 1 + (d' + 2) + 1 = d' + 4)] at h
    exact h

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨5, 0, 0, 3, 0⟩) (by execute fm 8)
  apply progress_nonhalt (fm := fm)
    (P := fun q ↦ ∃ a d, q = ⟨a, 0, 0, d, 0⟩ ∧ d ≥ 1 ∧ a ≥ d + 1)
  · intro c ⟨a, d, hq, hd, ha⟩
    subst hq
    exact ⟨⟨a + d + 4, 0, 0, d + 3, 0⟩, ⟨a + d + 4, d + 3, rfl, by omega, by omega⟩,
      main_trans a d hd ha⟩
  · exact ⟨5, 3, rfl, by omega, by omega⟩

end Sz22_2003_unofficial_217
