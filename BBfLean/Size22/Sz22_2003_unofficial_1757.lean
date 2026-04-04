import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #1757: [9/10, 2/21, 539/2, 5/7, 98/11]

Vector representation:
```
-1  2 -1  0  0
 1 -1  0 -1  0
-1  0  0  2  1
 0  0  1 -1  0
 1  0  0  2 -1
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_1757

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a+1, b, c+1, d, e⟩ => some ⟨a, b+2, c, d, e⟩
  | ⟨a, b+1, c, d+1, e⟩ => some ⟨a+1, b, c, d, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b, c, d+2, e+1⟩
  | ⟨a, b, c, d+1, e⟩ => some ⟨a, b, c+1, d, e⟩
  | ⟨a, b, c, d, e+1⟩ => some ⟨a+1, b, c, d+2, e⟩
  | _ => none

theorem d_to_c : ∀ k, ⟨0, 0, c, d + k, e⟩ [fm]⊢* ⟨0, 0, c + k, d, e⟩ := by
  intro k; induction' k with k ih generalizing c d
  · exists 0
  · rw [Nat.add_succ d k]; step fm
    apply stepStar_trans (ih (c := c + 1)); ring_nf; finish

theorem a_to_de : ∀ k, ⟨a + k, 0, 0, d, e⟩ [fm]⊢* ⟨a, 0, 0, d + 2 * k, e + k⟩ := by
  intro k; induction' k with k ih generalizing a d e
  · exists 0
  · rw [Nat.add_succ a k]; step fm
    apply stepStar_trans (ih (a := a) (d := d + 2) (e := e + 1)); ring_nf; finish

theorem interleave_round : ⟨1, b, c + 3, 2, f + 1⟩ [fm]⊢* ⟨1, b + 4, c, 2, f⟩ := by
  step fm; step fm; step fm; step fm; step fm; step fm; finish

theorem interleave_chain : ∀ k, ∀ b c f, ⟨1, b, c + 3 * k, 2, f + k⟩ [fm]⊢* ⟨1, b + 4 * k, c, 2, f⟩ := by
  intro k; induction' k with k ih <;> intro b c f
  · exists 0
  · rw [show c + 3 * (k + 1) = (c + 3) + 3 * k from by ring,
        show f + (k + 1) = (f + 1) + k from by ring]
    apply stepStar_trans (ih b (c + 3) (f + 1))
    apply stepStar_trans (interleave_round (b := b + 4 * k)); ring_nf; finish

theorem drain_chain : ∀ k b, ⟨a + 1, b + 2 * k, 0, 0, f⟩ [fm]⊢* ⟨a + 1 + k, b, 0, 0, f + k⟩ := by
  intro k; induction' k with k ih <;> intro b
  · exists 0
  · rw [show b + 2 * (k + 1) = (b + 2) + 2 * k from by ring]
    apply stepStar_trans (ih (b + 2))
    rw [show a + 1 + k = (a + k) + 1 from by ring]
    step fm
    apply stepStar_trans (step_stepStar
      (show fm ⟨a + k, b + 2, 0, 2, f + k + 1⟩ = some ⟨a + k + 1, b + 1, 0, 1, f + k + 1⟩ from by simp [fm]))
    apply stepStar_trans (step_stepStar
      (show fm ⟨a + k + 1, b + 1, 0, 1, f + k + 1⟩ = some ⟨a + k + 2, b, 0, 0, f + k + 1⟩ from by simp [fm]))
    rw [show a + k + 2 = a + 1 + (k + 1) from by ring,
        show f + k + 1 = f + (k + 1) from by ring]
    finish

theorem end_r0 : ⟨1, b + 2, 0, 2, f⟩ [fm]⊢* ⟨3, b, 0, 0, f⟩ := by
  step fm; step fm; finish

theorem end_r1 : ⟨1, b, 1, 2, f⟩ [fm]⊢* ⟨2, b, 0, 0, f⟩ := by
  step fm; step fm; step fm; finish

theorem end_r2 : ⟨1, b, 2, 2, f⟩ [fm]⊢* ⟨2, b, 0, 0, f + 1⟩ := by
  step fm; step fm; step fm; step fm; step fm; step fm; step fm; finish

theorem trans_r2 : ∀ m, ⟨0, 0, 0, 3 * m + 2, 3 * m + 1 + F⟩ [fm]⊢⁺
    ⟨0, 0, 0, 4 * m + 4, 6 * m + 3 + F⟩ := by
  intro m
  apply stepStar_stepPlus_stepPlus
  · rw [show (3 * m + 2 : ℕ) = 0 + (3 * m + 2) from by ring]
    exact d_to_c (3 * m + 2) (c := 0) (d := 0) (e := 3 * m + 1 + F)
  simp only [Nat.zero_add]
  rw [show 3 * m + 1 + F = (3 * m + F) + 1 from by ring]
  apply step_stepStar_stepPlus
    (show fm ⟨0, 0, 3 * m + 2, 0, (3 * m + F) + 1⟩ = some ⟨1, 0, 3 * m + 2, 2, 3 * m + F⟩ from by simp [fm])
  rw [show 3 * m + 2 = 2 + 3 * m from by ring,
      show 3 * m + F = (2 * m + F) + m from by omega]
  apply stepStar_trans (interleave_chain m 0 2 (2 * m + F))
  rw [show 0 + 4 * m = 4 * m from by ring]
  apply stepStar_trans (end_r2 (b := 4 * m) (f := 2 * m + F))
  rw [show 4 * m = 0 + 2 * (2 * m) from by ring]
  apply stepStar_trans (drain_chain (2 * m) 0 (a := 1) (f := 2 * m + F + 1))
  rw [show 1 + 1 + 2 * m = 0 + (2 * m + 2) from by ring]
  apply stepStar_trans (a_to_de (2 * m + 2) (a := 0) (d := 0) (e := 2 * m + F + 1 + 2 * m))
  ring_nf; finish

theorem trans_r1 : ∀ m, ⟨0, 0, 0, 3 * (m + 1) + 1, 3 * (m + 1) + F⟩ [fm]⊢⁺
    ⟨0, 0, 0, 4 * m + 8, 6 * m + 7 + F⟩ := by
  intro m
  apply stepStar_stepPlus_stepPlus
  · rw [show (3 * (m + 1) + 1 : ℕ) = 0 + (3 * (m + 1) + 1) from by ring]
    exact d_to_c (3 * (m + 1) + 1) (c := 0) (d := 0) (e := 3 * (m + 1) + F)
  simp only [Nat.zero_add]
  rw [show 3 * (m + 1) + F = (3 * m + 2 + F) + 1 from by ring]
  apply step_stepStar_stepPlus
    (show fm ⟨0, 0, 3 * (m + 1) + 1, 0, (3 * m + 2 + F) + 1⟩ = some ⟨1, 0, 3 * (m + 1) + 1, 2, 3 * m + 2 + F⟩
      from by simp [fm])
  rw [show 3 * (m + 1) + 1 = 1 + 3 * (m + 1) from by ring,
      show 3 * m + 2 + F = (2 * m + 1 + F) + (m + 1) from by omega]
  apply stepStar_trans (interleave_chain (m + 1) 0 1 (2 * m + 1 + F))
  rw [show 0 + 4 * (m + 1) = 4 * (m + 1) from by ring]
  apply stepStar_trans (end_r1 (b := 4 * (m + 1)) (f := 2 * m + 1 + F))
  rw [show 4 * (m + 1) = 0 + 2 * (2 * (m + 1)) from by ring]
  apply stepStar_trans (drain_chain (2 * (m + 1)) 0 (a := 1) (f := 2 * m + 1 + F))
  rw [show 1 + 1 + 2 * (m + 1) = 0 + (2 * m + 4) from by ring]
  apply stepStar_trans (a_to_de (2 * m + 4) (a := 0) (d := 0) (e := 2 * m + 1 + F + 2 * (m + 1)))
  ring_nf; finish

theorem trans_r0 : ∀ m, ⟨0, 0, 0, 3 * (m + 1), 3 * m + 2 + F⟩ [fm]⊢⁺
    ⟨0, 0, 0, 4 * m + 8, 6 * m + 5 + F⟩ := by
  intro m
  apply stepStar_stepPlus_stepPlus
  · rw [show (3 * (m + 1) : ℕ) = 0 + 3 * (m + 1) from by ring]
    exact d_to_c (3 * (m + 1)) (c := 0) (d := 0) (e := 3 * m + 2 + F)
  simp only [Nat.zero_add]
  rw [show 3 * m + 2 + F = (3 * m + 1 + F) + 1 from by ring]
  apply step_stepStar_stepPlus
    (show fm ⟨0, 0, 3 * (m + 1), 0, (3 * m + 1 + F) + 1⟩ = some ⟨1, 0, 3 * (m + 1), 2, 3 * m + 1 + F⟩
      from by simp [fm])
  rw [show 3 * (m + 1) = 0 + 3 * (m + 1) from by ring,
      show 3 * m + 1 + F = (2 * m + F) + (m + 1) from by omega]
  apply stepStar_trans (interleave_chain (m + 1) 0 0 (2 * m + F))
  rw [show 0 + 4 * (m + 1) = (4 * m + 2) + 2 from by ring]
  apply stepStar_trans (end_r0 (b := 4 * m + 2) (f := 2 * m + F))
  rw [show 4 * m + 2 = 0 + 2 * (2 * m + 1) from by ring]
  apply stepStar_trans (drain_chain (2 * m + 1) 0 (a := 2) (f := 2 * m + F))
  rw [show 2 + 1 + (2 * m + 1) = 0 + (2 * m + 4) from by ring]
  apply stepStar_trans (a_to_de (2 * m + 4) (a := 0) (d := 0) (e := 2 * m + F + (2 * m + 1)))
  ring_nf; finish

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨0, 0, 0, 2, 1⟩) (by execute fm 1)
  apply progress_nonhalt (fm := fm)
    (P := fun q ↦ ∃ D E, q = ⟨0, 0, 0, D, E⟩ ∧ D ≥ 2 ∧ D % 2 = 0 ∧ E ≥ D - 1)
  · intro c ⟨D, E, hq, hD, hDeven, hE⟩; subst hq
    have hDmod : D % 3 = 0 ∨ D % 3 = 1 ∨ D % 3 = 2 := by omega
    rcases hDmod with h0 | h1 | h2
    · obtain ⟨m, rfl⟩ : ∃ m, D = 3 * m := ⟨D / 3, by omega⟩
      have hm1 : m ≥ 2 := by omega
      obtain ⟨m', rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
      obtain ⟨F, rfl⟩ : ∃ F, E = 3 * m' + 2 + F := ⟨E - (3 * m' + 2), by omega⟩
      exact ⟨⟨0, 0, 0, 4 * m' + 8, 6 * m' + 5 + F⟩,
        ⟨4 * m' + 8, 6 * m' + 5 + F, rfl, by omega, by omega, by omega⟩,
        trans_r0 m'⟩
    · obtain ⟨m, rfl⟩ : ∃ m, D = 3 * m + 1 := ⟨D / 3, by omega⟩
      obtain ⟨m', rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
      obtain ⟨F, rfl⟩ : ∃ F, E = 3 * (m' + 1) + F := ⟨E - 3 * (m' + 1), by omega⟩
      exact ⟨⟨0, 0, 0, 4 * m' + 8, 6 * m' + 7 + F⟩,
        ⟨4 * m' + 8, 6 * m' + 7 + F, rfl, by omega, by omega, by omega⟩,
        trans_r1 m'⟩
    · obtain ⟨m, rfl⟩ : ∃ m, D = 3 * m + 2 := ⟨D / 3, by omega⟩
      obtain ⟨F, rfl⟩ : ∃ F, E = 3 * m + 1 + F := ⟨E - (3 * m + 1), by omega⟩
      exact ⟨⟨0, 0, 0, 4 * m + 4, 6 * m + 3 + F⟩,
        ⟨4 * m + 4, 6 * m + 3 + F, rfl, by omega, by omega, by omega⟩,
        trans_r2 m⟩
  · exact ⟨2, 1, rfl, by omega, by omega, by omega⟩
