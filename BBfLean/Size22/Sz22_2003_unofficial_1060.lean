import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #1060: [5/18, 539/2, 4/35, 3/7, 14/11]

Vector representation:
```
-1 -2  1  0  0
-1  0  0  2  1
 2  0 -1 -1  0
 0  1  0 -1  0
 1  0  0  1 -1
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_1060

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a+1, b+2, c, d, e⟩ => some ⟨a, b, c+1, d, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b, c, d+2, e+1⟩
  | ⟨a, b, c+1, d+1, e⟩ => some ⟨a+2, b, c, d, e⟩
  | ⟨a, b, c, d+1, e⟩ => some ⟨a, b+1, c, d, e⟩
  | ⟨a, b, c, d, e+1⟩ => some ⟨a+1, b, c, d+1, e⟩
  | _ => none

private theorem step_r5 (b C E : ℕ) :
    ⟨(0 : ℕ), b, C, 0, E + 1⟩ [fm]⊢ ⟨1, b, C, 1, E⟩ := by
  show fm ⟨0, b, C, 0, E + 1⟩ = some ⟨1, b, C, 1, E⟩
  unfold fm; simp only

private theorem chain_b0 : ∀ k, ∀ c d e,
    ⟨(0 : ℕ), 0, c + k, d + 1, e⟩ [fm]⊢* ⟨0, 0, c, d + 3 * k + 1, e + 2 * k⟩ := by
  intro k; induction' k with k ih <;> intro c d e
  · ring_nf; finish
  · rw [show c + (k + 1) = (c + k) + 1 from by ring,
        show d + 3 * (k + 1) + 1 = (d + 3) + 3 * k + 1 from by ring,
        show e + 2 * (k + 1) = (e + 2) + 2 * k from by ring]
    step fm; step fm; step fm
    exact ih c (d + 3) (e + 2)

private theorem chain_b1 : ∀ k, ∀ c d e,
    ⟨(0 : ℕ), 1, c + k, d + 1, e⟩ [fm]⊢* ⟨0, 1, c, d + 3 * k + 1, e + 2 * k⟩ := by
  intro k; induction' k with k ih <;> intro c d e
  · ring_nf; finish
  · rw [show c + (k + 1) = (c + k) + 1 from by ring,
        show d + 3 * (k + 1) + 1 = (d + 3) + 3 * k + 1 from by ring,
        show e + 2 * (k + 1) = (e + 2) + 2 * k from by ring]
    step fm; step fm; step fm
    exact ih c (d + 3) (e + 2)

private theorem r4_drain : ∀ k, ∀ b e,
    ⟨(0 : ℕ), b, 0, k, e⟩ [fm]⊢* ⟨0, b + k, 0, 0, e⟩ := by
  intro k; induction' k with k ih <;> intro b e
  · ring_nf; finish
  · rw [show b + (k + 1) = (b + 1) + k from by ring]
    step fm; exact ih (b + 1) e

private theorem chain_drain_b0 (k d e : ℕ) :
    ⟨(0 : ℕ), 0, k, d + 1, e⟩ [fm]⊢* ⟨0, d + 3 * k + 1, 0, 0, e + 2 * k⟩ := by
  have h1 := chain_b0 k 0 d e
  have h2 := r4_drain (d + 3 * k + 1) 0 (e + 2 * k)
  have h3 := stepStar_trans h1 h2
  convert h3 using 2; ring_nf

private theorem chain_drain_b1 (k d e : ℕ) :
    ⟨(0 : ℕ), 1, k, d + 1, e⟩ [fm]⊢* ⟨0, d + 3 * k + 2, 0, 0, e + 2 * k⟩ := by
  have h1 := chain_b1 k 0 d e
  have h2 := r4_drain (d + 3 * k + 1) 1 (e + 2 * k)
  have h3 := stepStar_trans h1 h2
  convert h3 using 2; ring_nf

private theorem outer_round (b C E : ℕ) :
    ⟨(0 : ℕ), b + 6, C, 0, E + 1⟩ [fm]⊢* ⟨0, b, C + 2, 0, E⟩ := by
  apply stepStar_trans (step_stepStar (step_r5 (b + 6) C E))
  step fm; step fm; step fm; step fm
  ring_nf; finish

private theorem outer_chain : ∀ k, ∀ b C E,
    ⟨(0 : ℕ), b + 6 * (k + 1), C, 0, E + (k + 1)⟩ [fm]⊢*
    ⟨0, b, C + 2 * (k + 1), 0, E⟩ := by
  intro k; induction' k with k ih <;> intro b C E
  · rw [show 6 * 1 = 6 from by ring, show 2 * 1 = 2 from by ring,
        show E + 1 = E + 1 from rfl]
    exact outer_round b C E
  · apply stepStar_trans
    · rw [show 6 * (k + 1 + 1) = 6 * (k + 1) + 6 from by ring,
          show E + (k + 1 + 1) = (E + 1) + (k + 1) from by ring,
          show b + (6 * (k + 1) + 6) = (b + 6) + 6 * (k + 1) from by ring]
      exact ih (b + 6) C (E + 1)
    · show ⟨(0 : ℕ), b + 6, C + 2 * (k + 1), 0, E + 1⟩ [fm]⊢*
          ⟨0, b, C + 2 * (k + 1 + 1), 0, E⟩
      rw [show C + 2 * (k + 1 + 1) = (C + 2 * (k + 1)) + 2 from by ring]
      exact outer_round b (C + 2 * (k + 1)) E

private theorem tail_r0 (j F : ℕ) :
    ⟨(0 : ℕ), 2, 2 * j, 0, F + 1⟩ [fm]⊢⁺ ⟨0, 6 * j + 4, 0, 0, 4 * j + F + 2⟩ := by
  apply step_stepStar_stepPlus (step_r5 2 (2 * j) F)
  step fm
  rw [show (6 : ℕ) * j + 4 = 0 + 3 * (2 * j + 1) + 1 from by ring,
      show 4 * j + F + 2 = F + 2 * (2 * j + 1) from by ring]
  exact chain_drain_b0 (2 * j + 1) 0 F

private theorem tail_r1 (j F : ℕ) :
    ⟨(0 : ℕ), 3, 2 * j, 0, F + 1⟩ [fm]⊢⁺ ⟨0, 6 * j + 5, 0, 0, 4 * j + F + 2⟩ := by
  apply step_stepStar_stepPlus (step_r5 3 (2 * j) F)
  step fm
  rw [show (6 : ℕ) * j + 5 = 0 + 3 * (2 * j + 1) + 2 from by ring,
      show 4 * j + F + 2 = F + 2 * (2 * j + 1) from by ring]
  exact chain_drain_b1 (2 * j + 1) 0 F

private theorem tail_r2 (j F : ℕ) :
    ⟨(0 : ℕ), 4, 2 * j, 0, F + 1⟩ [fm]⊢⁺ ⟨0, 6 * j + 5, 0, 0, 4 * j + F + 3⟩ := by
  apply step_stepStar_stepPlus (step_r5 4 (2 * j) F)
  step fm; step fm; step fm; step fm
  rw [show (6 : ℕ) * j + 5 = 1 + 3 * (2 * j + 1) + 1 from by ring,
      show 4 * j + F + 3 = (F + 1) + 2 * (2 * j + 1) from by ring]
  exact chain_drain_b0 (2 * j + 1) 1 (F + 1)

private theorem tail_r3 (j F : ℕ) :
    ⟨(0 : ℕ), 5, 2 * j, 0, F + 1⟩ [fm]⊢⁺ ⟨0, 6 * j + 6, 0, 0, 4 * j + F + 3⟩ := by
  apply step_stepStar_stepPlus (step_r5 5 (2 * j) F)
  step fm; step fm; step fm; step fm
  rw [show (6 : ℕ) * j + 6 = 1 + 3 * (2 * j + 1) + 2 from by ring,
      show 4 * j + F + 3 = (F + 1) + 2 * (2 * j + 1) from by ring]
  exact chain_drain_b1 (2 * j + 1) 1 (F + 1)

private theorem tail_r4 (j G : ℕ) :
    ⟨(0 : ℕ), 6, 2 * j, 0, G + 2⟩ [fm]⊢⁺ ⟨0, 6 * j + 9, 0, 0, 4 * j + G + 5⟩ := by
  apply step_stepStar_stepPlus (step_r5 6 (2 * j) (G + 1))
  step fm; step fm; step fm; step fm
  apply stepStar_trans (step_stepStar (step_r5 0 (2 * j + 1 + 1) G))
  step fm
  rw [show (6 : ℕ) * j + 9 = 2 + 3 * (2 * j + 2) + 1 from by ring,
      show 4 * j + G + 5 = (G + 1) + 2 * (2 * j + 2) from by ring]
  exact chain_drain_b0 (2 * j + 2) 2 (G + 1)

private theorem tail_r5 (j G : ℕ) :
    ⟨(0 : ℕ), 7, 2 * j, 0, G + 2⟩ [fm]⊢⁺ ⟨0, 6 * j + 10, 0, 0, 4 * j + G + 5⟩ := by
  apply step_stepStar_stepPlus (step_r5 7 (2 * j) (G + 1))
  step fm; step fm; step fm; step fm
  apply stepStar_trans (step_stepStar (step_r5 1 (2 * j + 1 + 1) G))
  step fm
  rw [show (6 : ℕ) * j + 10 = 2 + 3 * (2 * j + 2) + 2 from by ring,
      show 4 * j + G + 5 = (G + 1) + 2 * (2 * j + 2) from by ring]
  exact chain_drain_b1 (2 * j + 2) 2 (G + 1)

private theorem full_trans (B E : ℕ) (hBE : 6 * E ≥ B) :
    ∃ B' E', ⟨(0 : ℕ), B + 2, 0, 0, E + 2⟩ [fm]⊢⁺ ⟨0, B' + 2, 0, 0, E' + 2⟩ ∧
    6 * E' ≥ B' := by
  obtain ⟨j, r, rfl, hr6⟩ : ∃ j r, B = 6 * j + r ∧ r < 6 :=
    ⟨B / 6, B % 6, (Nat.div_add_mod B 6).symm, Nat.mod_lt _ (by omega)⟩
  have hEj : E ≥ j := by omega
  obtain ⟨w, rfl⟩ : ∃ w, E = w + j := ⟨E - j, by omega⟩
  have hoc_star : j ≥ 1 → ⟨(0 : ℕ), 6 * j + r + 2, 0, 0, w + j + 2⟩ [fm]⊢*
      ⟨0, r + 2, 2 * j, 0, w + 2⟩ := by
    intro hj1
    obtain ⟨j', rfl⟩ : ∃ j', j = j' + 1 := ⟨j - 1, by omega⟩
    rw [show 6 * (j' + 1) + r + 2 = (r + 2) + 6 * (j' + 1) from by ring,
        show w + (j' + 1) + 2 = (w + 2) + (j' + 1) from by ring]
    convert outer_chain j' (r + 2) 0 (w + 2) using 2; ring_nf
  have hr_cases : r = 0 ∨ r = 1 ∨ r = 2 ∨ r = 3 ∨ r = 4 ∨ r = 5 := by omega
  rcases hr_cases with rfl | rfl | rfl | rfl | rfl | rfl
  · exact ⟨6 * j + 2, 4 * j + w + 1, by
      rcases j.eq_zero_or_pos with rfl | hj1
      · simp only [Nat.mul_zero, Nat.zero_add, Nat.add_zero]
        convert tail_r0 0 (w + 1) using 2; ring_nf
      · exact stepStar_stepPlus_stepPlus (hoc_star hj1)
            (by convert tail_r0 j (w + 1) using 2)
    , by omega⟩
  · exact ⟨6 * j + 3, 4 * j + w + 1, by
      rcases j.eq_zero_or_pos with rfl | hj1
      · simp only [Nat.mul_zero, Nat.zero_add, Nat.add_zero]
        convert tail_r1 0 (w + 1) using 2; ring_nf
      · exact stepStar_stepPlus_stepPlus (hoc_star hj1)
            (by convert tail_r1 j (w + 1) using 2)
    , by omega⟩
  · exact ⟨6 * j + 3, 4 * j + w + 2, by
      rcases j.eq_zero_or_pos with rfl | hj1
      · simp only [Nat.mul_zero, Nat.zero_add, Nat.add_zero]
        convert tail_r2 0 (w + 1) using 2; ring_nf
      · exact stepStar_stepPlus_stepPlus (hoc_star hj1)
            (by convert tail_r2 j (w + 1) using 2)
    , by omega⟩
  · exact ⟨6 * j + 4, 4 * j + w + 2, by
      rcases j.eq_zero_or_pos with rfl | hj1
      · simp only [Nat.mul_zero, Nat.zero_add, Nat.add_zero]
        convert tail_r3 0 (w + 1) using 2; ring_nf
      · exact stepStar_stepPlus_stepPlus (hoc_star hj1)
            (by convert tail_r3 j (w + 1) using 2)
    , by omega⟩
  · exact ⟨6 * j + 7, 4 * j + w + 3, by
      rcases j.eq_zero_or_pos with rfl | hj1
      · simp only [Nat.mul_zero, Nat.zero_add, Nat.add_zero]
        convert tail_r4 0 w using 2; ring_nf
      · exact stepStar_stepPlus_stepPlus (hoc_star hj1)
            (by convert tail_r4 j w using 2)
    , by omega⟩
  · exact ⟨6 * j + 8, 4 * j + w + 3, by
      rcases j.eq_zero_or_pos with rfl | hj1
      · simp only [Nat.mul_zero, Nat.zero_add, Nat.add_zero]
        convert tail_r5 0 w using 2; ring_nf
      · exact stepStar_stepPlus_stepPlus (hoc_star hj1)
            (by convert tail_r5 j w using 2)
    , by omega⟩

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨0, 5, 0, 0, 4⟩) (by execute fm 25)
  apply progress_nonhalt (fm := fm)
    (P := fun q ↦ ∃ B E, q = ⟨0, B + 2, 0, 0, E + 2⟩ ∧ 6 * E ≥ B)
  · intro q ⟨B, E, hq, hBE⟩; subst hq
    obtain ⟨B', E', hstep, hBE'⟩ := full_trans B E hBE
    exact ⟨⟨0, B' + 2, 0, 0, E' + 2⟩, ⟨B', E', rfl, hBE'⟩, hstep⟩
  · exact ⟨3, 2, rfl, by omega⟩

end Sz22_2003_unofficial_1060
