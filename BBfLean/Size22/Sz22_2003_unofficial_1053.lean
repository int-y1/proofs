import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #1053: [5/18, 2/35, 41503/2, 3/7, 2/11]

Vector representation:
```
-1 -2  1  0  0
 1  0 -1 -1  0
-1  0  0  3  2
 0  1  0 -1  0
 1  0  0  0 -1
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_1053

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a+1, b+2, c, d, e⟩ => some ⟨a, b, c+1, d, e⟩
  | ⟨a, b, c+1, d+1, e⟩ => some ⟨a+1, b, c, d, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b, c, d+3, e+2⟩
  | ⟨a, b, c, d+1, e⟩ => some ⟨a, b+1, c, d, e⟩
  | ⟨a, b, c, d, e+1⟩ => some ⟨a+1, b, c, d, e⟩
  | _ => none

theorem r3_burst_b0 : ∀ k D E,
    ⟨k, (0 : ℕ), 0, D, E⟩ [fm]⊢* ⟨0, 0, 0, D + 3 * k, E + 2 * k⟩ := by
  intro k; induction' k with k ih <;> intro D E
  · ring_nf; finish
  · rw [show D + 3 * (k + 1) = (D + 3) + 3 * k from by ring,
        show E + 2 * (k + 1) = (E + 2) + 2 * k from by ring]
    step fm; exact ih (D + 3) (E + 2)

theorem r3_burst_b1 : ∀ k D E,
    ⟨k, (1 : ℕ), 0, D, E⟩ [fm]⊢* ⟨0, 1, 0, D + 3 * k, E + 2 * k⟩ := by
  intro k; induction' k with k ih <;> intro D E
  · ring_nf; finish
  · rw [show D + 3 * (k + 1) = (D + 3) + 3 * k from by ring,
        show E + 2 * (k + 1) = (E + 2) + 2 * k from by ring]
    step fm; exact ih (D + 3) (E + 2)

theorem gen_drain_b0 : ∀ C, ∀ A D E, (C ≥ 1 → A + D ≥ 1) →
    ⟨A, (0 : ℕ), C, D, E⟩ [fm]⊢* ⟨0, 0, 0, D + 2 * C + 3 * A, E + 2 * C + 2 * A⟩ := by
  intro C; induction' C using Nat.strongRecOn with C ihC
  intro A D E hAD
  rcases C with _ | C
  · simp only [Nat.mul_zero, Nat.add_zero] at *
    exact r3_burst_b0 A D E
  · rcases D with _ | D
    · obtain ⟨A', rfl⟩ : ∃ A', A = A' + 1 := ⟨A - 1, by omega⟩
      step fm; step fm
      have h := ihC C (by omega) (A' + 1) 2 (E + 2) (fun _ => by omega)
      rw [show 0 + 2 * (C + 1) + 3 * (A' + 1) = 2 + 2 * C + 3 * (A' + 1) from by ring,
          show E + 2 * (C + 1) + 2 * (A' + 1) = E + 2 + 2 * C + 2 * (A' + 1) from by ring]
      exact h
    · step fm
      have h := ihC C (by omega) (A + 1) D E (fun _ => by omega)
      rw [show D + 1 + 2 * (C + 1) + 3 * A = D + 2 * C + 3 * (A + 1) from by ring,
          show E + 2 * (C + 1) + 2 * A = E + 2 * C + 2 * (A + 1) from by ring]
      exact h

theorem gen_drain_b1 : ∀ C, ∀ A D E, (C ≥ 1 → A + D ≥ 1) →
    ⟨A, (1 : ℕ), C, D, E⟩ [fm]⊢* ⟨0, 1, 0, D + 2 * C + 3 * A, E + 2 * C + 2 * A⟩ := by
  intro C; induction' C using Nat.strongRecOn with C ihC
  intro A D E hAD
  rcases C with _ | C
  · simp only [Nat.mul_zero, Nat.add_zero] at *
    exact r3_burst_b1 A D E
  · rcases D with _ | D
    · obtain ⟨A', rfl⟩ : ∃ A', A = A' + 1 := ⟨A - 1, by omega⟩
      step fm; step fm
      have h := ihC C (by omega) (A' + 1) 2 (E + 2) (fun _ => by omega)
      rw [show 0 + 2 * (C + 1) + 3 * (A' + 1) = 2 + 2 * C + 3 * (A' + 1) from by ring,
          show E + 2 * (C + 1) + 2 * (A' + 1) = E + 2 + 2 * C + 2 * (A' + 1) from by ring]
      exact h
    · step fm
      have h := ihC C (by omega) (A + 1) D E (fun _ => by omega)
      rw [show D + 1 + 2 * (C + 1) + 3 * A = D + 2 * C + 3 * (A + 1) from by ring,
          show E + 2 * (C + 1) + 2 * A = E + 2 * C + 2 * (A + 1) from by ring]
      exact h

theorem r4_drain : ∀ k b E,
    ⟨(0 : ℕ), b, 0, k, E⟩ [fm]⊢* ⟨0, b + k, 0, 0, E⟩ := by
  intro k; induction' k with k ih <;> intro b E
  · ring_nf; finish
  · rw [show b + (k + 1) = (b + 1) + k from by ring]
    step fm; exact ih (b + 1) E

theorem r5r1_chain : ∀ k c E,
    ⟨(0 : ℕ), 2 * k, c, 0, E + k⟩ [fm]⊢* ⟨0, 0, c + k, 0, E⟩ := by
  intro k; induction' k with k ih <;> intro c E
  · ring_nf; finish
  · rw [show 2 * (k + 1) = 2 * k + 2 from by ring,
        show E + (k + 1) = E + k + 1 from by ring,
        show c + (k + 1) = (c + 1) + k from by ring]
    step fm; step fm; exact ih (c + 1) E

theorem r5r1_chain_odd : ∀ k c E,
    ⟨(0 : ℕ), 2 * k + 1, c, 0, E + k⟩ [fm]⊢* ⟨0, 1, c + k, 0, E⟩ := by
  intro k; induction' k with k ih <;> intro c E
  · ring_nf; finish
  · rw [show 2 * (k + 1) + 1 = (2 * k + 1) + 2 from by ring,
        show E + (k + 1) = E + k + 1 from by ring,
        show c + (k + 1) = (c + 1) + k from by ring]
    step fm; step fm; exact ih (c + 1) E

theorem main_trans_odd (m w : ℕ) (hm : m ≥ 1) :
    ⟨(0 : ℕ), 2 * m + 1, 0, 0, m + 1 + w⟩ [fm]⊢⁺ ⟨0, 2 * m + 4, 0, 0, m + 1 + w + m + 1⟩ := by
  apply stepStar_stepPlus_stepPlus
  · rw [show m + 1 + w = (1 + w) + m from by ring]
    exact r5r1_chain_odd m 0 (1 + w)
  rw [show (0 : ℕ) + m = m from by ring, show 1 + w = w + 1 from by ring]
  obtain ⟨m', rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
  apply step_stepStar_stepPlus (by unfold fm; rfl)
  apply stepStar_trans
  · show (1, 1, m' + 1, 0, w) [fm]⊢* (0, 1, m' + 1, 3, w + 2)
    step fm; finish
  apply stepStar_trans
  · exact gen_drain_b1 (m' + 1) 0 3 (w + 2) (fun _ => by omega)
  apply stepStar_trans
  · exact r4_drain (3 + 2 * (m' + 1)) 1 (w + 2 + 2 * (m' + 1))
  rw [show 1 + (3 + 2 * (m' + 1)) = 2 * (m' + 1) + 4 from by ring,
      show w + 2 + 2 * (m' + 1) = m' + 1 + 1 + w + (m' + 1) + 1 from by ring]
  finish

theorem main_trans_even (m w : ℕ) :
    ⟨(0 : ℕ), 2 * (m + 1), 0, 0, m + 2 + w⟩ [fm]⊢⁺ ⟨0, 2 * m + 5, 0, 0, m + 2 + w + m + 2⟩ := by
  apply stepStar_stepPlus_stepPlus
  · rw [show m + 2 + w = (1 + w) + (m + 1) from by ring]
    exact r5r1_chain (m + 1) 0 (1 + w)
  rw [show (0 : ℕ) + (m + 1) = m + 1 from by ring, show 1 + w = w + 1 from by ring]
  apply step_stepStar_stepPlus (by unfold fm; rfl)
  apply stepStar_trans
  · show (1, 0, m + 1, 0, w) [fm]⊢* (0, 0, m + 1, 3, w + 2)
    step fm; finish
  apply stepStar_trans
  · exact gen_drain_b0 (m + 1) 0 3 (w + 2) (fun _ => by omega)
  apply stepStar_trans
  · exact r4_drain (3 + 2 * (m + 1)) 0 (w + 2 + 2 * (m + 1))
  rw [show 0 + (3 + 2 * (m + 1)) = 2 * m + 5 from by ring,
      show w + 2 + 2 * (m + 1) = m + 2 + w + m + 2 from by ring]
  finish

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨0, 3, 0, 0, 2⟩) (by execute fm 4)
  apply progress_nonhalt (fm := fm)
    (P := fun q ↦ ∃ B E, q = ⟨0, B, 0, 0, E⟩ ∧ B ≥ 3 ∧ 2 * E ≥ B + 1)
  · intro q ⟨B, E, hq, hB, hBE⟩
    subst hq
    rcases Nat.even_or_odd B with ⟨m, hm⟩ | ⟨m, hm⟩
    · have hm2 : m ≥ 2 := by omega
      have hE : E ≥ m + 1 := by omega
      obtain ⟨w, rfl⟩ := Nat.exists_eq_add_of_le hE
      obtain ⟨m', rfl⟩ : ∃ m', m = m' + 2 := ⟨m - 2, by omega⟩
      refine ⟨⟨0, 2 * (m' + 1) + 5, 0, 0, (m' + 1) + 2 + w + (m' + 1) + 2⟩,
              ⟨2 * (m' + 1) + 5, (m' + 1) + 2 + w + (m' + 1) + 2, rfl, by omega, by omega⟩, ?_⟩
      rw [hm, show (m' + 2) + (m' + 2) = 2 * ((m' + 1) + 1) from by ring,
          show (m' + 2) + 1 + w = (m' + 1) + 2 + w from by ring]
      exact main_trans_even (m' + 1) w
    · have hm1 : m ≥ 1 := by omega
      have hE : E ≥ m + 1 := by omega
      obtain ⟨w, rfl⟩ := Nat.exists_eq_add_of_le hE
      refine ⟨⟨0, 2 * m + 4, 0, 0, m + 1 + w + m + 1⟩,
              ⟨2 * m + 4, m + 1 + w + m + 1, rfl, by omega, by omega⟩, ?_⟩
      rw [hm]
      exact main_trans_odd m w hm1
  · exact ⟨3, 2, rfl, by omega, by omega⟩

end Sz22_2003_unofficial_1053
