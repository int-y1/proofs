import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #1074: [5/6, 196/55, 121/2, 3/7, 15/11]

Vector representation:
```
-1 -1  1  0  0
 2  0 -1  2 -1
-1  0  0  0  2
 0  1  0 -1  0
 0  1  1  0 -1
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_1074

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a+1, b+1, c, d, e⟩ => some ⟨a, b, c+1, d, e⟩
  | ⟨a, b, c+1, d, e+1⟩ => some ⟨a+2, b, c, d+2, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b, c, d, e+2⟩
  | ⟨a, b, c, d+1, e⟩ => some ⟨a, b+1, c, d, e⟩
  | ⟨a, b, c, d, e+1⟩ => some ⟨a, b+1, c+1, d, e⟩
  | _ => none

private theorem r4_chain : ∀ k, ∀ b d e,
    ⟨(0 : ℕ), b, 0, d + k, e⟩ [fm]⊢* ⟨0, b + k, 0, d, e⟩ := by
  intro k; induction' k with k ih <;> intro b d e
  · ring_nf; finish
  · rw [show d + (k + 1) = (d + k) + 1 from by ring,
        show b + (k + 1) = (b + 1) + k from by ring]
    step fm; exact ih (b + 1) d e

private theorem r3_drain : ∀ k, ∀ d e,
    ⟨k, (0 : ℕ), 0, d, e⟩ [fm]⊢* ⟨0, 0, 0, d, e + 2 * k⟩ := by
  intro k; induction' k with k ih <;> intro d e
  · ring_nf; finish
  · rw [show e + 2 * (k + 1) = (e + 2) + 2 * k from by ring]
    step fm; exact ih d (e + 2)

private theorem r2r1r1_chain : ∀ k, ∀ c d e,
    ⟨(0 : ℕ), 2 * k, c + 1, d, e + k⟩ [fm]⊢* ⟨0, 0, c + 1 + k, d + 2 * k, e⟩ := by
  intro k; induction' k with k ih <;> intro c d e
  · ring_nf; finish
  · rw [show c + 1 + (k + 1) = (c + 1) + 1 + k from by ring,
        show d + 2 * (k + 1) = (d + 2) + 2 * k from by ring]
    have h1 : ⟨(0 : ℕ), 2 * (k + 1), c + 1, d, e + (k + 1)⟩ [fm]⊢*
              ⟨0, 2 * k, (c + 1) + 1, d + 2, e + k⟩ := by
      rw [show 2 * (k + 1) = 2 * k + 2 from by ring,
          show e + (k + 1) = (e + k) + 1 from by ring]
      step fm; step fm; step fm; ring_nf; finish
    exact stepStar_trans h1 (ih (c + 1) (d + 2) e)

private theorem r2r1_odd : ∀ k, ∀ c d e,
    ⟨(0 : ℕ), 2 * k + 1, c + 1, d, e + k + 1⟩ [fm]⊢*
    ⟨1, 0, c + 1 + k, d + 2 * k + 2, e⟩ := by
  intro k; induction' k with k ih <;> intro c d e
  · rw [show e + 0 + 1 = e + 1 from by ring,
        show d + 2 * 0 + 2 = d + 2 from by ring,
        show c + 1 + 0 = c + 1 from by ring]
    step fm; step fm; ring_nf; finish
  · rw [show c + 1 + (k + 1) = (c + 1) + 1 + k from by ring,
        show d + 2 * (k + 1) + 2 = (d + 2) + 2 * k + 2 from by ring]
    have h1 : ⟨(0 : ℕ), 2 * (k + 1) + 1, c + 1, d, e + (k + 1) + 1⟩ [fm]⊢*
              ⟨0, 2 * k + 1, (c + 1) + 1, d + 2, e + k + 1⟩ := by
      rw [show 2 * (k + 1) + 1 = 2 * k + 1 + 2 from by ring,
          show e + (k + 1) + 1 = (e + k + 1) + 1 from by ring]
      step fm; step fm; step fm; ring_nf; finish
    exact stepStar_trans h1 (ih (c + 1) (d + 2) e)

private theorem r3r2_helper : ∀ a d,
    ⟨a + 1, (0 : ℕ), 1, d, 0⟩ [fm]⊢* ⟨a + 2, 0, 0, d + 2, 1⟩ := by
  intro a d; step fm; step fm; ring_nf; finish

private theorem r3r2r2_helper : ∀ a c d,
    ⟨a + 1, (0 : ℕ), c + 2, d, 0⟩ [fm]⊢* ⟨a + 4, 0, c, d + 4, 0⟩ := by
  intro a c d; step fm; step fm; step fm; ring_nf; finish

private theorem r2_helper : ∀ a c d e,
    ⟨a, (0 : ℕ), c + 1, d, e + 1⟩ [fm]⊢* ⟨a + 2, 0, c, d + 2, e⟩ := by
  intro a c d e; step fm; ring_nf; finish

private theorem combined_drain : ∀ S, ∀ A C D E,
    C + E = S →
    (E ≥ 1 ∨ A ≥ 1 ∨ C = 0) →
    ⟨A, (0 : ℕ), C, D, E⟩ [fm]⊢* ⟨0, 0, 0, D + 2 * C, E + 3 * C + 2 * A⟩ := by
  intro S; induction' S using Nat.strongRecOn with S IH
  intro A C D E hS hcond
  rcases C with _ | C
  · simp only [Nat.mul_zero, Nat.add_zero]; exact r3_drain A D E
  rcases E with _ | E
  · have hA : A ≥ 1 := by omega
    obtain ⟨a, ha⟩ := Nat.exists_eq_add_of_le hA
    rw [show A = a + 1 from by omega]
    rcases C with _ | C
    · have := stepStar_trans (r3r2_helper a D) (r3_drain (a + 2) (D + 2) 1)
      convert this using 2; all_goals ring_nf
    · rw [show C + 1 + 1 = C + 2 from by ring]
      have := stepStar_trans (r3r2r2_helper a C D)
        (IH (C + 0) (by omega) (a + 4) C (D + 4) 0 (by ring) (by omega))
      convert this using 2; all_goals ring_nf
  · have := stepStar_trans (r2_helper A C D E)
      (IH (C + E) (by omega) (A + 2) C (D + 2) E (by ring) (by omega))
    convert this using 2; all_goals ring_nf

private theorem even_tail_zero (m d : ℕ) :
    ⟨(1 : ℕ), 0, m + 1, d, 0⟩ [fm]⊢* ⟨0, 0, 0, d + 2 * m + 2, 3 * m + 5⟩ := by
  have h1 : ⟨(1 : ℕ), 0, m + 1, d, 0⟩ [fm]⊢* ⟨0, 0, m + 1, d, 2⟩ := by
    step fm; ring_nf; finish
  have h2 := combined_drain ((m + 1) + 2) 0 (m + 1) d 2 (by ring) (by omega)
  convert stepStar_trans h1 h2 using 2; ring_nf

private theorem even_tail_succ (m d E : ℕ) :
    ⟨(1 : ℕ), 0, m + 1, d, E + 1⟩ [fm]⊢* ⟨0, 0, 0, d + 2 * m + 2, E + 3 * m + 6⟩ := by
  have h1 : ⟨(1 : ℕ), 0, m + 1, d, E + 1⟩ [fm]⊢* ⟨3, 0, m, d + 2, E⟩ := by
    step fm; ring_nf; finish
  have h2 := combined_drain (m + E) 3 m (d + 2) E (by ring) (by omega)
  convert stepStar_trans h1 h2 using 2; ring_nf

private theorem even_tail (m d E : ℕ) :
    ⟨(1 : ℕ), 0, m + 1, d, E⟩ [fm]⊢* ⟨0, 0, 0, d + 2 * m + 2, E + 3 * m + 5⟩ := by
  rcases E with _ | E
  · convert even_tail_zero m d using 2; ring_nf
  · convert even_tail_succ m d E using 2; ring_nf

private theorem main_trans_even (m E : ℕ) :
    ⟨(0 : ℕ), 0, 0, 2 * m, E + m + 2⟩ [fm]⊢⁺ ⟨0, 0, 0, 4 * m + 4, E + 3 * m + 5⟩ := by
  have h_r4 : ⟨(0 : ℕ), 0, 0, 2 * m, E + m + 2⟩ [fm]⊢* ⟨0, 2 * m, 0, 0, E + m + 2⟩ := by
    convert r4_chain (2 * m) 0 0 (E + m + 2) using 2; ring_nf
  have h_odd : ⟨(0 : ℕ), 2 * m + 1, 1, 0, E + m + 1⟩ [fm]⊢*
      ⟨1, 0, m + 1, 2 * m + 2, E⟩ := by
    convert r2r1_odd m 0 0 E using 2; ring_nf
  have h_tail := even_tail m (2 * m + 2) E
  apply stepStar_stepPlus_stepPlus h_r4
  rw [show E + m + 2 = (E + m + 1) + 1 from by ring]
  apply step_stepStar_stepPlus
  · show fm ⟨(0 : ℕ), 2 * m, 0, 0, (E + m + 1) + 1⟩ =
         some ⟨0, 2 * m + 1, 1, 0, E + m + 1⟩; rfl
  convert stepStar_trans h_odd h_tail using 2; ring_nf

private theorem main_trans_odd (m E : ℕ) :
    ⟨(0 : ℕ), 0, 0, 2 * m + 1, E + m + 3⟩ [fm]⊢⁺ ⟨0, 0, 0, 4 * m + 6, E + 3 * m + 7⟩ := by
  have h_r4 : ⟨(0 : ℕ), 0, 0, 2 * m + 1, E + m + 3⟩ [fm]⊢* ⟨0, 2 * m + 1, 0, 0, E + m + 3⟩ := by
    convert r4_chain (2 * m + 1) 0 0 (E + m + 3) using 2; ring_nf
  have h_even : ⟨(0 : ℕ), 2 * m + 2, 1, 0, (E + 1) + (m + 1)⟩ [fm]⊢*
      ⟨0, 0, m + 2, 2 * m + 2, E + 1⟩ := by
    convert r2r1r1_chain (m + 1) 0 0 (E + 1) using 2; ring_nf
  have h_drain := combined_drain ((m + 2) + (E + 1)) 0 (m + 2) (2 * m + 2) (E + 1)
    (by ring) (by omega)
  apply stepStar_stepPlus_stepPlus h_r4
  rw [show E + m + 3 = ((E + 1) + (m + 1)) + 1 from by ring]
  apply step_stepStar_stepPlus
  · show fm ⟨(0 : ℕ), 2 * m + 1, 0, 0, ((E + 1) + (m + 1)) + 1⟩ =
         some ⟨0, 2 * m + 2, 1, 0, (E + 1) + (m + 1)⟩; rfl
  convert stepStar_trans h_even h_drain using 2; ring_nf

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨0, 0, 0, 0, 2⟩) (by execute fm 1)
  apply progress_nonhalt (fm := fm)
    (P := fun q ↦ ∃ d e, q = ⟨0, 0, 0, d, e⟩ ∧ 2 * e ≥ d + 4)
  · intro q ⟨d, e, hq, hinv⟩
    subst hq
    rcases Nat.even_or_odd d with ⟨m, hm⟩ | ⟨m, hm⟩
    · subst hm
      have he : e ≥ m + 2 := by omega
      obtain ⟨E, hE⟩ := Nat.exists_eq_add_of_le he
      subst hE
      refine ⟨⟨0, 0, 0, 4 * m + 4, E + 3 * m + 5⟩,
             ⟨4 * m + 4, E + 3 * m + 5, rfl, by omega⟩, ?_⟩
      convert main_trans_even m E using 2; ring_nf
    · subst hm
      have he : e ≥ m + 3 := by omega
      obtain ⟨E, hE⟩ := Nat.exists_eq_add_of_le he
      subst hE
      refine ⟨⟨0, 0, 0, 4 * m + 6, E + 3 * m + 7⟩,
             ⟨4 * m + 6, E + 3 * m + 7, rfl, by omega⟩, ?_⟩
      convert main_trans_odd m E using 2; ring_nf
  · exact ⟨0, 2, rfl, by omega⟩

end Sz22_2003_unofficial_1074
