import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #1076: [5/6, 196/55, 121/2, 3/7, 35/11]

Vector representation:
```
-1 -1  1  0  0
 2  0 -1  2 -1
-1  0  0  0  2
 0  1  0 -1  0
 0  0  1  1 -1
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_1076

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a+1, b+1, c, d, e⟩ => some ⟨a, b, c+1, d, e⟩
  | ⟨a, b, c+1, d, e+1⟩ => some ⟨a+2, b, c, d+2, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b, c, d, e+2⟩
  | ⟨a, b, c, d+1, e⟩ => some ⟨a, b+1, c, d, e⟩
  | ⟨a, b, c, d, e+1⟩ => some ⟨a, b, c+1, d+1, e⟩
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

private theorem main_trans_even (m r : ℕ) :
    ⟨(0 : ℕ), 0, 0, 2 * m, r + m + 2⟩ [fm]⊢⁺ ⟨0, 0, 0, 4 * m + 3, r + 3 * m + 4⟩ := by
  have h1 : ⟨(0 : ℕ), 0, 0, 2 * m, r + m + 2⟩ [fm]⊢* ⟨0, 2 * m, 0, 0, r + m + 2⟩ := by
    convert r4_chain (2 * m) 0 0 (r + m + 2) using 2; ring_nf
  have hstep : fm ⟨(0 : ℕ), 2 * m, 0, 0, r + m + 2⟩ =
    some ⟨0, 2 * m, 1, 1, r + m + 1⟩ := by
    rw [show r + m + 2 = (r + m + 1) + 1 from by ring]; rfl
  have h2 : ⟨(0 : ℕ), 2 * m, 1, 1, r + m + 1⟩ [fm]⊢*
             ⟨0, 0, m + 1, 2 * m + 1, r + 1⟩ := by
    convert r2r1r1_chain m 0 1 (r + 1) using 2; all_goals ring_nf
  have h3 := combined_drain ((m + 1) + (r + 1)) 0 (m + 1) (2 * m + 1) (r + 1)
    (by ring) (by omega)
  have hfull := stepStar_trans h1
    (stepStar_trans (step_stepStar hstep) (stepStar_trans h2 h3))
  have hne : (⟨(0 : ℕ), 0, 0, 2 * m, r + m + 2⟩ : Q) ≠
    ⟨0, 0, 0, 2 * m + 1 + 2 * (m + 1), r + 1 + 3 * (m + 1) + 2 * 0⟩ := by
    intro h; simp only [Prod.mk.injEq] at h; omega
  have hplus := stepStar_stepPlus hfull hne
  convert hplus using 2; all_goals ring_nf

private theorem main_trans_odd (m r : ℕ) :
    ⟨(0 : ℕ), 0, 0, 2 * m + 1, r + m + 2⟩ [fm]⊢⁺ ⟨0, 0, 0, 4 * m + 5, r + 3 * m + 5⟩ := by
  have h1 : ⟨(0 : ℕ), 0, 0, 2 * m + 1, r + m + 2⟩ [fm]⊢* ⟨0, 2 * m + 1, 0, 0, r + m + 2⟩ := by
    convert r4_chain (2 * m + 1) 0 0 (r + m + 2) using 2; ring_nf
  have hstep : fm ⟨(0 : ℕ), 2 * m + 1, 0, 0, r + m + 2⟩ =
    some ⟨0, 2 * m + 1, 1, 1, r + m + 1⟩ := by
    rw [show r + m + 2 = (r + m + 1) + 1 from by ring]; rfl
  have h2 : ⟨(0 : ℕ), 2 * m + 1, 1, 1, r + m + 1⟩ [fm]⊢*
             ⟨1, 0, m + 1, 2 * m + 3, r⟩ := by
    convert r2r1_odd m 0 1 r using 2; all_goals ring_nf
  have h3 := combined_drain ((m + 1) + r) 1 (m + 1) (2 * m + 3) r
    (by ring) (by omega)
  have hfull := stepStar_trans h1
    (stepStar_trans (step_stepStar hstep) (stepStar_trans h2 h3))
  have hne : (⟨(0 : ℕ), 0, 0, 2 * m + 1, r + m + 2⟩ : Q) ≠
    ⟨0, 0, 0, 2 * m + 3 + 2 * (m + 1), r + 3 * (m + 1) + 2 * 1⟩ := by
    intro h; simp only [Prod.mk.injEq] at h; omega
  have hplus := stepStar_stepPlus hfull hne
  convert hplus using 2; all_goals ring_nf

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨0, 0, 0, 0, 2⟩) (by execute fm 1)
  apply progress_nonhalt (fm := fm)
    (P := fun q ↦ ∃ d e, q = ⟨0, 0, 0, d, e⟩ ∧ 2 * e ≥ d + 3)
  · intro q ⟨d, e, hq, hinv⟩
    subst hq
    rcases Nat.even_or_odd d with ⟨m, hm⟩ | ⟨m, hm⟩
    · rw [show d = 2 * m from by omega] at hinv ⊢
      have he : e ≥ m + 2 := by omega
      obtain ⟨r, hr⟩ : ∃ r, e = r + m + 2 := ⟨e - m - 2, by omega⟩
      subst hr
      refine ⟨⟨0, 0, 0, 4 * m + 3, r + 3 * m + 4⟩,
             ⟨4 * m + 3, r + 3 * m + 4, rfl, by omega⟩, ?_⟩
      exact main_trans_even m r
    · rw [show d = 2 * m + 1 from by omega] at hinv ⊢
      have he : e ≥ m + 2 := by omega
      obtain ⟨r, hr⟩ : ∃ r, e = r + m + 2 := ⟨e - m - 2, by omega⟩
      subst hr
      refine ⟨⟨0, 0, 0, 4 * m + 5, r + 3 * m + 5⟩,
             ⟨4 * m + 5, r + 3 * m + 5, rfl, by omega⟩, ?_⟩
      exact main_trans_odd m r
  · exact ⟨0, 2, rfl, by omega⟩

end Sz22_2003_unofficial_1076
