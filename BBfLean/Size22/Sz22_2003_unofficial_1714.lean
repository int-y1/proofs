import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #1714: [77/15, 99/14, 44/3, 5/11, 3/2]

Vector representation:
```
 0 -1 -1  1  1
-1  2  0 -1  1
 2 -1  0  0  1
 0  0  1  0 -1
-1  1  0  0  0
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6 (1M context)
-/

namespace Sz22_2003_unofficial_1714

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a, b+1, c+1, d, e⟩ => some ⟨a, b, c, d+1, e+1⟩
  | ⟨a+1, b, c, d+1, e⟩ => some ⟨a, b+2, c, d, e+1⟩
  | ⟨a, b+1, c, d, e⟩ => some ⟨a+2, b, c, d, e+1⟩
  | ⟨a, b, c, d, e+1⟩ => some ⟨a, b, c+1, d, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b+1, c, d, e⟩
  | _ => none

theorem e_to_c : ∀ k, ∀ A C,
    ⟨A, 0, C, 0, k⟩ [fm]⊢* ⟨A, 0, C + k, 0, 0⟩ := by
  intro k; induction' k with k ih <;> intro A C
  · exists 0
  · step fm
    apply stepStar_trans (ih A (C + 1))
    rw [show C + 1 + k = C + (k + 1) from by ring]; finish

theorem r3_chain : ∀ k, ∀ A E,
    ⟨A, k, 0, 0, E⟩ [fm]⊢* ⟨A + 2 * k, 0, 0, 0, E + k⟩ := by
  intro k; induction' k with k ih <;> intro A E
  · exists 0
  · step fm
    apply stepStar_trans (ih (A + 2) (E + 1))
    rw [show A + 2 + 2 * k = A + 2 * (k + 1) from by ring,
        show E + 1 + k = E + (k + 1) from by ring]; finish

theorem r2r1r1_chain : ∀ k, ∀ A C D E,
    ⟨A + k, 0, C + 2 * k, D + 1, E⟩ [fm]⊢* ⟨A, 0, C, D + k + 1, E + 3 * k⟩ := by
  intro k; induction' k with k ih <;> intro A C D E
  · simp; exists 0
  · rw [show A + (k + 1) = (A + k) + 1 from by ring,
        show C + 2 * (k + 1) = (C + 2 * k + 1) + 1 from by ring]
    step fm
    rw [show C + 2 * k + 1 + 1 = (C + 2 * k) + 1 + 1 from by ring]
    step fm
    step fm
    apply stepStar_trans (ih A C (D + 1) (E + 3))
    rw [show D + 1 + k + 1 = D + (k + 1) + 1 from by ring,
        show E + 3 + 3 * k = E + 3 * (k + 1) from by ring]; finish

theorem drain : ∀ D, ∀ A B E, (D = 0 ∨ A + B ≥ 1) →
    ⟨A, B, 0, D, E⟩ [fm]⊢* ⟨A + 2 * B + 3 * D, 0, 0, 0, E + B + 3 * D⟩ := by
  intro D; induction' D using Nat.strongRecOn with D ih; intro A B E hpre
  rcases D with _ | D
  · rw [show A + 2 * B + 3 * 0 = A + 2 * B from by ring,
        show E + B + 3 * 0 = E + B from by ring]
    exact r3_chain B A E
  · rcases A with _ | A
    · rcases B with _ | B
      · exfalso; omega
      · step fm
        rw [show (2 : ℕ) = 1 + 1 from rfl]
        step fm
        have := ih D (by omega) 1 (B + 2) (E + 2) (by right; omega)
        rw [show 1 + 2 * (B + 2) + 3 * D = 0 + 2 * (B + 1) + 3 * (D + 1) from by ring,
            show E + 2 + (B + 2) + 3 * D = E + (B + 1) + 3 * (D + 1) from by ring] at this
        exact this
    · step fm
      have := ih D (by omega) A (B + 2) (E + 1) (by right; omega)
      rw [show A + 2 * (B + 2) + 3 * D = (A + 1) + 2 * B + 3 * (D + 1) from by ring,
          show E + 1 + (B + 2) + 3 * D = E + B + 3 * (D + 1) from by ring] at this
      exact this

theorem main_trans_odd (m k : ℕ) :
    ⟨m + k + 2, 0, 2 * k + 1, 0, 0⟩ [fm]⊢⁺ ⟨m + 3 * k + 4, 0, 6 * k + 4, 0, 0⟩ := by
  have p1 : ⟨m + k + 2, 0, 2 * k + 1, 0, 0⟩ [fm]⊢⁺
      ⟨m + k + 1, 0, 2 * k, 1, 1⟩ := by
    rw [show m + k + 2 = (m + k + 1) + 1 from by ring,
        show 2 * k + 1 = (2 * k) + 1 from by ring]
    step fm; step fm; ring_nf; finish
  have p2 : ⟨m + k + 1, 0, 2 * k, 1, 1⟩ [fm]⊢*
      ⟨m + 1, 0, 0, k + 1, 3 * k + 1⟩ := by
    have h := r2r1r1_chain k (m + 1) 0 0 1
    rw [show m + 1 + k = m + k + 1 from by ring,
        show 0 + 2 * k = 2 * k from by ring,
        show 0 + k + 1 = k + 1 from by ring,
        show 1 + 3 * k = 3 * k + 1 from by ring] at h
    exact h
  have p3 : ⟨m + 1, 0, 0, k + 1, 3 * k + 1⟩ [fm]⊢*
      ⟨m + 3 * k + 4, 0, 0, 0, 6 * k + 4⟩ := by
    have h := drain (k + 1) (m + 1) 0 (3 * k + 1) (by right; omega)
    rw [show m + 1 + 2 * 0 + 3 * (k + 1) = m + 3 * k + 4 from by ring,
        show 3 * k + 1 + 0 + 3 * (k + 1) = 6 * k + 4 from by ring] at h
    exact h
  have p4 : ⟨m + 3 * k + 4, 0, 0, 0, 6 * k + 4⟩ [fm]⊢*
      ⟨m + 3 * k + 4, 0, 6 * k + 4, 0, 0⟩ := by
    have h := e_to_c (6 * k + 4) (m + 3 * k + 4) 0
    simp only [Nat.zero_add] at h; exact h
  exact stepPlus_stepStar_stepPlus p1
    (stepStar_trans p2 (stepStar_trans p3 p4))

theorem main_trans_even (m k : ℕ) :
    ⟨m + k + 3, 0, 2 * (k + 1), 0, 0⟩ [fm]⊢⁺ ⟨m + 3 * k + 6, 0, 6 * k + 7, 0, 0⟩ := by
  have p1 : ⟨m + k + 3, 0, 2 * (k + 1), 0, 0⟩ [fm]⊢⁺
      ⟨m + k + 2, 0, 2 * k + 1, 1, 1⟩ := by
    rw [show m + k + 3 = (m + k + 2) + 1 from by ring,
        show 2 * (k + 1) = (2 * k + 1) + 1 from by ring]
    step fm; step fm; ring_nf; finish
  have p2 : ⟨m + k + 2, 0, 2 * k + 1, 1, 1⟩ [fm]⊢*
      ⟨m + 2, 0, 1, k + 1, 3 * k + 1⟩ := by
    have h := r2r1r1_chain k (m + 2) 1 0 1
    rw [show m + 2 + k = m + k + 2 from by ring,
        show 1 + 2 * k = 2 * k + 1 from by ring,
        show 0 + k + 1 = k + 1 from by ring,
        show 1 + 3 * k = 3 * k + 1 from by ring] at h
    exact h
  have p3 : ⟨m + 2, 0, 1, k + 1, 3 * k + 1⟩ [fm]⊢*
      ⟨m + 1, 1, 0, k + 1, 3 * k + 3⟩ := by
    rw [show m + 2 = (m + 1) + 1 from by ring]
    step fm
    rw [show (2 : ℕ) = 1 + 1 from rfl,
        show (1 : ℕ) = 0 + 1 from rfl]
    step fm
    ring_nf; finish
  have p4 : ⟨m + 1, 1, 0, k + 1, 3 * k + 3⟩ [fm]⊢*
      ⟨m + 3 * k + 6, 0, 0, 0, 6 * k + 7⟩ := by
    have h := drain (k + 1) (m + 1) 1 (3 * k + 3) (by right; omega)
    rw [show m + 1 + 2 * 1 + 3 * (k + 1) = m + 3 * k + 6 from by ring,
        show 3 * k + 3 + 1 + 3 * (k + 1) = 6 * k + 7 from by ring] at h
    exact h
  have p5 : ⟨m + 3 * k + 6, 0, 0, 0, 6 * k + 7⟩ [fm]⊢*
      ⟨m + 3 * k + 6, 0, 6 * k + 7, 0, 0⟩ := by
    have h := e_to_c (6 * k + 7) (m + 3 * k + 6) 0
    simp only [Nat.zero_add] at h; exact h
  exact stepPlus_stepStar_stepPlus p1
    (stepStar_trans p2 (stepStar_trans p3 (stepStar_trans p4 p5)))

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨2, 0, 1, 0, 0⟩) (by execute fm 3)
  apply progress_nonhalt (fm := fm)
    (P := fun q ↦ ∃ m k, q = ⟨m + k + 2, 0, 2 * k + 1, 0, 0⟩ ∨
                          q = ⟨m + k + 3, 0, 2 * (k + 1), 0, 0⟩)
  · intro q ⟨m, k, hq⟩
    rcases hq with hq | hq
    · subst hq
      refine ⟨⟨m + 3 * k + 4, 0, 6 * k + 4, 0, 0⟩,
             ⟨m, 3 * k + 1, Or.inr ?_⟩, ?_⟩
      · show (m + 3 * k + 4, 0, 6 * k + 4, 0, 0) =
              (m + (3 * k + 1) + 3, 0, 2 * ((3 * k + 1) + 1), 0, 0)
        ring_nf
      · exact main_trans_odd m k
    · subst hq
      refine ⟨⟨m + 3 * k + 6, 0, 6 * k + 7, 0, 0⟩,
             ⟨m + 1, 3 * k + 3, Or.inl ?_⟩, ?_⟩
      · show (m + 3 * k + 6, 0, 6 * k + 7, 0, 0) =
              ((m + 1) + (3 * k + 3) + 2, 0, 2 * (3 * k + 3) + 1, 0, 0)
        ring_nf
      · exact main_trans_even m k
  · exact ⟨0, 0, Or.inl (by ring_nf)⟩

end Sz22_2003_unofficial_1714
