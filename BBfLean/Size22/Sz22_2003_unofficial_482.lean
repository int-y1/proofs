import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #482: [28/15, 3/22, 175/2, 11/7, 14/5]

Vector representation:
```
 2 -1 -1  1  0
-1  1  0  0 -1
-1  0  2  1  0
 0  0  0 -1  1
 1  0 -1  1  0
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_482

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a, b+1, c+1, d, e⟩ => some ⟨a+2, b, c, d+1, e⟩
  | ⟨a+1, b, c, d, e+1⟩ => some ⟨a, b+1, c, d, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b, c+2, d+1, e⟩
  | ⟨a, b, c, d+1, e⟩ => some ⟨a, b, c, d, e+1⟩
  | ⟨a, b, c+1, d, e⟩ => some ⟨a+1, b, c, d+1, e⟩
  | _ => none

theorem r4_chain : ∀ k, ∀ c d e, ⟨0, 0, c, d + k, e⟩ [fm]⊢* ⟨0, 0, c, d, e + k⟩ := by
  intro k; induction' k with k ih <;> intro c d e
  · exists 0
  rw [show d + (k + 1) = (d + k) + 1 from by ring]
  step fm; apply stepStar_trans (ih c d (e + 1)); ring_nf; finish

theorem r5r2r1_chain : ∀ k, ∀ a d e,
    ⟨a + 1, 0, k, d, e + k⟩ [fm]⊢* ⟨a + k + 1, 0, 0, d + k, e⟩ := by
  intro k; induction' k with k ih <;> intro a d e
  · exists 0
  rw [show e + (k + 1) = (e + k) + 1 from by ring]
  step fm; step fm; apply stepStar_trans (ih (a + 1) (d + 1) e); ring_nf; finish

theorem r2_chain : ∀ k, ∀ a b d,
    ⟨a + k, b, 0, d, k⟩ [fm]⊢* ⟨a, b + k, 0, d, 0⟩ := by
  intro k; induction' k with k ih <;> intro a b d
  · exists 0
  rw [show a + (k + 1) = (a + k) + 1 from by ring]
  step fm; apply stepStar_trans (ih a (b + 1) d); ring_nf; finish

theorem r3r1r1_chain : ∀ k, ∀ A D,
    ⟨A + 1, 2 * k, 0, D, 0⟩ [fm]⊢* ⟨A + 3 * k + 1, 0, 0, D + 3 * k, 0⟩ := by
  intro k; induction' k with k ih <;> intro A D
  · simp; exists 0
  rw [show 2 * (k + 1) = 2 * k + 2 from by ring]
  step fm; step fm; step fm; apply stepStar_trans (ih (A + 3) (D + 3)); ring_nf; finish

theorem r3r1r1_chain_odd : ∀ k, ∀ A D,
    ⟨A + 1, 2 * k + 1, 0, D, 0⟩ [fm]⊢* ⟨A + 3 * k + 1, 1, 0, D + 3 * k, 0⟩ := by
  intro k; induction' k with k ih <;> intro A D
  · simp; exists 0
  rw [show 2 * (k + 1) + 1 = 2 * k + 1 + 2 from by ring]
  step fm; step fm; step fm; apply stepStar_trans (ih (A + 3) (D + 3)); ring_nf; finish

theorem b1_tail (A D : ℕ) :
    ⟨A + 1, 1, 0, D, 0⟩ [fm]⊢* ⟨A + 1, 0, 3, D + 3, 0⟩ := by
  step fm; step fm; step fm; ring_nf; finish

theorem r3_chain : ∀ k, ∀ c D,
    ⟨k, 0, c, D, 0⟩ [fm]⊢* ⟨0, 0, c + 2 * k, D + k, 0⟩ := by
  intro k; induction' k with k ih <;> intro c D
  · exists 0
  step fm; apply stepStar_trans (ih (c + 2) (D + 1)); ring_nf; finish

-- Odd case: (0, 0, A+2K+2, A+4K+2, 0) ⊢⁺ (0, 0, 2A+6K+5, 2A+8K+6, 0)
theorem main_odd (A K : ℕ) :
    ⟨0, 0, A + 2 * K + 2, A + 4 * K + 2, 0⟩ [fm]⊢⁺
    ⟨0, 0, 2 * A + 6 * K + 5, 2 * A + 8 * K + 6, 0⟩ := by
  apply step_stepStar_stepPlus
  · show fm ⟨0, 0, A + 2 * K + 2, (A + 4 * K + 1) + 1, 0⟩ =
      some ⟨0, 0, A + 2 * K + 2, A + 4 * K + 1, 1⟩
    simp [fm]
  have phase1 : ⟨0, 0, A + 2 * K + 2, A + 4 * K + 1, 1⟩ [fm]⊢*
      ⟨0, 0, A + 2 * K + 2, 0, A + 4 * K + 2⟩ := by
    have h := r4_chain (A + 4 * K + 1) (A + 2 * K + 2) 0 1
    rw [show 0 + (A + 4 * K + 1) = A + 4 * K + 1 from by ring,
        show 1 + (A + 4 * K + 1) = A + 4 * K + 2 from by ring] at h; exact h
  have phase2 : ⟨0, 0, A + 2 * K + 2, 0, A + 4 * K + 2⟩ [fm]⊢*
      ⟨A + 2 * K + 2, 0, 0, A + 2 * K + 2, 2 * K + 1⟩ := by
    rw [show A + 2 * K + 2 = (A + 2 * K + 1) + 1 from by ring,
        show A + 4 * K + 2 = (2 * K + 1) + (A + 2 * K + 1) from by ring]
    step fm
    have h := r5r2r1_chain (A + 2 * K + 1) 0 1 (2 * K + 1)
    rw [show 0 + (A + 2 * K + 1) + 1 = A + 2 * K + 2 from by ring,
        show 1 + (A + 2 * K + 1) = A + 2 * K + 2 from by ring] at h; exact h
  have phase3 : ⟨A + 2 * K + 2, 0, 0, A + 2 * K + 2, 2 * K + 1⟩ [fm]⊢*
      ⟨A + 1, 2 * K + 1, 0, A + 2 * K + 2, 0⟩ := by
    have h := r2_chain (2 * K + 1) (A + 1) 0 (A + 2 * K + 2)
    rw [show A + 1 + (2 * K + 1) = A + 2 * K + 2 from by ring,
        show 0 + (2 * K + 1) = 2 * K + 1 from by ring] at h; exact h
  have phase4a : ⟨A + 1, 2 * K + 1, 0, A + 2 * K + 2, 0⟩ [fm]⊢*
      ⟨A + 3 * K + 1, 1, 0, A + 5 * K + 2, 0⟩ := by
    have h := r3r1r1_chain_odd K A (A + 2 * K + 2)
    rw [show A + 2 * K + 2 + 3 * K = A + 5 * K + 2 from by ring] at h; exact h
  have phase4b : ⟨A + 3 * K + 1, 1, 0, A + 5 * K + 2, 0⟩ [fm]⊢*
      ⟨A + 3 * K + 1, 0, 3, A + 5 * K + 5, 0⟩ := by
    have h := b1_tail (A + 3 * K) (A + 5 * K + 2)
    rw [show A + 3 * K + 1 = A + 3 * K + 1 from rfl] at h; exact h
  have phase5 : ⟨A + 3 * K + 1, 0, 3, A + 5 * K + 5, 0⟩ [fm]⊢*
      ⟨0, 0, 2 * A + 6 * K + 5, 2 * A + 8 * K + 6, 0⟩ := by
    have h := r3_chain (A + 3 * K + 1) 3 (A + 5 * K + 5)
    rw [show 3 + 2 * (A + 3 * K + 1) = 2 * A + 6 * K + 5 from by ring,
        show A + 5 * K + 5 + (A + 3 * K + 1) = 2 * A + 8 * K + 6 from by ring] at h; exact h
  exact stepStar_trans (stepStar_trans (stepStar_trans (stepStar_trans (stepStar_trans
    phase1 phase2) phase3) phase4a) phase4b) phase5

-- Even case: (0, 0, A+2K+1, A+4K, 0) ⊢⁺ (0, 0, 2A+6K+2, 2A+8K+2, 0), K ≥ 1
theorem main_even (A K : ℕ) :
    ⟨0, 0, A + 2 * K + 3, A + 4 * K + 4, 0⟩ [fm]⊢⁺
    ⟨0, 0, 2 * A + 6 * K + 8, 2 * A + 8 * K + 10, 0⟩ := by
  apply step_stepStar_stepPlus
  · show fm ⟨0, 0, A + 2 * K + 3, (A + 4 * K + 3) + 1, 0⟩ =
      some ⟨0, 0, A + 2 * K + 3, A + 4 * K + 3, 1⟩
    simp [fm]
  have phase1 : ⟨0, 0, A + 2 * K + 3, A + 4 * K + 3, 1⟩ [fm]⊢*
      ⟨0, 0, A + 2 * K + 3, 0, A + 4 * K + 4⟩ := by
    have h := r4_chain (A + 4 * K + 3) (A + 2 * K + 3) 0 1
    rw [show 0 + (A + 4 * K + 3) = A + 4 * K + 3 from by ring,
        show 1 + (A + 4 * K + 3) = A + 4 * K + 4 from by ring] at h; exact h
  have phase2 : ⟨0, 0, A + 2 * K + 3, 0, A + 4 * K + 4⟩ [fm]⊢*
      ⟨A + 2 * K + 3, 0, 0, A + 2 * K + 3, 2 * K + 2⟩ := by
    rw [show A + 2 * K + 3 = (A + 2 * K + 2) + 1 from by ring,
        show A + 4 * K + 4 = (2 * K + 2) + (A + 2 * K + 2) from by ring]
    step fm
    have h := r5r2r1_chain (A + 2 * K + 2) 0 1 (2 * K + 2)
    rw [show 0 + (A + 2 * K + 2) + 1 = A + 2 * K + 3 from by ring,
        show 1 + (A + 2 * K + 2) = A + 2 * K + 3 from by ring] at h; exact h
  have phase3 : ⟨A + 2 * K + 3, 0, 0, A + 2 * K + 3, 2 * K + 2⟩ [fm]⊢*
      ⟨A + 1, 2 * K + 2, 0, A + 2 * K + 3, 0⟩ := by
    have h := r2_chain (2 * K + 2) (A + 1) 0 (A + 2 * K + 3)
    rw [show A + 1 + (2 * K + 2) = A + 2 * K + 3 from by ring,
        show 0 + (2 * K + 2) = 2 * K + 2 from by ring] at h; exact h
  have phase4 : ⟨A + 1, 2 * K + 2, 0, A + 2 * K + 3, 0⟩ [fm]⊢*
      ⟨A + 3 * K + 4, 0, 0, A + 5 * K + 6, 0⟩ := by
    rw [show 2 * K + 2 = 2 * (K + 1) from by ring]
    have h := r3r1r1_chain (K + 1) A (A + 2 * K + 3)
    rw [show A + 3 * (K + 1) + 1 = A + 3 * K + 4 from by ring,
        show A + 2 * K + 3 + 3 * (K + 1) = A + 5 * K + 6 from by ring] at h; exact h
  have phase5 : ⟨A + 3 * K + 4, 0, 0, A + 5 * K + 6, 0⟩ [fm]⊢*
      ⟨0, 0, 2 * A + 6 * K + 8, 2 * A + 8 * K + 10, 0⟩ := by
    have h := r3_chain (A + 3 * K + 4) 0 (A + 5 * K + 6)
    rw [show 0 + 2 * (A + 3 * K + 4) = 2 * A + 6 * K + 8 from by ring,
        show A + 5 * K + 6 + (A + 3 * K + 4) = 2 * A + 8 * K + 10 from by ring] at h; exact h
  exact stepStar_trans (stepStar_trans (stepStar_trans (stepStar_trans
    phase1 phase2) phase3) phase4) phase5

-- Wrapper: odd case in terms of c
theorem main_odd' (c K : ℕ) (hc : c ≥ 2 * K + 2) :
    ⟨0, 0, c, c + 2 * K, 0⟩ [fm]⊢⁺ ⟨0, 0, 2 * c + 2 * K + 1, 2 * c + 4 * K + 2, 0⟩ := by
  have h := main_odd (c - 2 * K - 2) K
  rw [show c - 2 * K - 2 + 2 * K + 2 = c from by omega,
      show c - 2 * K - 2 + 4 * K + 2 = c + 2 * K from by omega,
      show 2 * (c - 2 * K - 2) + 6 * K + 5 = 2 * c + 2 * K + 1 from by omega,
      show 2 * (c - 2 * K - 2) + 8 * K + 6 = 2 * c + 4 * K + 2 from by omega] at h
  exact h

-- Wrapper: even case in terms of c
theorem main_even' (c K : ℕ) (hK : K ≥ 1) (hc : c ≥ 2 * K + 1) :
    ⟨0, 0, c, c + 2 * K - 1, 0⟩ [fm]⊢⁺ ⟨0, 0, 2 * c + 2 * K, 2 * c + 4 * K, 0⟩ := by
  obtain ⟨K', rfl⟩ : ∃ K', K = K' + 1 := ⟨K - 1, by omega⟩
  have h := main_even (c - 2 * K' - 3) K'
  rw [show c - 2 * K' - 3 + 2 * K' + 3 = c from by omega,
      show c - 2 * K' - 3 + 4 * K' + 4 = c + 2 * K' + 1 from by omega,
      show 2 * (c - 2 * K' - 3) + 6 * K' + 8 = 2 * c + 2 * K' + 2 from by omega,
      show 2 * (c - 2 * K' - 3) + 8 * K' + 10 = 2 * c + 4 * K' + 4 from by omega,
      show c + 2 * K' + 1 = c + 2 * (K' + 1) - 1 from by omega,
      show 2 * c + 2 * K' + 2 = 2 * c + 2 * (K' + 1) from by ring,
      show 2 * c + 4 * K' + 4 = 2 * c + 4 * (K' + 1) from by ring] at h
  exact h

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨0, 0, 4, 4, 0⟩) (by execute fm 7)
  apply progress_nonhalt (fm := fm)
    (P := fun q ↦ ∃ c d, q = ⟨0, 0, c, d, 0⟩ ∧ c ≥ 2 ∧ c ≤ d ∧ d + 2 ≤ 2 * c)
  · intro q ⟨c, d, hq, hc, hcd, hdc⟩; subst hq
    rcases Nat.even_or_odd (d - c + 1) with ⟨K, hK⟩ | ⟨K, hK⟩
    · -- Even: d - c + 1 = 2K, K ≥ 1
      have hK1 : K ≥ 1 := by omega
      have hd_eq : d = c + 2 * K - 1 := by omega
      subst hd_eq
      exact ⟨_, ⟨2 * c + 2 * K, 2 * c + 4 * K, rfl, by omega, by omega, by omega⟩,
        main_even' c K hK1 (by omega)⟩
    · -- Odd: d - c + 1 = 2K + 1
      have hd_eq : d = c + 2 * K := by omega
      subst hd_eq
      exact ⟨_, ⟨2 * c + 2 * K + 1, 2 * c + 4 * K + 2, rfl, by omega, by omega, by omega⟩,
        main_odd' c K (by omega)⟩
  · exact ⟨4, 4, rfl, by omega, by omega, by omega⟩

end Sz22_2003_unofficial_482
