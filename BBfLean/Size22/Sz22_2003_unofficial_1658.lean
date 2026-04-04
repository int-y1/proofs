import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #1658: [77/15, 4/3, 9/14, 25/11, 33/2]

Vector representation:
```
 0 -1 -1  1  1
 2 -1  0  0  0
-1  2  0 -1  0
 0  0  2  0 -1
-1  1  0  0  1
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_1658

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a, b+1, c+1, d, e⟩ => some ⟨a, b, c, d+1, e+1⟩
  | ⟨a, b+1, c, d, e⟩ => some ⟨a+2, b, c, d, e⟩
  | ⟨a+1, b, c, d+1, e⟩ => some ⟨a, b+2, c, d, e⟩
  | ⟨a, b, c, d, e+1⟩ => some ⟨a, b, c+2, d, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b+1, c, d, e+1⟩
  | _ => none

theorem r4_chain : ∀ k, ∀ A C,
    ⟨A, 0, C, 0, k⟩ [fm]⊢* ⟨A, 0, C + 2 * k, 0, 0⟩ := by
  intro k; induction' k with k ih <;> intro A C
  · simp; exists 0
  · rw [show (k + 1 : ℕ) = k + 1 from rfl]
    step fm
    rw [show C + 2 * (k + 1) = (C + 2) + 2 * k from by ring]
    exact ih A (C + 2)

theorem r2_chain : ∀ k, ∀ A D E,
    ⟨A, k, 0, D, E⟩ [fm]⊢* ⟨A + 2 * k, 0, 0, D, E⟩ := by
  intro k; induction' k with k ih <;> intro A D E
  · simp; exists 0
  · rw [show (k + 1 : ℕ) = k + 1 from rfl]
    step fm
    apply stepStar_trans (ih (A + 2) D E)
    ring_nf; finish

-- R3+R2+R2 chain: (F+1, 0, 0, k, E) →* (F+3k+1, 0, 0, 0, E)
theorem r3r2r2_chain : ∀ k, ∀ F E,
    ⟨F + 1, 0, 0, k, E⟩ [fm]⊢* ⟨F + 3 * k + 1, 0, 0, 0, E⟩ := by
  intro k; induction' k with k ih <;> intro F E
  · simp; exists 0
  · rw [show F + 1 = F + 1 from rfl,
        show (k + 1 : ℕ) = k + 1 from rfl]
    step fm  -- R3: (F, 0+2, 0, k, E) = (F, 2, 0, k, E)
    rw [show (2 : ℕ) = 1 + 1 from rfl]
    step fm  -- R2: (F+2, 1, 0, k, E)
    rw [show (1 : ℕ) = 0 + 1 from rfl]
    step fm  -- R2: (F+4, 0, 0, k, E) = ((F+3)+1, 0, 0, k, E)
    rw [show F + 2 + 2 = (F + 3) + 1 from by ring]
    have h := ih (F + 3) E
    apply stepStar_trans h
    ring_nf; finish

-- Drain: R3,R1,R1 repeated K times, then R3,R1,R2
-- (F+K+1, 0, 2*K+1, D+1, G) →* (F+2, 0, 0, D+K+1, G+2*K+1)
theorem drain : ∀ K, ∀ F D G,
    ⟨F + K + 1, 0, 2 * K + 1, D + 1, G⟩ [fm]⊢*
    ⟨F + 2, 0, 0, D + K + 1, G + 2 * K + 1⟩ := by
  intro K; induction' K with K ih <;> intro F D G
  · -- K=0: R3, R1, R2
    rw [show F + 0 + 1 = F + 1 from by ring,
        show 2 * 0 + 1 = 0 + 1 from by ring,
        show F + 1 = F + 1 from rfl,
        show (D + 1 : ℕ) = D + 1 from rfl]
    step fm  -- R3: (F, 2, 0+1, D, G)
    rw [show (2 : ℕ) = 1 + 1 from rfl]
    step fm  -- R1: (F, 1, 0, D+1, G+1)
    rw [show (1 : ℕ) = 0 + 1 from rfl]
    step fm  -- R2: (F+2, 0, 0, D+1, G+1)
    rw [show D + 0 + 1 = D + 1 from by ring,
        show G + 2 * 0 + 1 = G + 1 from by ring]
    finish
  · -- K+1: R3, R1, R1, then ih
    rw [show F + (K + 1) + 1 = (F + K + 1) + 1 from by ring,
        show 2 * (K + 1) + 1 = (2 * K + 2) + 1 from by ring,
        show (D + 1 : ℕ) = D + 1 from rfl]
    step fm  -- R3: (F+K+1, 2, (2*K+2)+1, D, G)
    rw [show (2 : ℕ) = 1 + 1 from rfl]
    step fm  -- R1: (F+K+1, 1, 2*K+2, D+1, G+1)
    rw [show (1 : ℕ) = 0 + 1 from rfl,
        show 2 * K + 2 = (2 * K + 1) + 1 from by ring]
    step fm  -- R1: (F+K+1, 0, 2*K+1, D+2, G+2)
    rw [show D + 1 + 1 = (D + 1) + 1 from by ring,
        show G + 1 + 1 = G + 2 from by ring]
    have h := ih F (D + 1) (G + 2)
    apply stepStar_trans h
    rw [show (D + 1) + K + 1 = D + (K + 1) + 1 from by ring,
        show (G + 2) + 2 * K + 1 = G + 2 * (K + 1) + 1 from by ring]
    finish

theorem main_trans (A E : ℕ) (hAE : A ≥ E) :
    ⟨A + 1, 0, 0, 0, E⟩ [fm]⊢⁺ ⟨A + 2 * E + 2, 0, 0, 0, 2 * E + 1⟩ := by
  rcases E with _ | E
  · -- E=0: R5, R2
    rw [show A + 2 * 0 + 2 = A + 2 from by ring,
        show 2 * 0 + 1 = 1 from by ring]
    step fm; step fm; finish
  · -- E+1
    -- Phase 1: R4 chain (E+1 steps)
    have p1 : ⟨A + 1, 0, 0, 0, E + 1⟩ [fm]⊢* ⟨A + 1, 0, 2 * (E + 1), 0, 0⟩ := by
      have h := r4_chain (E + 1) (A + 1) 0
      rw [show 0 + 2 * (E + 1) = 2 * (E + 1) from by ring] at h
      exact h
    -- Phase 2: R5
    have p2 : ⟨A + 1, 0, 2 * (E + 1), 0, 0⟩ [fm]⊢⁺ ⟨A, 1, 2 * (E + 1), 0, 1⟩ := by
      rw [show A + 1 = A + 1 from rfl,
          show 2 * (E + 1) = 0 + 2 * (E + 1) from by ring]
      step fm; finish
    -- Phase 3: R1
    have p3 : ⟨A, 1, 2 * (E + 1), 0, 1⟩ [fm]⊢*
              ⟨A, 0, 2 * E + 1, 1, 2⟩ := by
      rw [show 2 * (E + 1) = (2 * E + 1) + 1 from by ring,
          show (1 : ℕ) = 0 + 1 from rfl]
      step fm
      ring_nf; finish
    -- Phase 4: drain with K=E, F=A-E-1, D=0, G=2
    have p4 : ⟨A, 0, 2 * E + 1, 1, 2⟩ [fm]⊢*
              ⟨A - E + 1, 0, 0, E + 1, 2 * E + 3⟩ := by
      have h := drain E (A - E - 1) 0 2
      rw [show (A - E - 1) + 2 = A - E + 1 from by omega,
          show 0 + E + 1 = E + 1 from by ring,
          show 2 + 2 * E + 1 = 2 * E + 3 from by ring,
          show (A - E - 1) + E + 1 = A from by omega,
          show (0 : ℕ) + 1 = 1 from by ring] at h
      exact h
    -- Phase 5: r3r2r2 chain (E+1 rounds)
    have p5 : ⟨A - E + 1, 0, 0, E + 1, 2 * E + 3⟩ [fm]⊢*
              ⟨A + 2 * E + 4, 0, 0, 0, 2 * E + 3⟩ := by
      rw [show A - E + 1 = (A - E - 1) + 1 + 1 from by omega]
      have h := r3r2r2_chain (E + 1) ((A - E - 1) + 1) (2 * E + 3)
      -- h : ((A-E-1)+1+1, 0, 0, E+1, 2E+3) →* ((A-E-1)+1+3*(E+1)+1, 0, 0, 0, 2E+3)
      -- (A-E-1)+1+3*(E+1)+1 = A-E+3E+3+1 = A+2E+4
      rw [show (A - E - 1) + 1 + 3 * (E + 1) + 1 = A + 2 * E + 4 from by omega] at h
      exact h
    rw [show 2 * (E + 1) + 1 = 2 * E + 3 from by ring,
        show A + 2 * (E + 1) + 2 = A + 2 * E + 4 from by ring]
    exact stepStar_stepPlus_stepPlus p1
      (stepPlus_stepStar_stepPlus p2 (stepStar_trans p3 (stepStar_trans p4 p5)))

theorem nonhalt : ¬halts fm c₀ := by
  apply progress_nonhalt (fm := fm)
    (P := fun q ↦ ∃ A E, q = ⟨A + 1, 0, 0, 0, E⟩ ∧ A ≥ E)
  · intro c ⟨A, E, hq, hAE⟩
    rw [hq]
    refine ⟨⟨A + 2 * E + 2, 0, 0, 0, 2 * E + 1⟩,
           ⟨A + 2 * E + 1, 2 * E + 1, ?_, ?_⟩,
           main_trans A E hAE⟩
    · ring_nf
    · omega
  · exact ⟨0, 0, rfl, by omega⟩

end Sz22_2003_unofficial_1658
