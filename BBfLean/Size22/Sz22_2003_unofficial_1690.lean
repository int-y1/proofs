import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #1690: [77/15, 9/14, 44/3, 5/11, 33/2]

Vector representation:
```
 0 -1 -1  1  1
-1  2  0 -1  0
 2 -1  0  0  1
 0  0  1  0 -1
-1  1  0  0  1
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6 (1M context)
-/

namespace Sz22_2003_unofficial_1690

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a, b+1, c+1, d, e⟩ => some ⟨a, b, c, d+1, e+1⟩
  | ⟨a+1, b, c, d+1, e⟩ => some ⟨a, b+2, c, d, e⟩
  | ⟨a, b+1, c, d, e⟩ => some ⟨a+2, b, c, d, e+1⟩
  | ⟨a, b, c, d, e+1⟩ => some ⟨a, b, c+1, d, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b+1, c, d, e+1⟩
  | _ => none

theorem r4_chain : ∀ k, ∀ A C,
    ⟨A, 0, C, 0, k⟩ [fm]⊢* ⟨A, 0, C + k, 0, 0⟩ := by
  intro k; induction' k with k ih <;> intro A C
  · simp; exists 0
  · step fm
    apply stepStar_trans (ih A (C + 1))
    rw [show C + 1 + k = C + (k + 1) from by ring]; finish

theorem r2r1r1_chain : ∀ k, ∀ A C D E,
    ⟨A + k, 0, C + 2 * k, D + 1, E⟩ [fm]⊢* ⟨A, 0, C, D + 1 + k, E + 2 * k⟩ := by
  intro k; induction' k with k ih <;> intro A C D E
  · simp; exists 0
  · rw [show A + (k + 1) = (A + k) + 1 from by ring,
        show C + 2 * (k + 1) = (C + 2 * k) + 1 + 1 from by ring]
    step fm; step fm; step fm
    apply stepStar_trans (ih A C (D + 1) (E + 2))
    rw [show D + 1 + 1 + k = D + 1 + (k + 1) from by ring,
        show E + 2 + 2 * k = E + 2 * (k + 1) from by ring]; finish

theorem drain : ∀ M, ∀ A B D E, 3 * D + B = M →
    ⟨A, B + 1, 0, D, E⟩ [fm]⊢* ⟨A + 2 * B + 2 + 3 * D, 0, 0, 0, E + B + 1 + 2 * D⟩ := by
  intro M; induction' M using Nat.strongRecOn with M ih; intro A B D E hM
  rcases D with _ | D
  · -- D = 0
    rcases B with _ | B
    · -- B = 0: (A, 1, 0, 0, E) → R3 → (A+2, 0, 0, 0, E+1)
      step fm; ring_nf; finish
    · -- B = B'+1: (A, B'+2, 0, 0, E) → R3 → (A+2, B'+1, 0, 0, E+1)
      rw [show (B + 1) + 1 = (B + 1) + 1 from rfl]
      step fm
      have := ih (3 * 0 + B) (by omega) (A + 2) B 0 (E + 1) rfl
      rw [show (A + 2) + 2 * B + 2 + 3 * 0 = A + 2 * (B + 1) + 2 + 3 * 0 from by ring,
          show E + 1 + B + 1 + 2 * 0 = E + (B + 1) + 1 + 2 * 0 from by ring] at this
      exact this
  · -- D = D'+1
    rcases A with _ | A
    · -- A = 0
      rcases B with _ | B
      · -- B = 0: (0, 1, 0, D'+1, E) → R3 → (2, 0, 0, D'+1, E+1) → R2 → (1, 2, 0, D', E+1)
        step fm
        rw [show D + 1 = D + 1 from rfl]
        step fm
        have := ih (3 * D + 1) (by omega) 1 1 D (E + 1) (by ring)
        rw [show 1 + 2 * 1 + 2 + 3 * D = 0 + 2 * 0 + 2 + 3 * (D + 1) from by ring,
            show E + 1 + 1 + 1 + 2 * D = E + 0 + 1 + 2 * (D + 1) from by ring] at this
        exact this
      · -- B = B'+1: (0, B'+2, 0, D'+1, E) → R3 → (2, B'+1, 0, D'+1, E+1)
        rw [show (B + 1) + 1 = (B + 1) + 1 from rfl]
        step fm
        have := ih (3 * (D + 1) + B) (by omega) 2 B (D + 1) (E + 1) (by ring)
        rw [show 2 + 2 * B + 2 + 3 * (D + 1) = 0 + 2 * (B + 1) + 2 + 3 * (D + 1) from by ring,
            show E + 1 + B + 1 + 2 * (D + 1) = E + (B + 1) + 1 + 2 * (D + 1) from by ring] at this
        exact this
    · -- A = A'+1, D = D'+1: R2 fires
      rw [show A + 1 = A + 1 from rfl, show D + 1 = D + 1 from rfl]
      step fm
      have := ih (3 * D + (B + 2)) (by omega) A (B + 2) D E (by ring)
      rw [show A + 2 * (B + 2) + 2 + 3 * D = (A + 1) + 2 * B + 2 + 3 * (D + 1) from by ring,
          show E + (B + 2) + 1 + 2 * D = E + B + 1 + 2 * (D + 1) from by ring] at this
      exact this

-- Main transition: (a, 0, 0, 0, a+G) ⊢⁺ (2*a+G+1, 0, 0, 0, 2*a+2*G+2)
-- Parametrized as: a = 2*m+G+2 gives (2*m+G+2, 0, 0, 0, 2*m+2*G+2)
-- Next: (2*(2*m+G+2)+G+1, 0, 0, 0, 2*(2*m+G+2)+2*G+2)
--     = (4*m+3*G+5, 0, 0, 0, 4*m+4*G+6)
theorem main_trans (m G : ℕ) :
    ⟨2 * m + G + 2, 0, 0, 0, 2 * m + 2 * G + 2⟩ [fm]⊢⁺
    ⟨4 * m + 3 * G + 5, 0, 0, 0, 4 * m + 4 * G + 6⟩ := by
  -- Phase 1: R4 fires (2*m+2*G+2) times
  have p1 : ⟨2 * m + G + 2, 0, 0, 0, 2 * m + 2 * G + 2⟩ [fm]⊢*
      ⟨2 * m + G + 2, 0, 2 * m + 2 * G + 2, 0, 0⟩ := by
    have := r4_chain (2 * m + 2 * G + 2) (2 * m + G + 2) 0
    simp only [Nat.zero_add] at this; exact this
  -- Phase 2: R5 fires once
  have p2 : ⟨2 * m + G + 2, 0, 2 * m + 2 * G + 2, 0, 0⟩ [fm]⊢⁺
      ⟨2 * m + G + 1, 1, 2 * m + 2 * G + 2, 0, 1⟩ := by
    rw [show 2 * m + G + 2 = (2 * m + G + 1) + 1 from by ring]
    step fm; finish
  -- Phase 3: R1 fires once
  have p3 : ⟨2 * m + G + 1, 1, 2 * m + 2 * G + 2, 0, 1⟩ [fm]⊢*
      ⟨2 * m + G + 1, 0, 2 * m + 2 * G + 1, 1, 2⟩ := by
    rw [show (1 : ℕ) = 0 + 1 from rfl,
        show 2 * m + 2 * G + 2 = (2 * m + 2 * G + 1) + 1 from by ring]
    step fm; ring_nf; finish
  -- Phase 4: R2R1R1 chain fires (m+G) times
  have p4 : ⟨2 * m + G + 1, 0, 2 * m + 2 * G + 1, 1, 2⟩ [fm]⊢*
      ⟨m + 1, 0, 1, m + G + 1, 2 * m + 2 * G + 2⟩ := by
    have := r2r1r1_chain (m + G) (m + 1) 1 0 2
    rw [show m + 1 + (m + G) = 2 * m + G + 1 from by ring,
        show 1 + 2 * (m + G) = 2 * m + 2 * G + 1 from by ring,
        show 0 + 1 + (m + G) = m + G + 1 from by ring,
        show 2 + 2 * (m + G) = 2 * m + 2 * G + 2 from by ring] at this
    exact this
  -- Phase 5: R2 then R1 (partial round since c=1)
  have p5 : ⟨m + 1, 0, 1, m + G + 1, 2 * m + 2 * G + 2⟩ [fm]⊢*
      ⟨m, 1, 0, m + G + 1, 2 * m + 2 * G + 3⟩ := by
    rw [show m + 1 = m + 1 from rfl,
        show m + G + 1 = (m + G) + 1 from by ring]
    step fm
    rw [show (2 : ℕ) = 1 + 1 from rfl, show (1 : ℕ) = 0 + 1 from rfl]
    step fm
    ring_nf; finish
  -- Phase 6: Drain (m, 1, 0, m+G+1, 2*m+2*G+3) using the drain lemma
  -- Here A=m, B=0, D=m+G+1, E=2*m+2*G+3
  -- Output: (m + 0 + 2 + 3*(m+G+1), 0, 0, 0, 2*m+2*G+3 + 0 + 1 + 2*(m+G+1))
  --       = (m + 2 + 3m + 3G + 3, 0, 0, 0, 2m+2G+3 + 1 + 2m + 2G + 2)
  --       = (4m + 3G + 5, 0, 0, 0, 4m + 4G + 6)
  have p6 : ⟨m, 1, 0, m + G + 1, 2 * m + 2 * G + 3⟩ [fm]⊢*
      ⟨4 * m + 3 * G + 5, 0, 0, 0, 4 * m + 4 * G + 6⟩ := by
    rw [show (1 : ℕ) = 0 + 1 from rfl]
    have := drain (3 * (m + G + 1) + 0) m 0 (m + G + 1) (2 * m + 2 * G + 3) (by ring)
    rw [show m + 2 * 0 + 2 + 3 * (m + G + 1) = 4 * m + 3 * G + 5 from by ring,
        show 2 * m + 2 * G + 3 + 0 + 1 + 2 * (m + G + 1) = 4 * m + 4 * G + 6 from by ring] at this
    exact this
  exact stepStar_stepPlus_stepPlus p1
    (stepPlus_stepStar_stepPlus p2
      (stepStar_trans p3 (stepStar_trans p4 (stepStar_trans p5 p6))))

theorem nonhalt : ¬halts fm c₀ := by
  -- Bootstrap: c₀ = (1,0,0,0,0) reaches (2,0,0,0,2) in 2 steps
  -- (2,0,0,0,2) corresponds to m=0, G=0: 2*0+0+2=2, 2*0+0+2=2
  apply stepStar_not_halts_not_halts (c₂ := ⟨2, 0, 0, 0, 2⟩) (by execute fm 2)
  apply progress_nonhalt_simple (fm := fm) (A := ℕ × ℕ)
    (fun ⟨m, G⟩ ↦ ⟨2 * m + G + 2, 0, 0, 0, 2 * m + 2 * G + 2⟩) ⟨0, 0⟩
  intro ⟨m, G⟩
  -- Next state: (4*m+3*G+5, 0, 0, 0, 4*m+4*G+6)
  -- = (2*m'+G'+2, 0, 0, 0, 2*m'+2*G'+2) where m' = 2*m+G+1, G' = G+1
  -- Check: 2*(2*m+G+1)+(G+1)+2 = 4*m+2*G+2+G+1+2 = 4*m+3*G+5 ✓
  -- Check: 2*(2*m+G+1)+2*(G+1)+2 = 4*m+2*G+2+2*G+2+2 = 4*m+4*G+6 ✓
  refine ⟨⟨2 * m + G + 1, G + 1⟩, ?_⟩
  show ⟨2 * m + G + 2, 0, 0, 0, 2 * m + 2 * G + 2⟩ [fm]⊢⁺
    ⟨2 * (2 * m + G + 1) + (G + 1) + 2, 0, 0, 0, 2 * (2 * m + G + 1) + 2 * (G + 1) + 2⟩
  rw [show 2 * (2 * m + G + 1) + (G + 1) + 2 = 4 * m + 3 * G + 5 from by ring,
      show 2 * (2 * m + G + 1) + 2 * (G + 1) + 2 = 4 * m + 4 * G + 6 from by ring]
  exact main_trans m G

end Sz22_2003_unofficial_1690
