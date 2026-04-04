import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #1922: [9/70, 2/15, 275/2, 7/11, 6/7]

Vector representation:
```
-1  2 -1 -1  0
 1 -1 -1  0  0
-1  0  2  0  1
 0  0  0  1 -1
 1  1  0 -1  0
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_1922

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a+1, b, c+1, d+1, e⟩ => some ⟨a, b+2, c, d, e⟩
  | ⟨a, b+1, c+1, d, e⟩ => some ⟨a+1, b, c, d, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b, c+2, d, e+1⟩
  | ⟨a, b, c, d, e+1⟩ => some ⟨a, b, c, d+1, e⟩
  | ⟨a, b, c, d+1, e⟩ => some ⟨a+1, b+1, c, d, e⟩
  | _ => none

theorem r3r2r2_chain : ∀ k, ∀ a b e,
    ⟨a + 1, b + 2 * k, 0, 0, e⟩ [fm]⊢* ⟨a + k + 1, b, 0, 0, e + k⟩ := by
  intro k; induction' k with k ih <;> intro a b e
  · exists 0
  · rw [show b + 2 * (k + 1) = (b + 2 * k) + 2 from by ring]
    step fm; step fm; step fm
    rw [show a + 2 = (a + 1) + 1 from by ring]
    apply stepStar_trans (ih (a + 1) b (e + 1))
    ring_nf; finish

theorem r3_chain : ∀ a, ∀ c e,
    ⟨a + 1, 0, c, 0, e⟩ [fm]⊢* ⟨0, 0, c + 2 * (a + 1), 0, e + (a + 1)⟩ := by
  intro a; induction' a with a ih <;> intro c e
  · step fm; finish
  · step fm
    apply stepStar_trans (ih (c + 2) (e + 1))
    ring_nf; finish

theorem r4_chain : ∀ k, ∀ c d e,
    ⟨0, 0, c, d, e + k + 1⟩ [fm]⊢* ⟨0, 0, c, d + k + 1, e⟩ := by
  intro k; induction' k with k ih <;> intro c d e
  · step fm; finish
  · rw [show e + (k + 1) + 1 = (e + k + 1) + 1 from by ring]
    step fm
    apply stepStar_trans (ih c (d + 1) e)
    ring_nf; finish

theorem r1r2_interleave : ∀ k, ∀ j c d,
    ⟨1, j + 1, c + 2 * (k + 1), d + (k + 1), 0⟩ [fm]⊢* ⟨1, j + k + 2, c, d, 0⟩ := by
  intro k; induction' k with k ih <;> intro j c d
  · step fm; step fm; ring_nf; finish
  · rw [show c + 2 * (k + 1 + 1) = (c + 2 * (k + 1)) + 2 from by ring,
        show d + (k + 1 + 1) = (d + (k + 1)) + 1 from by ring]
    step fm; step fm
    rw [show j + 2 = (j + 1) + 1 from by ring]
    apply stepStar_trans (ih (j + 1) c d)
    ring_nf; finish

theorem d_drain_sub : ∀ d b,
    ⟨1, b + 1, 0, d + 1, 0⟩ [fm]⊢* ⟨1, b + 2 * d + 3, 0, 0, 0⟩ := by
  intro d; induction' d with d ih <;> intro b
  · step fm; step fm; step fm; step fm; step fm; finish
  · step fm; step fm; step fm; step fm; step fm
    rw [show b + 1 + 2 = (b + 2) + 1 from by ring]
    apply stepStar_trans (ih (b + 2))
    ring_nf; finish

theorem even_trans :
    ⟨1, 2 * (m + 3), 0, 0, 0⟩ [fm]⊢⁺ ⟨1, 3 * (m + 3), 0, 0, 0⟩ := by
  -- First step: R3 fires on (1, 2*(m+3), 0, 0, 0)
  rw [show 2 * (m + 3) = 0 + 2 * (m + 3) from by ring]
  step fm
  -- State after R3: (0, 0+2*(m+3), 2, 0, 1)
  -- Continue with R2, R2 to complete first round of R3R2R2
  step fm; step fm
  -- State: (2, 0+2*(m+3)-2, 0, 0, 1) = (2, 2*(m+2), 0, 0, 1)
  -- Remaining R3R2R2 rounds: m+2 rounds
  show ⟨2, 0 + 2 * (m + 2), 0, 0, 1⟩ [fm]⊢* _
  rw [show (2 : ℕ) = 1 + 1 from by ring]
  apply stepStar_trans (r3r2r2_chain (m + 2) 1 0 1)
  rw [show 1 + (m + 2) + 1 = (m + 3) + 1 from by ring,
      show 1 + (m + 2) = m + 3 from by ring]
  -- Phase 2: R3 chain
  apply stepStar_trans (r3_chain (m + 3) 0 (m + 3))
  rw [show 0 + 2 * ((m + 3) + 1) = 2 * m + 8 from by ring,
      show (m + 3) + ((m + 3) + 1) = 2 * m + 7 from by ring]
  -- Phase 3: R4 chain
  rw [show (2 * m + 7 : ℕ) = 0 + (2 * m + 6) + 1 from by ring]
  apply stepStar_trans (r4_chain (2 * m + 6) (2 * m + 8) 0 0)
  rw [show 0 + (2 * m + 6) + 1 = (2 * m + 6) + 1 from by ring]
  -- Phase 4: R5
  step fm
  -- Phase 5: R1R2 interleave
  rw [show 2 * m + 8 = 2 + 2 * ((m + 2) + 1) from by ring,
      show 2 * m + 6 = (m + 3) + ((m + 2) + 1) from by ring]
  apply stepStar_trans (r1r2_interleave (m + 2) 0 2 (m + 3))
  rw [show 0 + (m + 2) + 2 = m + 4 from by ring]
  -- Phase 6: R1, R2
  rw [show (m + 3 : ℕ) = (m + 2) + 1 from by ring]
  step fm; step fm
  show ⟨1, m + 4 + 2 - 1, 0, m + 2, 0⟩ [fm]⊢* _
  rw [show m + 4 + 2 - 1 = m + 5 from by omega]
  -- Phase 7: d_drain
  rw [show (m + 2 : ℕ) = (m + 1) + 1 from by ring,
      show m + 5 = (m + 4) + 1 from by ring]
  apply stepStar_trans (d_drain_sub (m + 1) (m + 4))
  rw [show m + 4 + 2 * (m + 1) + 3 = 3 * (m + 3) from by ring]
  finish

theorem odd_trans :
    ⟨1, 2 * (m + 2) + 1, 0, 0, 0⟩ [fm]⊢⁺ ⟨1, 3 * (m + 2) + 1, 0, 0, 0⟩ := by
  -- First step: R3
  rw [show 2 * (m + 2) + 1 = 1 + 2 * (m + 2) from by ring]
  step fm
  -- R2, R2
  step fm; step fm
  -- Remaining R3R2R2: m+1 rounds
  show ⟨2, 1 + 2 * (m + 1), 0, 0, 1⟩ [fm]⊢* _
  rw [show (2 : ℕ) = 1 + 1 from by ring]
  apply stepStar_trans (r3r2r2_chain (m + 1) 1 1 1)
  rw [show 1 + (m + 1) + 1 = (m + 2) + 1 from by ring,
      show 1 + (m + 1) = m + 2 from by ring]
  -- Phase 1b: R3, R2
  step fm; step fm
  show ⟨(m + 2) + 1, 0, 1, 0, m + 2 + 1⟩ [fm]⊢* _
  rw [show m + 2 + 1 = m + 3 from by ring]
  -- Phase 2: R3 chain
  apply stepStar_trans (r3_chain (m + 2) 1 (m + 3))
  rw [show 1 + 2 * ((m + 2) + 1) = 2 * m + 7 from by ring,
      show (m + 3) + ((m + 2) + 1) = 2 * m + 6 from by ring]
  -- Phase 3: R4 chain
  rw [show (2 * m + 6 : ℕ) = 0 + (2 * m + 5) + 1 from by ring]
  apply stepStar_trans (r4_chain (2 * m + 5) (2 * m + 7) 0 0)
  rw [show 0 + (2 * m + 5) + 1 = (2 * m + 5) + 1 from by ring]
  -- Phase 4: R5
  step fm
  -- Phase 5: R1R2 interleave
  rw [show 2 * m + 7 = 3 + 2 * ((m + 1) + 1) from by ring,
      show 2 * m + 5 = (m + 3) + ((m + 1) + 1) from by ring]
  apply stepStar_trans (r1r2_interleave (m + 1) 0 3 (m + 3))
  rw [show 0 + (m + 1) + 2 = m + 3 from by ring]
  -- Phase 6: R1, R2, R1
  rw [show (m + 3 : ℕ) = (m + 2) + 1 from by ring]
  step fm; step fm; step fm
  show ⟨0, m + 3 + 2 - 1 + 2, 0, m + 1, 0⟩ [fm]⊢* _
  rw [show m + 3 + 2 - 1 + 2 = m + 6 from by omega]
  -- Phase 7: R5
  rw [show (m + 1 : ℕ) = m + 1 from rfl]
  step fm
  show ⟨1, m + 6 + 1, 0, m, 0⟩ [fm]⊢* _
  rw [show m + 6 + 1 = m + 7 from by ring]
  -- Phase 8: d_drain
  rcases m with _ | m'
  · finish
  · show ⟨1, (m' + 7) + 1, 0, m' + 1, 0⟩ [fm]⊢* _
    apply stepStar_trans (d_drain_sub m' (m' + 7))
    rw [show m' + 7 + 2 * m' + 3 = 3 * ((m' + 1) + 2) + 1 from by ring]
    finish

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨1, 5, 0, 0, 0⟩) (by execute fm 65)
  apply progress_nonhalt (fm := fm)
    (P := fun q ↦ ∃ b, q = ⟨1, b, 0, 0, 0⟩ ∧ b ≥ 5)
  · intro c ⟨b, hq, hb⟩; subst hq
    rcases Nat.even_or_odd b with ⟨K, hK⟩ | ⟨K, hK⟩
    · rw [show K + K = 2 * K from by ring] at hK; subst hK
      obtain ⟨m, rfl⟩ : ∃ m, K = m + 3 := ⟨K - 3, by omega⟩
      exact ⟨⟨1, 3 * (m + 3), 0, 0, 0⟩,
        ⟨3 * (m + 3), rfl, by omega⟩, even_trans⟩
    · subst hK
      obtain ⟨m, rfl⟩ : ∃ m, K = m + 2 := ⟨K - 2, by omega⟩
      exact ⟨⟨1, 3 * (m + 2) + 1, 0, 0, 0⟩,
        ⟨3 * (m + 2) + 1, rfl, by omega⟩, odd_trans⟩
  · exact ⟨5, rfl, by omega⟩
