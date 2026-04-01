import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #1242: [5/6, 77/2, 4/35, 9/7, 28/11]

Vector representation:
```
-1 -1  1  0  0
-1  0  0  1  1
 2  0 -1 -1  0
 0  2  0 -1  0
 2  0  0  1 -1
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_1242

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a+1, b+1, c, d, e⟩ => some ⟨a, b, c+1, d, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b, c, d+1, e+1⟩
  | ⟨a, b, c+1, d+1, e⟩ => some ⟨a+2, b, c, d, e⟩
  | ⟨a, b, c, d+1, e⟩ => some ⟨a, b+2, c, d, e⟩
  | ⟨a, b, c, d, e+1⟩ => some ⟨a+2, b, c, d+1, e⟩
  | _ => none

private lemma fm_r5 (b c e : ℕ) : fm ⟨0, b, c, 0, e + 1⟩ = some ⟨2, b, c, 1, e⟩ := by
  cases c <;> rfl

private lemma fm_r3 (b c d e : ℕ) : fm ⟨0, b, c + 1, d + 1, e⟩ = some ⟨2, b, c, d, e⟩ := by
  rfl

theorem r4_drain : ∀ k, ∀ b d e, ⟨(0:ℕ), b, 0, d + k, e⟩ [fm]⊢* ⟨0, b + 2 * k, 0, d, e⟩ := by
  intro k; induction' k with k ih <;> intro b d e
  · exists 0
  · rw [show d + (k + 1) = (d + k) + 1 from by ring]
    step fm
    apply stepStar_trans (ih (b + 2) d e)
    ring_nf; finish

theorem cycle6_step (b c e : ℕ) :
    ⟨(0:ℕ), b + 4, c, 0, e + 1⟩ [fm]⊢* ⟨0, b, c + 3, 0, e⟩ := by
  -- R5: (0, b+4, c, 0, e+1) → (2, b+4, c, 1, e)
  apply stepStar_trans (step_stepStar (fm_r5 (b + 4) c e))
  -- R1: (2, (b+3)+1, c, 1, e) → (1, b+3, c+1, 1, e)
  rw [show b + 4 = (b + 3) + 1 from by ring]
  apply stepStar_trans (step_stepStar (show fm ⟨2, (b+3)+1, c, 1, e⟩ = some ⟨1, b+3, c+1, 1, e⟩ from rfl))
  -- R1: (1, (b+2)+1, c+1, 1, e) → (0, b+2, c+2, 1, e)
  rw [show b + 3 = (b + 2) + 1 from by ring]
  apply stepStar_trans (step_stepStar (show fm ⟨1, (b+2)+1, c+1, 1, e⟩ = some ⟨0, b+2, c+2, 1, e⟩ from rfl))
  -- R3: (0, b+2, (c+1)+1, 0+1, e) → (2, b+2, c+1, 0, e)
  rw [show c + 2 = (c + 1) + 1 from by ring, show (1:ℕ) = 0 + 1 from by ring]
  apply stepStar_trans (step_stepStar (fm_r3 (b+2) (c+1) 0 e))
  -- R1: (2, (b+1)+1, c+1, 0, e) → (1, b+1, c+2, 0, e)
  rw [show b + 2 = (b + 1) + 1 from by ring]
  apply stepStar_trans (step_stepStar (show fm ⟨2, (b+1)+1, c+1, 0, e⟩ = some ⟨1, b+1, c+2, 0, e⟩ from rfl))
  -- R1: (1, b+1, c+2, 0, e) → (0, b, c+3, 0, e)
  apply stepStar_trans (step_stepStar (show fm ⟨1, b+1, c+2, 0, e⟩ = some ⟨0, b, c+3, 0, e⟩ from rfl))
  finish

theorem cycle6 : ∀ k, ∀ b c e, ⟨(0:ℕ), b + 4 * k, c, 0, e + k⟩ [fm]⊢* ⟨0, b, c + 3 * k, 0, e⟩ := by
  intro k; induction' k with k ih <;> intro b c e
  · simp; exists 0
  · rw [show b + 4 * (k + 1) = (b + 4) + 4 * k from by ring,
        show e + (k + 1) = (e + 1) + k from by ring]
    apply stepStar_trans (ih (b + 4) c (e + 1))
    apply stepStar_trans (cycle6_step b (c + 3 * k) e)
    rw [show c + 3 * k + 3 = c + 3 * (k + 1) from by ring]
    finish

theorem r3r2r2 : ∀ k, ∀ c d e, ⟨(0:ℕ), 0, c + k, d + 1, e⟩ [fm]⊢* ⟨0, 0, c, d + 1 + k, e + 2 * k⟩ := by
  intro k; induction' k with k ih <;> intro c d e
  · exists 0
  · rw [show c + (k + 1) = (c + k) + 1 from by ring,
        show d + 1 = d + 1 from rfl]
    apply stepStar_trans (step_stepStar (fm_r3 0 (c + k) d e))
    apply stepStar_trans (step_stepStar (show fm ⟨2, 0, c+k, d, e⟩ = some ⟨1, 0, c+k, d+1, e+1⟩ from rfl))
    apply stepStar_trans (step_stepStar (show fm ⟨1, 0, c+k, d+1, e+1⟩ = some ⟨0, 0, c+k, d+2, e+2⟩ from rfl))
    rw [show d + 2 = (d + 1) + 1 from by ring]
    apply stepStar_trans (ih c (d + 1) (e + 2))
    ring_nf; finish

-- Even transition: d = 2(m+2), E = e+m+3
-- (0,0,0,2(m+2),e+m+3) →⁺ (0,0,0,3m+9,e+6m+14)
-- Phases: R4 drain → cycle6 → R5→R2→R2 → R3R2R2 chain
theorem even_trans (m e : ℕ) :
    ⟨(0:ℕ), 0, 0, 2 * (m + 2), e + m + 3⟩ [fm]⊢⁺
    ⟨0, 0, 0, 3 * m + 9, e + 6 * m + 14⟩ := by
  rw [show 2 * (m + 2) = (2 * m + 3) + 1 from by ring]
  step fm
  rw [show 2 * m + 3 = 0 + (2 * m + 3) from by ring]
  apply stepStar_trans (r4_drain (2 * m + 3) 2 0 (e + m + 3))
  rw [show 2 + 2 * (2 * m + 3) = 0 + 4 * (m + 2) from by ring,
      show e + m + 3 = (e + 1) + (m + 2) from by ring]
  apply stepStar_trans (cycle6 (m + 2) 0 0 (e + 1))
  rw [show 0 + 3 * (m + 2) = 3 * m + 6 from by ring]
  -- State: (0, 0, 3m+6, 0, e+1)
  apply stepStar_trans (step_stepStar (fm_r5 0 (3 * m + 6) e))
  -- State: (2, 0, 3m+6, 1, e)
  apply stepStar_trans (step_stepStar (show fm ⟨2, 0, 3*m+6, 1, e⟩ = some ⟨1, 0, 3*m+6, 2, e+1⟩ from rfl))
  apply stepStar_trans (step_stepStar (show fm ⟨1, 0, 3*m+6, 2, e+1⟩ = some ⟨0, 0, 3*m+6, 3, e+2⟩ from rfl))
  -- Phase 4: R3→R2→R2 chain, 3m+6 rounds
  rw [show 3 * m + 6 = 0 + (3 * m + 6) from by ring,
      show (3:ℕ) = 2 + 1 from by ring]
  apply stepStar_trans (r3r2r2 (3 * m + 6) 0 2 (e + 2))
  rw [show 2 + 1 + (3 * m + 6) = 3 * m + 9 from by ring,
      show e + 2 + 2 * (3 * m + 6) = e + 6 * m + 14 from by ring]
  finish

-- Odd transition: d = 2K+3, E = e+K+2
-- (0,0,0,2K+3,e+K+2) →⁺ (0,0,0,3K+6,e+6K+10)
theorem odd_trans (K e : ℕ) :
    ⟨(0:ℕ), 0, 0, 2 * K + 3, e + K + 2⟩ [fm]⊢⁺
    ⟨0, 0, 0, 3 * K + 6, e + 6 * K + 10⟩ := by
  rw [show 2 * K + 3 = (2 * K + 2) + 1 from by ring]
  step fm
  rw [show 2 * K + 2 = 0 + (2 * K + 2) from by ring]
  apply stepStar_trans (r4_drain (2 * K + 2) 2 0 (e + K + 2))
  rw [show 2 + 2 * (2 * K + 2) = 2 + 4 * (K + 1) from by ring,
      show e + K + 2 = (e + 1) + (K + 1) from by ring]
  apply stepStar_trans (cycle6 (K + 1) 2 0 (e + 1))
  rw [show 0 + 3 * (K + 1) = 3 * K + 3 from by ring]
  -- State: (0, 2, 3K+3, 0, e+1)
  apply stepStar_trans (step_stepStar (fm_r5 2 (3 * K + 3) e))
  -- State: (2, 2, 3K+3, 1, e). R1.
  rw [show (2:ℕ) = 1 + 1 from by ring]
  apply stepStar_trans (step_stepStar (show fm ⟨2, 1+1, 3*K+3, 1, e⟩ = some ⟨1, 1, 3*K+4, 1, e⟩ from rfl))
  apply stepStar_trans (step_stepStar (show fm ⟨1, 1, 3*K+4, 1, e⟩ = some ⟨0, 0, 3*K+5, 1, e⟩ from rfl))
  -- R3
  rw [show 3 * K + 5 = (3 * K + 4) + 1 from by ring,
      show (1:ℕ) = 0 + 1 from by ring]
  apply stepStar_trans (step_stepStar (fm_r3 0 (3*K+4) 0 e))
  -- R2, R2
  apply stepStar_trans (step_stepStar (show fm ⟨2, 0, 3*K+4, 0, e⟩ = some ⟨1, 0, 3*K+4, 1, e+1⟩ from rfl))
  apply stepStar_trans (step_stepStar (show fm ⟨1, 0, 3*K+4, 1, e+1⟩ = some ⟨0, 0, 3*K+4, 2, e+2⟩ from rfl))
  -- Phase 4: R3→R2→R2 chain, 3K+4 rounds
  rw [show 3 * K + 4 = 0 + (3 * K + 4) from by ring,
      show (2:ℕ) = 1 + 1 from by ring]
  apply stepStar_trans (r3r2r2 (3 * K + 4) 0 1 (e + 2))
  rw [show 1 + 1 + (3 * K + 4) = 3 * K + 6 from by ring,
      show e + 2 + 2 * (3 * K + 4) = e + 6 * K + 10 from by ring]
  finish

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨0, 0, 0, 3, 4⟩) (by execute fm 11)
  apply progress_nonhalt (fm := fm)
    (P := fun q ↦ ∃ d E, q = ⟨0, 0, 0, d, E⟩ ∧ d ≥ 3 ∧ E ≥ d)
  · intro c ⟨d, E, hq, hd, hE⟩; subst hq
    rcases Nat.even_or_odd d with ⟨K, hK⟩ | ⟨K, hK⟩
    · -- d even: d = 2K, K ≥ 2
      rw [show K + K = 2 * K from by ring] at hK; subst hK
      have hK2 : K ≥ 2 := by omega
      obtain ⟨m, rfl⟩ : ∃ m, K = m + 2 := ⟨K - 2, by omega⟩
      -- d = 2(m+2), E ≥ 2(m+2). Need E = e + m + 3, e ≥ 0. Since E ≥ 2m+4 ≥ m+3.
      obtain ⟨e, rfl⟩ : ∃ e, E = e + (m + 3) := ⟨E - (m + 3), by omega⟩
      refine ⟨⟨0, 0, 0, 3 * m + 9, e + 6 * m + 14⟩,
        ⟨3 * m + 9, e + 6 * m + 14, rfl, by omega, by omega⟩, ?_⟩
      show ⟨0, 0, 0, 2 * (m + 2), e + (m + 3)⟩ [fm]⊢⁺ ⟨0, 0, 0, 3 * m + 9, e + 6 * m + 14⟩
      rw [show e + (m + 3) = e + m + 3 from by ring]
      exact even_trans m e
    · -- d odd: d = 2K+1, K ≥ 1
      subst hK
      have hK1 : K ≥ 1 := by omega
      obtain ⟨K', rfl⟩ : ∃ K', K = K' + 1 := ⟨K - 1, by omega⟩
      -- d = 2(K'+1)+1 = 2K'+3. E ≥ 2K'+3. Need E = e + K' + 2, e ≥ 0.
      -- E ≥ 2K'+3 ≥ K'+2 for K' ≥ 0.
      obtain ⟨e, rfl⟩ : ∃ e, E = e + (K' + 2) := ⟨E - (K' + 2), by omega⟩
      refine ⟨⟨0, 0, 0, 3 * K' + 6, e + 6 * K' + 10⟩,
        ⟨3 * K' + 6, e + 6 * K' + 10, rfl, by omega, by omega⟩, ?_⟩
      show ⟨0, 0, 0, 2 * (K' + 1) + 1, e + (K' + 2)⟩ [fm]⊢⁺ ⟨0, 0, 0, 3 * K' + 6, e + 6 * K' + 10⟩
      rw [show 2 * (K' + 1) + 1 = 2 * K' + 3 from by ring,
          show e + (K' + 2) = e + K' + 2 from by ring]
      exact odd_trans K' e
  · exact ⟨3, 4, rfl, by omega, by omega⟩

end Sz22_2003_unofficial_1242
