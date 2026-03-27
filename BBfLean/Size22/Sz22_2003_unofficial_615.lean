import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #615: [35/6, 121/2, 56/55, 3/7, 5/11]

Vector representation:
```
-1 -1  1  1  0
-1  0  0  0  2
 3  0 -1  1 -1
 0  1  0 -1  0
 0  0  1  0 -1
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_615

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a+1, b+1, c, d, e⟩ => some ⟨a, b, c+1, d+1, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b, c, d, e+2⟩
  | ⟨a, b, c+1, d, e+1⟩ => some ⟨a+3, b, c, d+1, e⟩
  | ⟨a, b, c, d+1, e⟩ => some ⟨a, b+1, c, d, e⟩
  | ⟨a, b, c, d, e+1⟩ => some ⟨a, b, c+1, d, e⟩
  | _ => none

-- R4 chain: convert d to b (with a=0, c=0)
theorem d_to_b (b d k e : ℕ) : ⟨(0:ℕ), b, 0, d+k, e⟩ [fm]⊢* ⟨0, b+k, 0, d, e⟩ := by
  revert b d
  induction k with
  | zero => intro b d; exists 0
  | succ k ih =>
    intro b d
    rw [show d + (k + 1) = (d + k) + 1 from by ring]
    step fm
    apply stepStar_trans (ih (b + 1) d)
    rw [show b + 1 + k = b + (k + 1) from by ring]
    finish

-- R3+R2^3 chain
theorem r3r2_chain (c d e k : ℕ) : ⟨(0:ℕ), 0, c+k, d, e+k⟩ [fm]⊢* ⟨0, 0, c, d+k, e+6*k⟩ := by
  revert c d e
  induction k with
  | zero => intro c d e; exists 0
  | succ k ih =>
    intro c d e
    rw [show c + (k + 1) = (c + k) + 1 from by ring,
        show e + (k + 1) = (e + k) + 1 from by ring]
    step fm; step fm; step fm; step fm
    rw [show e + k + 2 + 2 + 2 = (e + 6) + k from by ring]
    apply stepStar_trans (ih c (d + 1) (e + 6))
    rw [show d + 1 + k = d + (k + 1) from by ring,
        show e + 6 + 6 * k = e + 6 * (k + 1) from by ring]
    finish

-- Wrapper: (0,0,K,D,E) →* (0,0,0,D+K,E+5*K) when E >= K
theorem r3r2_drain (K D E : ℕ) (hE : E ≥ K) :
    ⟨(0:ℕ), 0, K, D, E⟩ [fm]⊢* ⟨0, 0, 0, D+K, E+5*K⟩ := by
  obtain ⟨E', rfl⟩ : ∃ E', E = E' + K := ⟨E - K, by omega⟩
  have h := r3r2_chain 0 D E' K
  rw [show 0 + K = K from by ring,
      show E' + 6 * K = E' + K + 5 * K from by ring] at h
  exact h

-- Big chain via strong induction on B
theorem big_chain : ∀ B, ∀ C D E, E ≥ B + C →
    ⟨(3:ℕ), B, C, D, E⟩ [fm]⊢* ⟨0, 0, 0, D+C+2*B, E+5*C+3*B+6⟩ := by
  intro B; induction B using Nat.strongRecOn with
  | ind B ih =>
  intro C D E hE
  match B with
  | 0 =>
    step fm; step fm; step fm
    apply stepStar_trans (r3r2_drain C D (E + 6) (by omega))
    rw [show D + C + 2 * 0 = D + C from by ring,
        show E + 5 * C + 3 * 0 + 6 = E + 6 + 5 * C from by ring]
    finish
  | 1 =>
    step fm; step fm; step fm
    apply stepStar_trans (r3r2_drain (C+1) (D+1) (E + 4) (by omega))
    rw [show D + 1 + (C + 1) = D + C + 2 * 1 from by ring,
        show E + 4 + 5 * (C + 1) = E + 5 * C + 3 * 1 + 6 from by ring]
    finish
  | 2 =>
    step fm; step fm; step fm
    apply stepStar_trans (r3r2_drain (C+2) (D+2) (E + 2) (by omega))
    rw [show D + 2 + (C + 2) = D + C + 2 * 2 from by ring,
        show E + 2 + 5 * (C + 2) = E + 5 * C + 3 * 2 + 6 from by ring]
    finish
  | B' + 3 =>
    -- R1^3: (3, B'+3, C, D, E) → (2, B'+2, C+1, D+1, E) → (1, B'+1, C+2, D+2, E)
    --       → (0, B', C+3, D+3, E)
    -- R3: (0, B', C+3, D+3, E) → (3, B', C+2, D+4, E-1) [needs C+3>=1 and E>=1]
    step fm; step fm; step fm
    -- Now at (0, B', C+3, D+3, E). Need R3 which requires c+1 and e+1 pattern.
    -- E >= B'+3+C >= 4, so E >= 1.
    -- Rewrite to expose the +1 patterns for R3
    obtain ⟨E', rfl⟩ : ∃ E', E = E' + 1 := ⟨E - 1, by omega⟩
    rw [show C + 1 + 1 + 1 = (C + 2) + 1 from by ring]
    step fm
    apply stepStar_trans (ih B' (by omega) (C + 2) (D + 4) E' (by omega))
    rw [show D + 4 + (C + 2) + 2 * B' = D + C + 2 * (B' + 3) from by ring,
        show E' + 5 * (C + 2) + 3 * B' + 6 = E' + 1 + 5 * C + 3 * (B' + 3) + 6 from by omega]
    finish

-- Main transition: (0,0,0,d,e) →⁺ (0,0,0,2d+1,e+3d+4)
theorem main_trans (hd : d ≥ 1) (he : e ≥ 3*d + 3) :
    ⟨(0:ℕ), 0, 0, d, e⟩ [fm]⊢⁺ ⟨0, 0, 0, 2*d+1, e+3*d+4⟩ := by
  obtain ⟨d', rfl⟩ : ∃ d', d = d' + 1 := ⟨d - 1, by omega⟩
  obtain ⟨e', rfl⟩ : ∃ e', e = e' + 2 := ⟨e - 2, by omega⟩
  -- Phase 1: R4 chain
  rw [show d' + 1 = 0 + (d' + 1) from by ring]
  apply stepStar_stepPlus_stepPlus (d_to_b 0 0 (d'+1) (e'+2))
  rw [show 0 + (d' + 1) = d' + 1 from by ring]
  -- Phase 2: R5 + R3
  rw [show e' + 2 = (e' + 1) + 1 from by ring]
  step fm
  step fm
  -- Phase 3: Big chain
  apply stepStar_trans (big_chain (d'+1) 0 1 e' (by omega))
  rw [show 1 + 0 + 2 * (d' + 1) = 2 * (d' + 1) + 1 from by ring,
      show e' + 5 * 0 + 3 * (d' + 1) + 6 = (e' + 2) + 3 * (d' + 1) + 4 from by ring]
  finish

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨0, 0, 0, 1, 6⟩) (by execute fm 6)
  apply progress_nonhalt (fm := fm)
    (P := fun q ↦ ∃ d e, q = ⟨0, 0, 0, d, e⟩ ∧ d ≥ 1 ∧ e ≥ 3*d + 3)
  · intro c ⟨d, e, hq, hd, he⟩; subst hq
    exact ⟨⟨0, 0, 0, 2*d+1, e+3*d+4⟩,
           ⟨2*d+1, e+3*d+4, rfl, by omega, by omega⟩,
           main_trans hd he⟩
  · exact ⟨1, 6, rfl, by omega, by omega⟩

end Sz22_2003_unofficial_615
