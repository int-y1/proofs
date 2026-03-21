import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz21_140_unofficial #45: [35/6, 4/55, 121/2, 3/7, 6/11]

Vector representation:
```
-1 -1  1  1  0
 2  0 -1  0 -1
-1  0  0  0  2
 0  1  0 -1  0
 1  1  0  0 -1
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz21_140_unofficial_45

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a+1, b+1, c, d, e⟩ => some ⟨a, b, c+1, d+1, e⟩
  | ⟨a, b, c+1, d, e+1⟩ => some ⟨a+2, b, c, d, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b, c, d, e+2⟩
  | ⟨a, b, c, d+1, e⟩ => some ⟨a, b+1, c, d, e⟩
  | ⟨a, b, c, d, e+1⟩ => some ⟨a+1, b+1, c, d, e⟩
  | _ => none

-- R4 repeated: d → b (when a=0, c=0)
theorem d_to_b : ∀ k b d e, ⟨0, b, 0, d+k, e⟩ [fm]⊢* ⟨(0 : ℕ), b+k, 0, d, e⟩ := by
  intro k; induction k with
  | zero => intro b d e; exists 0
  | succ k ih =>
    intro b d e
    rw [show d + (k + 1) = (d + k) + 1 from by ring]
    step fm
    apply stepStar_trans (ih _ _ _)
    ring_nf; finish

-- R3 repeated: a → e (when b=0, c=0)
theorem a_to_e : ∀ k a d e, ⟨a+k, 0, 0, d, e⟩ [fm]⊢* ⟨a, (0 : ℕ), 0, d, e+2*k⟩ := by
  intro k; induction k with
  | zero => intro a d e; exists 0
  | succ k ih =>
    intro a d e
    rw [show a + (k + 1) = (a + k) + 1 from by ring]
    step fm
    apply stepStar_trans (ih _ _ _)
    ring_nf; finish

-- R2 repeated: c,e → a (when b=0)
theorem r2_chain : ∀ k a c d e, ⟨a, 0, c+k, d, e+k⟩ [fm]⊢* ⟨a+2*k, (0 : ℕ), c, d, e⟩ := by
  intro k; induction k with
  | zero => intro a c d e; exists 0
  | succ k ih =>
    intro a c d e
    rw [show c + (k + 1) = (c + k) + 1 from by ring,
        show e + (k + 1) = e + k + 1 from by ring]
    step fm
    apply stepStar_trans (ih _ _ _ _)
    ring_nf; finish

-- Rounds lemma: R1,R1,R2 round reducing b by 2
-- (2, B+2k, C, D, E+k) →* (2, B, C+k, D+2k, E)
theorem round_step : ∀ k B C D E, ⟨2, B+2*k, C, D, E+k⟩ [fm]⊢* ⟨(2 : ℕ), B, C+k, D+2*k, E⟩ := by
  intro k; induction k with
  | zero => intro B C D E; exists 0
  | succ k ih =>
    intro B C D E
    rw [show B + 2 * (k + 1) = (B + 2 * k) + 1 + 1 from by ring,
        show E + (k + 1) = E + k + 1 from by ring]
    -- R1
    step fm
    rw [show B + 2 * k + 1 = (B + 2 * k) + 1 from by ring]
    -- R1
    step fm
    -- R2
    rw [show E + k + 1 = (E + k) + 1 from by ring]
    step fm
    apply stepStar_trans (ih _ _ _ _)
    ring_nf; finish

-- Middle phase for even B=2K:
-- (2, 2K, 0, D, E+2K) ->* (2+2K, 0, 0, D+2K, E)
theorem middle_even (K D E : ℕ) : ⟨2, 2*K, 0, D, E+2*K⟩ [fm]⊢* ⟨2+2*K, 0, 0, D+2*K, E⟩ := by
  apply stepStar_trans (c₂ := ⟨2, 0, K, D + 2 * K, E + K⟩)
  · have h := round_step K 0 0 D (E + K)
    simp only [Nat.zero_add] at h
    rw [show E + 2 * K = E + K + K from by ring]
    exact h
  · have h := r2_chain K 2 0 (D + 2 * K) E
    simp only [Nat.zero_add] at h
    exact h

-- Middle phase for odd B=2K+1:
-- (2, 2K+1, 0, D, E+2K+1) ->* (2K+3, 0, 0, D+2K+1, E)
theorem middle_odd (K D E : ℕ) : ⟨2, 2*K+1, 0, D, E+2*K+1⟩ [fm]⊢* ⟨2*K+3, 0, 0, D+2*K+1, E⟩ := by
  apply stepStar_trans (c₂ := ⟨2, 1, K, D + 2 * K, E + K + 1⟩)
  · have h := round_step K 1 0 D (E + K + 1)
    simp only [Nat.zero_add] at h
    rw [show 1 + 2 * K = 2 * K + 1 from by ring,
        show E + K + 1 + K = E + 2 * K + 1 from by ring] at h
    exact h
  -- R1: (2, 1, K, D+2K, E+K+1) -> (1, 0, K+1, D+2K+1, E+K+1)
  apply stepStar_trans (c₂ := ⟨1, 0, K + 1, D + 2 * K + 1, E + K + 1⟩)
  · rw [show (2 : ℕ) = 1 + 1 from by ring,
        show (1 : ℕ) = 0 + 1 from by ring]
    step fm; finish
  -- R2 chain
  · have h := r2_chain (K + 1) 1 0 (D + 2 * K + 1) E
    simp only [Nat.zero_add] at h
    rw [show E + (K + 1) = E + K + 1 from by ring,
        show 1 + 2 * (K + 1) = 2 * K + 3 from by ring] at h
    exact h

-- Main transition: (0, 0, 0, D+1, F+D+3) ⊢⁺ (0, 0, 0, D+2, F+2*D+6)
theorem main_trans (D F : ℕ) : ⟨0, 0, 0, D+1, F+D+3⟩ [fm]⊢⁺ ⟨0, 0, 0, D+2, F+2*D+6⟩ := by
  -- Phase 1: d_to_b
  apply stepStar_stepPlus_stepPlus (c₂ := ⟨0, D + 1, 0, 0, F + D + 3⟩)
  · have h := d_to_b (D + 1) 0 0 (F + D + 3)
    simp only [Nat.zero_add] at h; exact h
  -- Phase 2: R5
  apply step_stepStar_stepPlus (c₂ := ⟨1, D + 2, 0, 0, F + D + 2⟩)
  · rw [show D + 2 = (D + 1) + 1 from by ring,
        show F + D + 3 = (F + D + 2) + 1 from by ring]
    simp [fm]
  -- Phase 3: R1
  apply stepStar_trans (c₂ := ⟨0, D + 1, 1, 1, F + D + 2⟩)
  · rw [show (1 : ℕ) = 0 + 1 from by ring,
        show D + 2 = (D + 1) + 1 from by ring]
    step fm; finish
  -- Phase 4: R2
  apply stepStar_trans (c₂ := ⟨2, D + 1, 0, 1, F + D + 1⟩)
  · rw [show (1 : ℕ) = 0 + 1 from by ring,
        show F + D + 2 = (F + D + 1) + 1 from by ring]
    step fm; finish
  -- Phase 5: middle phase (split on parity of D+1)
  apply stepStar_trans (c₂ := ⟨D + 3, 0, 0, D + 2, F⟩)
  · rcases Nat.even_or_odd (D + 1) with ⟨K, hK⟩ | ⟨K, hK⟩
    · -- D+1 = 2K (even)
      have h := middle_even K 1 F
      rw [show D + 1 = 2 * K from by omega,
          show F + D + 1 = F + 2 * K from by omega,
          show D + 3 = 2 + 2 * K from by omega,
          show D + 2 = 1 + 2 * K from by omega]
      exact h
    · -- D+1 = 2K+1 (odd)
      have h := middle_odd K 1 F
      rw [show D + 1 = 2 * K + 1 from by omega,
          show F + D + 1 = F + 2 * K + 1 from by omega,
          show D + 3 = 2 * K + 3 from by omega,
          show D + 2 = 2 * K + 1 + 1 from by omega]
      rw [show (1 : ℕ) + 2 * K + 1 = 2 * K + 2 from by ring] at h
      rw [show 2 * K + 1 + 1 = 2 * K + 2 from by ring]
      exact h
  -- Phase 6: a_to_e
  · have h := a_to_e (D + 3) 0 (D + 2) F
    simp only [Nat.zero_add] at h
    refine stepStar_trans h ?_
    ring_nf; finish

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨0, 0, 0, 1, 4⟩) (by execute fm 6)
  apply progress_nonhalt_simple (fm := fm) (A := ℕ × ℕ)
    (fun ⟨D, F⟩ ↦ ⟨0, 0, 0, D + 1, F + D + 3⟩) ⟨0, 1⟩
  intro ⟨D, F⟩
  refine ⟨⟨D + 1, F + D + 2⟩, ?_⟩
  -- Need: C(D+1, F+D+2) = (0,0,0,D+2, (F+D+2)+(D+1)+3) = (0,0,0,D+2, F+2D+6)
  -- main_trans: (0,0,0,D+1,F+D+3) ⊢⁺ (0,0,0,D+2,F+2*D+6)
  show ⟨0, 0, 0, D + 1, F + D + 3⟩ [fm]⊢⁺ ⟨0, 0, 0, D + 1 + 1, F + D + 2 + (D + 1) + 3⟩
  rw [show D + 1 + 1 = D + 2 from by ring,
      show F + D + 2 + (D + 1) + 3 = F + 2 * D + 6 from by ring]
  exact main_trans D F

end Sz21_140_unofficial_45
