import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #579: [35/6, 11/2, 4/55, 3/7, 56/11]

Vector representation:
```
-1 -1  1  1  0
-1  0  0  0  1
 2  0 -1  0 -1
 0  1  0 -1  0
 3  0  0  1 -1
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_579

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a+1, b+1, c, d, e⟩ => some ⟨a, b, c+1, d+1, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b, c, d, e+1⟩
  | ⟨a, b, c+1, d, e+1⟩ => some ⟨a+2, b, c, d, e⟩
  | ⟨a, b, c, d+1, e⟩ => some ⟨a, b+1, c, d, e⟩
  | ⟨a, b, c, d, e+1⟩ => some ⟨a+3, b, c, d+1, e⟩
  | _ => none

-- R4 repeated: convert d to b
theorem d_to_b : ∀ k b, ⟨0, b, 0, d+k, e⟩ [fm]⊢* ⟨0, b+k, 0, d, e⟩ := by
  intro k; induction' k with k ih <;> intro b
  · exists 0
  rw [show d + (k + 1) = (d + k) + 1 from by ring]
  step fm
  apply stepStar_trans (ih _)
  ring_nf; finish

-- R3R2R2 repeated: convert c to e (when b=0)
-- Each round: (0, 0, c+1, d, e+1) → R3 → (2, 0, c, d, e) → R2 → (1, 0, c, d, e+1) → R2 → (0, 0, c, d, e+2)
-- Net effect per round: c decreases by 1, e increases by 1
theorem r3r2r2_chain : ∀ k c e, ⟨0, 0, c+k, d, e+1⟩ [fm]⊢* ⟨0, 0, c, d, e+k+1⟩ := by
  intro k; induction' k with k ih <;> intro c e
  · exists 0
  rw [show c + (k + 1) = (c + k) + 1 from by ring]
  step fm; step fm; step fm
  apply stepStar_trans (ih c (e+1))
  ring_nf; finish

-- Even chain: do k big rounds of R3R1R1 when b = 2k
-- Each big round: (0, b+2, c+1, d, e+1) → R3 → (2, b+2, c, d, e) → R1 → (1, b+1, c+1, d+1, e)
-- → R1 → (0, b, c+2, d+2, e)
-- Net effect per round: b decreases by 2, c increases by 1, d increases by 2, e decreases by 1
theorem even_chain : ∀ k c d e, ⟨0, 2*k, c+1, d, e+k+1⟩ [fm]⊢* ⟨0, 0, c+k+1, d+2*k, e+1⟩ := by
  intro k; induction' k with k ih <;> intro c d e
  · simp; exists 0
  rw [show 2 * (k + 1) = (2 * k) + 2 from by ring,
      show e + (k + 1) + 1 = (e + k + 1) + 1 from by ring]
  step fm; step fm; step fm
  rw [show c + 2 = (c + 1) + 1 from by ring]
  apply stepStar_trans (ih (c+1) (d+2) e)
  ring_nf; finish

-- Odd chain: do k big rounds then handle b=1
-- (0, 2k+1, c+1, d, e+k+1) →* (0, 1, c+k+1, d+2k, e+1) via even_chain with extra 1
-- Then R3R1R2: (0, 1, c'+1, d', e'+1) → (0, 0, c'+1, d'+1, e'+1)
theorem odd_chain : ∀ k c d e,
    ⟨0, 2*k+1, c+1, d, e+k+1⟩ [fm]⊢* ⟨0, 0, c+k+1, d+2*k+1, e+1⟩ := by
  intro k; induction' k with k ih <;> intro c d e
  · -- k=0: (0, 1, c+1, d, e+1) → R3R1R2 → (0, 0, c+1, d+1, e+1)
    simp
    step fm; step fm; step fm; finish
  · -- (0, 2(k+1)+1, c+1, d, e+(k+1)+1) = (0, 2k+3, c+1, d, e+k+2)
    -- One big round: → (0, 2k+1, c+2, d+2, e+k+1)
    rw [show 2 * (k + 1) + 1 = (2 * k + 1) + 2 from by ring,
        show e + (k + 1) + 1 = (e + k + 1) + 1 from by ring]
    step fm; step fm; step fm
    rw [show c + 2 = (c + 1) + 1 from by ring]
    apply stepStar_trans (ih (c+1) (d+2) e)
    ring_nf; finish

-- Main transition for n ≥ 3 (write n = n'+3)
theorem general_trans :
    ⟨0, 0, 0, n+3, 2*n+7⟩ [fm]⊢⁺ ⟨0, 0, 0, n+4, 2*n+9⟩ := by
  -- Phase 1: R4 chain: (0,0,0,n+3,2n+7) →* (0,n+3,0,0,2n+7)
  rw [show n + 3 = 0 + (n + 3) from by ring]
  apply stepStar_stepPlus_stepPlus (d_to_b (d := 0) (e := 2*n+7) (n+3) 0)
  simp only [Nat.zero_add]
  -- Phase 2: R5: (0, n+3, 0, 0, 2n+7) → (3, n+3, 0, 1, 2n+6)
  rw [show 2 * n + 7 = (2 * n + 6) + 1 from by ring]
  step fm
  -- (3, n+3, 0, 1, 2n+6)
  -- Phase 3: R1 x 3
  rw [show (n : ℕ) + 3 = (n + 2) + 1 from by ring]
  step fm
  rw [show (n : ℕ) + 2 = (n + 1) + 1 from by ring]
  step fm
  rw [show (n : ℕ) + 1 = n + 0 + 1 from by ring]
  step fm
  -- (0, n, 3, 4, 2n+6) = (0, n, 2+1, 4, 2n+6)
  -- Phase 4: Drain b via even/odd chain, then R3R2R2 chain
  rcases Nat.even_or_odd n with ⟨K, hK⟩ | ⟨K, hK⟩
  · -- n = 2K (even)
    rw [show K + K = 2 * K from by ring] at hK; subst hK
    -- (0, 2K, 2+1, 4, 4K+6)
    -- Need: 4K+6 = (3K+5)+K+1
    rw [show 2 * (2 * K) + 6 = (3 * K + 5) + K + 1 from by ring]
    apply stepStar_trans (even_chain K 2 4 (3*K+5))
    -- (0, 0, K+3, 2K+4, 3K+6)
    rw [show 2 + K + 1 = 0 + (K + 3) from by ring,
        show (3 * K + 5) + 1 = (3 * K + 5) + 1 from rfl]
    apply stepStar_trans (r3r2r2_chain (d := 4+2*K) (K+3) 0 (3*K+5))
    ring_nf; finish
  · -- n = 2K+1 (odd)
    subst hK
    -- (0, 2K+1, 2+1, 4, 4K+8)
    -- Need: 4K+8 = (3K+7)+K+1
    rw [show 2 * (2 * K + 1) + 6 = (3 * K + 7) + K + 1 from by ring]
    apply stepStar_trans (odd_chain K 2 4 (3*K+7))
    -- (0, 0, K+3, 2K+5, 3K+8)
    rw [show 2 + K + 1 = 0 + (K + 3) from by ring,
        show 4 + 2 * K + 1 = 2 * K + 5 from by ring,
        show (3 * K + 7) + 1 = (3 * K + 7) + 1 from rfl]
    apply stepStar_trans (r3r2r2_chain (d := 2*K+5) (K+3) 0 (3*K+7))
    ring_nf; finish

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨0, 0, 0, 1, 3⟩) (by execute fm 5)
  apply progress_nonhalt (fm := fm)
    (P := fun q ↦ ∃ n, q = ⟨0, 0, 0, n+1, 2*(n+1)+1⟩)
  · intro c ⟨n, hq⟩; subst hq
    rcases n with _ | _ | n'
    · exact ⟨⟨0, 0, 0, 2, 5⟩, ⟨1, rfl⟩, by execute fm 8⟩
    · exact ⟨⟨0, 0, 0, 3, 7⟩, ⟨2, rfl⟩, by execute fm 12⟩
    · rw [show 2 * (n' + 2 + 1) + 1 = 2 * n' + 7 from by ring,
          show n' + 2 + 1 = n' + 3 from by ring]
      exact ⟨⟨0, 0, 0, n'+4, 2*n'+9⟩,
             ⟨n'+3, by ring_nf⟩,
             general_trans⟩
  · exact ⟨0, rfl⟩

end Sz22_2003_unofficial_579
