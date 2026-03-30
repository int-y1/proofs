import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #793: [35/6, 605/2, 4/77, 3/5, 14/11]

Vector representation:
```
-1 -1  1  1  0
-1  0  1  0  2
 2  0  0 -1 -1
 0  1 -1  0  0
 1  0  0  1 -1
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_793

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a+1, b+1, c, d, e⟩ => some ⟨a, b, c+1, d+1, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b, c+1, d, e+2⟩
  | ⟨a, b, c, d+1, e+1⟩ => some ⟨a+2, b, c, d, e⟩
  | ⟨a, b, c+1, d, e⟩ => some ⟨a, b+1, c, d, e⟩
  | ⟨a, b, c, d, e+1⟩ => some ⟨a+1, b, c, d+1, e⟩
  | _ => none

-- Phase 1: Move c to b via R4. (0, b, c+k, 0, e) →* (0, b+k, c, 0, e)
theorem c_to_b : ∀ k, ⟨0, b, c + k, 0, e⟩ [fm]⊢* ⟨0, b + k, c, 0, e⟩ := by
  intro k; induction' k with k ih generalizing b c
  · exists 0
  · rw [show c + (k + 1) = c + k + 1 from by ring]
    step fm
    apply stepStar_trans (ih (b := b + 1) (c := c))
    ring_nf; finish

-- R1,R1,R3 chain. (2, 2j, c, d, e+j) →* (2, 0, c+2j, d+j, e)
theorem r1r1r3_chain : ∀ j, ⟨2, 2 * j, c, d, e + j⟩ [fm]⊢* ⟨2, 0, c + 2 * j, d + j, e⟩ := by
  intro j; induction' j with j ih generalizing c d e
  · exists 0
  · rw [show 2 * (j + 1) = (2 * j + 1) + 1 from by ring,
        show e + (j + 1) = (e + 1) + j from by ring]
    step fm
    step fm
    rw [show (e + 1) + j = (e + j) + 1 from by ring]
    step fm
    apply stepStar_trans (ih (c := c + 2) (d := d + 1) (e := e))
    ring_nf; finish

-- Phase 2: Interleave. (0, 2k+1, 0, 0, e+k+2) →* (2, 0, 2k+1, k+1, e)
theorem interleave : ⟨0, 2 * k + 1, 0, 0, e + k + 2⟩ [fm]⊢* ⟨2, 0, 2 * k + 1, k + 1, e⟩ := by
  rw [show e + k + 2 = e + k + 1 + 1 from by ring]
  step fm  -- R5
  rw [show e + k + 1 = (e + k) + 1 from by ring]
  step fm  -- R1
  step fm  -- R3
  apply stepStar_trans (r1r1r3_chain k (c := 1) (d := 1) (e := e))
  ring_nf; finish

-- Phase 3: Two R2 steps. (2, 0, c, d, e) →⁺ (0, 0, c+2, d, e+4)
theorem r2_twice : ⟨2, 0, c, d, e⟩ [fm]⊢⁺ ⟨0, 0, c + 2, d, e + 4⟩ := by
  step fm; step fm; finish

-- Phase 4: R3,R2,R2 chain. (0, 0, c, d+K, e+1) →* (0, 0, c+2*K, d, e+3*K+1)
theorem r3r2r2_chain : ∀ K, ⟨0, 0, c, d + K, e + 1⟩ [fm]⊢* ⟨0, 0, c + 2 * K, d, e + 3 * K + 1⟩ := by
  intro K; induction' K with K ih generalizing c d e
  · exists 0
  · rw [show d + (K + 1) = (d + K) + 1 from by ring]
    step fm
    step fm
    step fm
    rw [show e + 4 = (e + 3) + 1 from by ring]
    apply stepStar_trans (ih (c := c + 2) (d := d) (e := e + 3))
    ring_nf; finish

-- Main transition: (0, 0, 2k+1, 0, e) →⁺ (0, 0, 4k+5, 0, e+2k+5) for e >= k+2
theorem main_trans (he : e ≥ k + 2) :
    ⟨0, 0, 2 * k + 1, 0, e⟩ [fm]⊢⁺ ⟨0, 0, 4 * k + 5, 0, e + 2 * k + 5⟩ := by
  obtain ⟨e', rfl⟩ : ∃ e', e = e' + k + 2 := ⟨e - k - 2, by omega⟩
  -- Phase 1: c_to_b: (0, 0, 2k+1, 0, e'+k+2) →* (0, 2k+1, 0, 0, e'+k+2)
  have phase1 : ⟨0, 0, 2 * k + 1, 0, e' + k + 2⟩ [fm]⊢* ⟨0, 2 * k + 1, 0, 0, e' + k + 2⟩ := by
    rw [show (2 * k + 1 : ℕ) = 0 + (2 * k + 1) from by ring]
    apply stepStar_trans (c_to_b (2 * k + 1) (b := 0) (c := 0) (e := e' + k + 2))
    ring_nf; finish
  -- Phase 2: interleave: (0, 2k+1, 0, 0, e'+k+2) →* (2, 0, 2k+1, k+1, e')
  apply stepStar_stepPlus_stepPlus phase1
  apply stepStar_stepPlus_stepPlus (interleave (k := k) (e := e'))
  -- Phase 3: r2_twice: (2, 0, 2k+1, k+1, e') →⁺ (0, 0, 2k+3, k+1, e'+4)
  apply stepPlus_stepStar_stepPlus r2_twice
  -- Phase 4: r3r2r2_chain
  have phase4 : ⟨0, 0, 2 * k + 3, k + 1, e' + 4⟩ [fm]⊢* ⟨0, 0, 4 * k + 5, 0, e' + k + 2 + 2 * k + 5⟩ := by
    rw [show e' + 4 = (e' + 3) + 1 from by ring,
        show (k + 1 : ℕ) = 0 + (k + 1) from by ring]
    apply stepStar_trans (r3r2r2_chain (k + 1) (c := 2 * k + 3) (d := 0) (e := e' + 3))
    ring_nf; finish
  exact phase4

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨0, 0, 5, 0, 7⟩) (by execute fm 10)
  apply progress_nonhalt (fm := fm)
    (P := fun q ↦ ∃ k e, q = ⟨0, 0, 2 * k + 1, 0, e⟩ ∧ k ≥ 2 ∧ e ≥ k + 2)
  · intro q ⟨k, e, hq, hk, he⟩; subst hq
    exact ⟨⟨0, 0, 4 * k + 5, 0, e + 2 * k + 5⟩,
      ⟨2 * k + 2, e + 2 * k + 5, by ring_nf, by omega, by omega⟩,
      main_trans he⟩
  · exact ⟨2, 7, rfl, by omega, by omega⟩
