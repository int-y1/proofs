import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #1093: [5/6, 3/385, 28/5, 77/2, 25/7]

Vector representation:
```
-1 -1  1  0  0
 0  1 -1 -1 -1
 2  0 -1  1  0
-1  0  0  1  1
 0  0  2 -1  0
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_1093

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a+1, b+1, c, d, e⟩ => some ⟨a, b, c+1, d, e⟩
  | ⟨a, b, c+1, d+1, e+1⟩ => some ⟨a, b+1, c, d, e⟩
  | ⟨a, b, c+1, d, e⟩ => some ⟨a+2, b, c, d+1, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b, c, d+1, e+1⟩
  | ⟨a, b, c, d+1, e⟩ => some ⟨a, b, c+2, d, e⟩
  | _ => none

-- R4 chain: (a+k, 0, 0, d, e) →* (a, 0, 0, d+k, e+k)
theorem r4_chain : ∀ k a d e, ⟨a + k, 0, 0, d, e⟩ [fm]⊢* ⟨a, 0, 0, d + k, e + k⟩ := by
  intro k; induction' k with k ih <;> intro a d e
  · exists 0
  · rw [show a + (k + 1) = (a + k) + 1 from by ring]
    step fm
    apply stepStar_trans (ih a (d + 1) (e + 1))
    ring_nf; finish

-- R5+R2+R2 drain: (0, b, 0, d+3*K, e+2*K) →* (0, b+2*K, 0, d, e)
theorem drain : ∀ K b d e, ⟨0, b, 0, d + 3 * K, e + 2 * K⟩ [fm]⊢* ⟨0, b + 2 * K, 0, d, e⟩ := by
  intro K; induction' K with K ih <;> intro b d e
  · exists 0
  · rw [show d + 3 * (K + 1) = (d + 3) + 3 * K from by ring,
        show e + 2 * (K + 1) = (e + 2) + 2 * K from by ring]
    apply stepStar_trans (ih b (d + 3) (e + 2))
    step fm; step fm; step fm; ring_nf; finish

-- Final drain: (0, b, 0, D+2, 1) →⁺ (2, b+1, 0, D+1, 0)
theorem final_drain : ⟨0, b, 0, D + 2, 1⟩ [fm]⊢⁺ ⟨2, b + 1, 0, D + 1, 0⟩ := by
  step fm; step fm; step fm; finish

-- One build step: (2, b+2, c, d, 0) →* (2, b, c+1, d+1, 0)
theorem build_step : ⟨2, b + 2, c, d, 0⟩ [fm]⊢* ⟨2, b, c + 1, d + 1, 0⟩ := by
  step fm; step fm; step fm; finish

-- R1+R1+R3 build: (2, 2*K+b, j, d, 0) →* (2, b, j+K, d+K, 0)
theorem build : ∀ K b j d, ⟨2, 2 * K + b, j, d, 0⟩ [fm]⊢* ⟨2, b, j + K, d + K, 0⟩ := by
  intro K; induction' K with K ih <;> intro b j d
  · simp; exists 0
  · rw [show 2 * (K + 1) + b = (2 * K + b) + 2 from by ring]
    apply stepStar_trans (build_step (b := 2 * K + b) (c := j) (d := d))
    apply stepStar_trans (ih b (j + 1) (d + 1))
    rw [show j + 1 + K = j + (K + 1) from by ring,
        show d + 1 + K = d + (K + 1) from by ring]
    finish

-- R3 chain: (a, 0, K, d, 0) →* (a+2*K, 0, 0, d+K, 0)
theorem r3_chain : ∀ K a d, ⟨a, 0, K, d, 0⟩ [fm]⊢* ⟨a + 2 * K, 0, 0, d + K, 0⟩ := by
  intro K; induction' K with K ih <;> intro a d
  · exists 0
  · step fm
    apply stepStar_trans (ih (a + 2) (d + 1))
    ring_nf; finish

-- Main transition: (2k+5, 0, 0, d, 0) →⁺ (2k+7, 0, 0, d+k+3, 0) when d ≥ k+3
theorem main_transition (hd : d ≥ k + 3) :
    ⟨2 * k + 5, 0, 0, d, 0⟩ [fm]⊢⁺ ⟨2 * k + 7, 0, 0, d + k + 3, 0⟩ := by
  obtain ⟨d', rfl⟩ : ∃ d', d = d' + (k + 3) := ⟨d - (k + 3), by omega⟩
  -- Phase 1: R4 chain
  -- (2k+5, 0, 0, d'+k+3, 0) →* (0, 0, 0, d'+k+3+2k+5, 0+2k+5)
  rw [show (2 * k + 5 : ℕ) = 0 + (2 * k + 5) from by ring]
  apply stepStar_stepPlus_stepPlus (r4_chain (2 * k + 5) 0 (d' + (k + 3)) 0)
  -- After R4: (0, 0, 0, d'+3k+8, 2k+5)
  -- Phase 2: drain (k+2) triples
  rw [show d' + (k + 3) + (2 * k + 5) = (d' + 2) + 3 * (k + 2) from by ring,
      show (0 + (2 * k + 5) : ℕ) = 1 + 2 * (k + 2) from by ring]
  apply stepStar_stepPlus_stepPlus (drain (k + 2) 0 (d' + 2) 1)
  -- After drain: (0, 2k+4, 0, d'+2, 1)
  -- Phase 3: final drain
  rw [show (0 + 2 * (k + 2) : ℕ) = 2 * k + 4 from by ring]
  apply stepPlus_stepStar_stepPlus (final_drain (b := 2 * k + 4) (D := d'))
  -- After final drain: (2, 2k+5, 0, d'+1, 0)
  rw [show (2 * k + 4 + 1 : ℕ) = 2 * k + 5 from by ring]
  -- Phase 4: build (k+2) triples
  rw [show (2 * k + 5 : ℕ) = 2 * (k + 2) + 1 from by ring]
  apply stepStar_trans (build (k + 2) 1 0 (d' + 1))
  -- After build: (2, 1, k+2, d'+1+k+2, 0) = (2, 1, k+2, d'+k+3, 0)
  -- Phase 5: R1 step
  rw [show (0 + (k + 2) : ℕ) = k + 2 from by ring,
      show d' + 1 + (k + 2) = d' + k + 3 from by ring]
  step fm
  -- After R1: (1, 0, k+3, d'+k+3, 0)
  -- Phase 6: R3 chain
  apply stepStar_trans (r3_chain (k + 3) 1 (d' + k + 3))
  rw [show 1 + 2 * (k + 3) = 2 * k + 7 from by ring,
      show d' + k + 3 + (k + 3) = d' + (k + 3) + k + 3 from by ring]
  finish

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨5, 0, 0, 3, 0⟩)
  · execute fm 21
  apply progress_nonhalt (fm := fm)
    (P := fun q ↦ ∃ k d, q = ⟨2 * k + 5, 0, 0, d, 0⟩ ∧ d ≥ k + 3)
  · intro c ⟨k, d, hq, hd⟩; subst hq
    exact ⟨⟨2 * k + 7, 0, 0, d + k + 3, 0⟩,
      ⟨k + 1, d + k + 3, by ring_nf, by omega⟩,
      main_transition hd⟩
  · exact ⟨0, 3, rfl, by omega⟩

end Sz22_2003_unofficial_1093
