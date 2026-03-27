import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #603: [35/6, 121/2, 4/55, 3/7, 30/11]

Vector representation:
```
-1 -1  1  1  0
-1  0  0  0  2
 2  0 -1  0 -1
 0  1  0 -1  0
 1  1  1  0 -1
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_603

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a+1, b+1, c, d, e⟩ => some ⟨a, b, c+1, d+1, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b, c, d, e+2⟩
  | ⟨a, b, c+1, d, e+1⟩ => some ⟨a+2, b, c, d, e⟩
  | ⟨a, b, c, d+1, e⟩ => some ⟨a, b+1, c, d, e⟩
  | ⟨a, b, c, d, e+1⟩ => some ⟨a+1, b+1, c+1, d, e⟩
  | _ => none

-- R4 repeated: convert d to b
theorem d_to_b : ∀ k b, ⟨0, b, 0, k, e⟩ [fm]⊢* ⟨0, b+k, 0, 0, e⟩ := by
  intro k; induction' k with k h <;> intro b
  · exists 0
  step fm
  apply stepStar_trans (h _)
  ring_nf; finish

-- R3R2R2 drain: (0,0,c+k,D+1,e+1) ->* (0,0,c,D+1,e+1+3*k)
theorem r3r2r2_drain : ∀ k c e, ⟨0, 0, c+k, D+1, e+1⟩ [fm]⊢* ⟨0, 0, c, D+1, e+1+3*k⟩ := by
  intro k; induction' k with k h <;> intro c e
  · exists 0
  rw [show c + (k + 1) = (c + k) + 1 from by ring]
  step fm; step fm; step fm
  apply stepStar_trans (h _ _)
  ring_nf; finish

-- R1R1R3 chain: iterate k rounds of (R1,R1,R3)
theorem r1r1r3_chain : ∀ k c d e, ⟨2, B+2*k, c, d, e+k⟩ [fm]⊢* ⟨2, B, c+k, d+2*k, e⟩ := by
  intro k; induction' k with k h <;> intro c d e
  · exists 0
  rw [show B + 2 * (k + 1) = (B + 2 * k) + 2 from by ring,
      show e + (k + 1) = (e + k) + 1 from by ring]
  step fm; step fm; step fm
  apply stepStar_trans (h _ _ _)
  ring_nf; finish

-- Full transition for even d: (0,0,0,2k,e+2k+2) ->+ (0,0,0,2k+1,e+4k+7)
theorem even_trans {k e : ℕ} : ⟨0, 0, 0, 2*k, e+2*k+2⟩ [fm]⊢⁺ ⟨0, 0, 0, 2*k+1, e+4*k+7⟩ := by
  -- R4 chain
  apply stepStar_stepPlus_stepPlus (d_to_b (e := e+2*k+2) (2*k) 0)
  simp only [Nat.zero_add]
  -- R5
  rw [show e + 2 * k + 2 = (e + 2 * k + 1) + 1 from by ring]
  step fm
  -- R1
  step fm
  -- R3
  rw [show e + 2 * k + 1 = (e + 2 * k) + 1 from by ring]
  step fm
  -- R1R1R3 chain k rounds
  rw [show (2:ℕ) * k = 0 + 2 * k from by ring,
      show e + (0 + 2 * k) = (e + k) + k from by ring]
  apply stepStar_trans (r1r1r3_chain (B := 0) k 1 1 (e+k))
  simp only [Nat.zero_add]
  -- R2, R2
  step fm; step fm
  -- R3R2R2 drain
  rw [show 1 + k = 0 + (k + 1) from by ring,
      show 1 + 2 * k = (2 * k) + 1 from by ring,
      show e + k + 2 + 2 = (e + k + 3) + 1 from by ring]
  apply stepStar_trans (r3r2r2_drain (D := 2*k) (k+1) 0 (e+k+3))
  ring_nf; finish

-- Full transition for odd d: (0,0,0,2k+1,e+2k+3) ->+ (0,0,0,2k+2,e+4k+9)
theorem odd_trans {k e : ℕ} : ⟨0, 0, 0, 2*k+1, e+2*k+3⟩ [fm]⊢⁺ ⟨0, 0, 0, 2*k+2, e+4*k+9⟩ := by
  -- R4 chain
  apply stepStar_stepPlus_stepPlus (d_to_b (e := e+2*k+3) (2*k+1) 0)
  simp only [Nat.zero_add]
  -- R5
  rw [show e + 2 * k + 3 = (e + 2 * k + 2) + 1 from by ring]
  step fm
  -- R1
  step fm
  -- R3
  rw [show e + 2 * k + 2 = (e + 2 * k + 1) + 1 from by ring]
  step fm
  -- R1R1R3 chain k rounds
  rw [show 2 * k + 1 = 1 + 2 * k from by ring,
      show e + 2 * k + 1 = (e + k + 1) + k from by ring]
  apply stepStar_trans (r1r1r3_chain (B := 1) k 1 1 (e+k+1))
  -- R1, R2
  step fm; step fm
  -- R3R2R2 drain
  rw [show 1 + k + 1 = 0 + (k + 2) from by ring,
      show 1 + 2 * k + 1 = (2 * k + 1) + 1 from by ring,
      show e + k + 1 + 2 = (e + k + 2) + 1 from by ring]
  apply stepStar_trans (r3r2r2_drain (D := 2*k+1) (k+2) 0 (e+k+2))
  ring_nf; finish

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨0, 0, 0, 0, 2⟩) (by execute fm 1)
  apply progress_nonhalt (fm := fm)
    (P := fun q ↦ ∃ d e, q = ⟨0, 0, 0, d, e⟩ ∧ e ≥ d + 2)
  · intro c ⟨d, e, hq, he⟩; subst hq
    rcases Nat.even_or_odd d with ⟨K, hK⟩ | ⟨K, hK⟩
    · rw [show K + K = 2 * K from by ring] at hK; subst hK
      obtain ⟨E, rfl⟩ : ∃ E, e = E + 2 * K + 2 := ⟨e - 2 * K - 2, by omega⟩
      exact ⟨⟨0, 0, 0, 2*K+1, E+4*K+7⟩,
        ⟨2*K+1, E+4*K+7, rfl, by omega⟩, even_trans⟩
    · subst hK
      obtain ⟨E, rfl⟩ : ∃ E, e = E + 2 * K + 3 := ⟨e - 2 * K - 3, by omega⟩
      exact ⟨⟨0, 0, 0, 2*K+2, E+4*K+9⟩,
        ⟨2*K+2, E+4*K+9, rfl, by omega⟩, odd_trans⟩
  · exact ⟨0, 2, rfl, by omega⟩
