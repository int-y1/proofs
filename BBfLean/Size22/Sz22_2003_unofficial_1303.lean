import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #1303: [63/10, 121/2, 4/33, 5/7, 10/11]

Vector representation:
```
-1  2 -1  1  0
-1  0  0  0  2
 2 -1  0  0 -1
 0  0  1 -1  0
 1  0  1  0 -1
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_1303

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a+1, b, c+1, d, e⟩ => some ⟨a, b+2, c, d+1, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b, c, d, e+2⟩
  | ⟨a, b+1, c, d, e+1⟩ => some ⟨a+2, b, c, d, e⟩
  | ⟨a, b, c, d+1, e⟩ => some ⟨a, b, c+1, d, e⟩
  | ⟨a, b, c, d, e+1⟩ => some ⟨a+1, b, c+1, d, e⟩
  | _ => none

-- R4 chain: transfer d to c. (0, 0, c, d+k, e) →* (0, 0, c+k, d, e)
theorem d_to_c : ∀ k, ∀ c d, ⟨0, 0, c, d + k, e⟩ [fm]⊢* ⟨0, 0, c + k, d, e⟩ := by
  intro k; induction' k with k ih <;> intro c d
  · exists 0
  · rw [show d + (k + 1) = (d + k) + 1 from by ring]
    step fm
    apply stepStar_trans (ih (c + 1) d)
    rw [show c + 1 + k = c + (k + 1) from by ring]; finish

-- Super-round chain: R3, R1, R1 repeated k times, consuming 2k from c.
-- (0, b+1, c+2*k, d, e+k) →* (0, b+1+3*k, c, d+2*k, e)
theorem super_round_chain : ∀ k, ∀ b c d e,
    ⟨0, b + 1, c + 2 * k, d, e + k⟩ [fm]⊢* ⟨0, b + 1 + 3 * k, c, d + 2 * k, e⟩ := by
  intro k; induction' k with k ih <;> intro b c d e
  · exists 0
  · rw [show c + 2 * (k + 1) = (c + 2 * k) + 2 from by ring,
        show e + (k + 1) = (e + k) + 1 from by ring]
    -- R3: (2, b, c+2k+2, d, e+k)
    step fm
    -- R1: (1, b+2, c+2k+1, d+1, e+k)
    rw [show c + 2 * k + 2 = (c + 2 * k + 1) + 1 from by ring]
    step fm
    -- R1: (0, b+4, c+2k, d+2, e+k)
    rw [show c + 2 * k + 1 = (c + 2 * k) + 1 from by ring]
    step fm
    rw [show b + 4 = (b + 3) + 1 from by ring]
    apply stepStar_trans (ih (b + 3) c (d + 2) e)
    ring_nf; finish

-- Final round for odd case: R3, R1, R2 when c=1.
-- (0, b+1, 1, d, e+1) →* (0, b+2, 0, d+1, e+2)
theorem final_round : ⟨0, b + 1, 1, d, e + 1⟩ [fm]⊢* ⟨0, b + 2, 0, d + 1, e + 2⟩ := by
  step fm  -- R3: (2, b, 1, d, e)
  step fm  -- R1: (1, b+2, 0, d+1, e)
  step fm  -- R2: (0, b+2, 0, d+1, e+2)
  finish

-- Drain: R3, R2, R2 repeated. (0, k, 0, d, e+1) →* (0, 0, 0, d, e+1+3*k)
theorem drain : ∀ k, ∀ d e, ⟨0, k, 0, d, e + 1⟩ [fm]⊢* ⟨0, 0, 0, d, e + 1 + 3 * k⟩ := by
  intro k; induction' k with k ih <;> intro d e
  · exists 0
  · show ⟨0, k + 1, 0, d, e + 1⟩ [fm]⊢* _
    step fm  -- R3: (2, k, 0, d, e)
    step fm  -- R2: (1, k, 0, d, e+2)
    step fm  -- R2: (0, k, 0, d, e+4)
    rw [show e + 4 = (e + 3) + 1 from by ring]
    apply stepStar_trans (ih d (e + 3))
    ring_nf; finish

-- Even transition: d = 2k.
-- (0, 0, 0, 2k, 8k²+6k+2) →⁺ (0, 0, 0, 2k+1, 8k²+14k+7)
theorem even_trans (k : ℕ) :
    ⟨0, 0, 0, 2 * k, 8 * k ^ 2 + 6 * k + 2⟩ [fm]⊢⁺
    ⟨0, 0, 0, 2 * k + 1, 8 * k ^ 2 + 14 * k + 7⟩ := by
  -- Phase 1: d_to_c
  have h1 : ⟨0, 0, 0, 2 * k, 8 * k ^ 2 + 6 * k + 2⟩ [fm]⊢*
      ⟨0, 0, 2 * k, 0, 8 * k ^ 2 + 6 * k + 2⟩ := by
    rw [show (2 * k : ℕ) = 0 + 2 * k from by ring]
    exact d_to_c (2 * k) 0 0
  -- Phase 2: R5 + R1
  have h2 : ⟨0, 0, 2 * k, 0, 8 * k ^ 2 + 6 * k + 2⟩ [fm]⊢⁺
      ⟨0, 2, 2 * k, 1, 8 * k ^ 2 + 6 * k + 1⟩ := by
    rw [show 8 * k ^ 2 + 6 * k + 2 = (8 * k ^ 2 + 6 * k + 1) + 1 from by ring]
    step fm  -- R5: (1, 0, 2k+1, 0, 8k²+6k+1)
    rw [show 2 * k + 1 = (2 * k) + 1 from by ring]
    step fm  -- R1: (0, 2, 2k, 1, 8k²+6k+1)
    finish
  -- Phase 3: super_round_chain k rounds
  have h3 : ⟨0, 2, 2 * k, 1, 8 * k ^ 2 + 6 * k + 1⟩ [fm]⊢*
      ⟨0, 3 * k + 2, 0, 2 * k + 1, 8 * k ^ 2 + 5 * k + 1⟩ := by
    rw [show (2 : ℕ) = 1 + 1 from by ring,
        show (2 * k : ℕ) = 0 + 2 * k from by ring,
        show 8 * k ^ 2 + 6 * k + 1 = (8 * k ^ 2 + 5 * k + 1) + k from by ring]
    apply stepStar_trans (super_round_chain k 1 0 1 (8 * k ^ 2 + 5 * k + 1))
    ring_nf; finish
  -- Phase 4: drain (3k+2 rounds)
  have h4 : ⟨0, 3 * k + 2, 0, 2 * k + 1, 8 * k ^ 2 + 5 * k + 1⟩ [fm]⊢*
      ⟨0, 0, 0, 2 * k + 1, 8 * k ^ 2 + 14 * k + 7⟩ := by
    rw [show 3 * k + 2 = 3 * k + 2 from rfl,
        show 8 * k ^ 2 + 5 * k + 1 = (8 * k ^ 2 + 5 * k) + 1 from by ring]
    apply stepStar_trans (drain (3 * k + 2) (2 * k + 1) (8 * k ^ 2 + 5 * k))
    ring_nf; finish
  -- Compose: h1 (⊢*) + h2 (⊢⁺) + h3 (⊢*) + h4 (⊢*)
  exact stepStar_stepPlus_stepPlus h1
    (stepPlus_stepStar_stepPlus h2
      (stepStar_trans h3 h4))

-- Odd transition: d = 2k+1.
-- (0, 0, 0, 2k+1, 8k²+14k+7) →⁺ (0, 0, 0, 2k+2, 8k²+22k+16)
theorem odd_trans (k : ℕ) :
    ⟨0, 0, 0, 2 * k + 1, 8 * k ^ 2 + 14 * k + 7⟩ [fm]⊢⁺
    ⟨0, 0, 0, 2 * k + 2, 8 * k ^ 2 + 22 * k + 16⟩ := by
  -- Phase 1: d_to_c
  have h1 : ⟨0, 0, 0, 2 * k + 1, 8 * k ^ 2 + 14 * k + 7⟩ [fm]⊢*
      ⟨0, 0, 2 * k + 1, 0, 8 * k ^ 2 + 14 * k + 7⟩ := by
    rw [show (2 * k + 1 : ℕ) = 0 + (2 * k + 1) from by ring]
    exact d_to_c (2 * k + 1) 0 0
  -- Phase 2: R5 + R1
  have h2 : ⟨0, 0, 2 * k + 1, 0, 8 * k ^ 2 + 14 * k + 7⟩ [fm]⊢⁺
      ⟨0, 2, 2 * k + 1, 1, 8 * k ^ 2 + 14 * k + 6⟩ := by
    rw [show 8 * k ^ 2 + 14 * k + 7 = (8 * k ^ 2 + 14 * k + 6) + 1 from by ring]
    step fm  -- R5: (1, 0, 2k+2, 0, 8k²+14k+6)
    rw [show 2 * k + 2 = (2 * k + 1) + 1 from by ring]
    step fm  -- R1: (0, 2, 2k+1, 1, 8k²+14k+6)
    finish
  -- Phase 3: super_round_chain k rounds
  have h3 : ⟨0, 2, 2 * k + 1, 1, 8 * k ^ 2 + 14 * k + 6⟩ [fm]⊢*
      ⟨0, 3 * k + 2, 1, 2 * k + 1, 8 * k ^ 2 + 13 * k + 6⟩ := by
    rw [show (2 : ℕ) = 1 + 1 from by ring,
        show 2 * k + 1 = 1 + 2 * k from by ring,
        show 8 * k ^ 2 + 14 * k + 6 = (8 * k ^ 2 + 13 * k + 6) + k from by ring]
    apply stepStar_trans (super_round_chain k 1 1 1 (8 * k ^ 2 + 13 * k + 6))
    ring_nf; finish
  -- Phase 4: final_round
  have h4 : ⟨0, 3 * k + 2, 1, 2 * k + 1, 8 * k ^ 2 + 13 * k + 6⟩ [fm]⊢*
      ⟨0, 3 * k + 3, 0, 2 * k + 2, 8 * k ^ 2 + 13 * k + 7⟩ := by
    rw [show 3 * k + 2 = (3 * k + 1) + 1 from by ring,
        show 8 * k ^ 2 + 13 * k + 6 = (8 * k ^ 2 + 13 * k + 5) + 1 from by ring]
    apply stepStar_trans
      (final_round (b := 3 * k + 1) (d := 2 * k + 1) (e := 8 * k ^ 2 + 13 * k + 5))
    ring_nf; finish
  -- Phase 5: drain (3k+3 rounds)
  have h5 : ⟨0, 3 * k + 3, 0, 2 * k + 2, 8 * k ^ 2 + 13 * k + 7⟩ [fm]⊢*
      ⟨0, 0, 0, 2 * k + 2, 8 * k ^ 2 + 22 * k + 16⟩ := by
    rw [show 8 * k ^ 2 + 13 * k + 7 = (8 * k ^ 2 + 13 * k + 6) + 1 from by ring]
    apply stepStar_trans (drain (3 * k + 3) (2 * k + 2) (8 * k ^ 2 + 13 * k + 6))
    ring_nf; finish
  -- Compose
  exact stepStar_stepPlus_stepPlus h1
    (stepPlus_stepStar_stepPlus h2
      (stepStar_trans h3 (stepStar_trans h4 h5)))

-- Main transition composing even and odd.
theorem main_trans (d : ℕ) :
    ⟨0, 0, 0, d, 2 * d ^ 2 + 3 * d + 2⟩ [fm]⊢⁺
    ⟨0, 0, 0, d + 1, 2 * (d + 1) ^ 2 + 3 * (d + 1) + 2⟩ := by
  rcases Nat.even_or_odd d with ⟨k, hk⟩ | ⟨k, hk⟩
  · -- d = 2k
    rw [show k + k = 2 * k from by ring] at hk; subst hk
    have : 2 * (2 * k) ^ 2 + 3 * (2 * k) + 2 = 8 * k ^ 2 + 6 * k + 2 := by ring
    have : 2 * (2 * k + 1) ^ 2 + 3 * (2 * k + 1) + 2 = 8 * k ^ 2 + 14 * k + 7 := by ring
    rw [‹2 * (2 * k) ^ 2 + 3 * (2 * k) + 2 = _›,
        ‹2 * (2 * k + 1) ^ 2 + 3 * (2 * k + 1) + 2 = _›]
    exact even_trans k
  · -- d = 2k+1
    subst hk
    have : 2 * (2 * k + 1) ^ 2 + 3 * (2 * k + 1) + 2 = 8 * k ^ 2 + 14 * k + 7 := by ring
    have : 2 * (2 * k + 1 + 1) ^ 2 + 3 * (2 * k + 1 + 1) + 2 = 8 * k ^ 2 + 22 * k + 16 := by
      ring
    rw [‹2 * (2 * k + 1) ^ 2 + 3 * (2 * k + 1) + 2 = _›,
        ‹2 * (2 * k + 1 + 1) ^ 2 + 3 * (2 * k + 1 + 1) + 2 = _›]
    exact odd_trans k

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨0, 0, 0, 0, 2⟩) (by execute fm 1)
  have : ⟨0, 0, 0, 0, 2⟩ = (fun d : ℕ ↦ (⟨0, 0, 0, d, 2 * d ^ 2 + 3 * d + 2⟩ : Q)) 0 := by
    simp
  rw [this]
  apply progress_nonhalt_simple (fm := fm) (A := ℕ)
    (fun d ↦ ⟨0, 0, 0, d, 2 * d ^ 2 + 3 * d + 2⟩) 0
  intro d; exists d + 1
  exact main_trans d
