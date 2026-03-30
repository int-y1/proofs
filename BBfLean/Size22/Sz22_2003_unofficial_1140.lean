import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #1140: [5/6, 44/35, 49/2, 9/11, 25/7]

Vector representation:
```
-1 -1  1  0  0
 2  0 -1 -1  1
-1  0  0  2  0
 0  2  0  0 -1
 0  0  2 -1  0
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_1140

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a+1, b+1, c, d, e⟩ => some ⟨a, b, c+1, d, e⟩
  | ⟨a, b, c+1, d+1, e⟩ => some ⟨a+2, b, c, d, e+1⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b, c, d+2, e⟩
  | ⟨a, b, c, d, e+1⟩ => some ⟨a, b+2, c, d, e⟩
  | ⟨a, b, c, d+1, e⟩ => some ⟨a, b, c+2, d, e⟩
  | _ => none

-- Phase 1: Interleaved R2/R1/R1 chain.
-- Each round: R2 (c≥1, d≥1, b=0), R1 (a≥1, b≥1), R1 (a≥1, b≥1).
-- Net: b -= 2, c += 1, d -= 1, e += 1.
theorem interleaved : ∀ k, ∀ b c d e,
    ⟨0, b + 2 * k, c + 1, d + k, e⟩ [fm]⊢* ⟨0, b, c + k + 1, d, e + k⟩ := by
  intro k; induction' k with k ih <;> intro b c d e
  · exists 0
  · rw [show b + 2 * (k + 1) = (b + 2 * k) + 2 from by ring,
        show d + (k + 1) = (d + k) + 1 from by ring]
    step fm  -- R2: (2, b+2k+2, c, d+k, e+1)
    step fm  -- R1: (1, b+2k+1, c+1, d+k, e+1)
    step fm  -- R1: (0, b+2k, c+2, d+k, e+1)
    apply stepStar_trans (ih b (c + 1) d (e + 1))
    ring_nf; finish

-- Phase 2: R2 chain (b=0, draining c and d simultaneously).
theorem r2_chain : ∀ k, ∀ a c d e,
    ⟨a, 0, c + k, d + k, e⟩ [fm]⊢* ⟨a + 2 * k, 0, c, d, e + k⟩ := by
  intro k; induction' k with k ih <;> intro a c d e
  · exists 0
  · rw [show c + (k + 1) = (c + k) + 1 from by ring,
        show d + (k + 1) = (d + k) + 1 from by ring]
    step fm  -- R2: (a+2, 0, c+k, d+k, e+1)
    apply stepStar_trans (ih (a + 2) c d (e + 1))
    ring_nf; finish

-- Phase 3: R3 drain (a to d, b=0, c=0).
theorem a_to_d : ∀ k, ∀ a d e,
    ⟨a + k, 0, 0, d, e⟩ [fm]⊢* ⟨a, 0, 0, d + 2 * k, e⟩ := by
  intro k; induction' k with k ih <;> intro a d e
  · exists 0
  · rw [show a + (k + 1) = (a + k) + 1 from by ring]
    step fm  -- R3: (a+k, 0, 0, d+2, e)
    apply stepStar_trans (ih a (d + 2) e)
    ring_nf; finish

-- Phase 4: R4 drain (e to b, a=0, c=0).
theorem e_to_b : ∀ k, ∀ b d e,
    ⟨0, b, 0, d, e + k⟩ [fm]⊢* ⟨0, b + 2 * k, 0, d, e⟩ := by
  intro k; induction' k with k ih <;> intro b d e
  · exists 0
  · rw [show e + (k + 1) = (e + k) + 1 from by ring]
    step fm  -- R4: (0, b+2, 0, d, e+k)
    apply stepStar_trans (ih (b + 2) d e)
    ring_nf; finish

-- Main transition: (0, 2k, 0, d, 0) ⊢⁺ (0, 4k+4, 0, d+2k+5, 0) when d ≥ 2k+3.
-- We write d = (2k+3) + m, so d' = (4k+8) + m = d + 2k + 5.
theorem main_trans (k m : ℕ) :
    ⟨0, 2 * k, 0, 2 * k + 3 + m, 0⟩ [fm]⊢⁺ ⟨0, 4 * k + 4, 0, 4 * k + 8 + m, 0⟩ := by
  -- Step 1: R5 kickoff
  rw [show 2 * k + 3 + m = (2 * k + 2 + m) + 1 from by ring]
  step fm  -- R5: (0, 2k, 2, 2k+2+m, 0)
  -- Step 2: Interleaved chain (k rounds)
  rw [show (2 : ℕ) = 1 + 1 from by ring,
      show 2 * k + 2 + m = (k + 2 + m) + k from by ring,
      show 2 * k = 0 + 2 * k from by ring]
  apply stepStar_trans (interleaved k 0 1 (k + 2 + m) 0)
  -- Now at (0, 0, 1+k+1, k+2+m, 0+k); massage for r2_chain
  rw [show 1 + k + 1 = 0 + (k + 2) from by ring,
      show k + 2 + m = m + (k + 2) from by ring]
  -- Step 3: R2 chain (k+2 rounds)
  apply stepStar_trans (r2_chain (k + 2) 0 0 m (0 + k))
  -- Now at (2*(k+2), 0, 0, m, 0+k+(k+2))
  rw [show 0 + 2 * (k + 2) = 0 + (2 * k + 4) from by ring,
      show 0 + k + (k + 2) = 2 * k + 2 from by ring]
  -- Step 4: R3 drain (2k+4 rounds)
  apply stepStar_trans (a_to_d (2 * k + 4) 0 m (2 * k + 2))
  -- Now at (0, 0, 0, m+2*(2k+4), 2k+2)
  rw [show m + 2 * (2 * k + 4) = 4 * k + 8 + m from by ring,
      show (2 * k + 2 : ℕ) = 0 + (2 * k + 2) from by ring]
  -- Step 5: R4 drain (2k+2 rounds)
  apply stepStar_trans (e_to_b (2 * k + 2) 0 (4 * k + 8 + m) 0)
  ring_nf; finish

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨0, 4, 0, 7, 0⟩) (by execute fm 10)
  apply progress_nonhalt (fm := fm)
    (P := fun q ↦ ∃ k m, q = ⟨0, 2 * k, 0, 2 * k + 3 + m, 0⟩)
  · intro c ⟨k, m, hq⟩; subst hq
    exact ⟨⟨0, 4 * k + 4, 0, 4 * k + 8 + m, 0⟩,
      ⟨2 * k + 2, m + 1, by ring_nf⟩, main_trans k m⟩
  · exact ⟨2, 0, by ring_nf⟩

end Sz22_2003_unofficial_1140
