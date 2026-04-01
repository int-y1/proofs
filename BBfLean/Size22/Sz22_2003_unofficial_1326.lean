import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #1326: [63/10, 2/33, 121/2, 5/7, 14/11]

Vector representation:
```
-1  2 -1  1  0
 1 -1  0  0 -1
-1  0  0  0  2
 0  0  1 -1  0
 1  0  0  1 -1
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_1326

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a+1, b, c+1, d, e⟩ => some ⟨a, b+2, c, d+1, e⟩
  | ⟨a, b+1, c, d, e+1⟩ => some ⟨a+1, b, c, d, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b, c, d, e+2⟩
  | ⟨a, b, c, d+1, e⟩ => some ⟨a, b, c+1, d, e⟩
  | ⟨a, b, c, d, e+1⟩ => some ⟨a+1, b, c, d+1, e⟩
  | _ => none

-- R4 chain: transfer d to c
theorem d_to_c : ∀ k, ∀ c d e,
    ⟨(0 : ℕ), (0 : ℕ), c, d + k, e⟩ [fm]⊢* ⟨(0 : ℕ), (0 : ℕ), c + k, d, e⟩ := by
  intro k; induction' k with k ih <;> intro c d e
  · exists 0
  · rw [show d + (k + 1) = (d + k) + 1 from by ring]
    step fm
    apply stepStar_trans (ih (c + 1) d e)
    ring_nf; finish

-- R1+R2 interleaved chain
theorem r1r2_chain : ∀ k, ∀ b d e,
    ⟨(1 : ℕ), b, k, d, e + k⟩ [fm]⊢* ⟨(1 : ℕ), b + k, (0 : ℕ), d + k, e⟩ := by
  intro k; induction' k with k ih <;> intro b d e
  · exists 0
  · rw [show e + (k + 1) = (e + k) + 1 from by ring,
        show (k : ℕ) + 1 = k + 1 from rfl]
    step fm
    step fm
    apply stepStar_trans (ih (b + 1) (d + 1) e)
    ring_nf; finish

-- R2 chain: when both b and e have +k structure
theorem r2_chain : ∀ k, ∀ a b d e,
    ⟨a, b + k, (0 : ℕ), d, e + k⟩ [fm]⊢* ⟨a + k, b, (0 : ℕ), d, e⟩ := by
  intro k; induction' k with k ih <;> intro a b d e
  · exists 0
  · rw [show b + (k + 1) = (b + k) + 1 from by ring,
        show e + (k + 1) = (e + k) + 1 from by ring]
    step fm
    apply stepStar_trans (ih (a + 1) b d e)
    ring_nf; finish

-- R3 chain: drain a when b=0
theorem r3_chain : ∀ k, ∀ d e,
    ⟨k, (0 : ℕ), (0 : ℕ), d, e⟩ [fm]⊢* ⟨(0 : ℕ), (0 : ℕ), (0 : ℕ), d, e + 2 * k⟩ := by
  intro k; induction' k with k ih <;> intro d e
  · exists 0
  · rw [show (k : ℕ) + 1 = k + 1 from rfl]
    step fm
    apply stepStar_trans (ih d (e + 2))
    ring_nf; finish

-- Shrink round: R3 then R2×2, decreases b by 2, increases a by 1
theorem shrink_round : ∀ a b D,
    ⟨a + 1, b + 2, (0 : ℕ), D, (0 : ℕ)⟩ [fm]⊢* ⟨a + 2, b, (0 : ℕ), D, (0 : ℕ)⟩ := by
  intro a b D
  step fm  -- R3: (a, b+2, 0, D, 2)
  step fm  -- R2: (a+1, b+1, 0, D, 1)
  step fm  -- R2: (a+2, b, 0, D, 0)
  finish

-- Shrink chain with b=0: iterate shrink_round k times
theorem shrink_chain0 : ∀ k, ∀ a D,
    ⟨a + 1, 2 * k, (0 : ℕ), D, (0 : ℕ)⟩ [fm]⊢* ⟨a + k + 1, (0 : ℕ), (0 : ℕ), D, (0 : ℕ)⟩ := by
  intro k; induction' k with k ih <;> intro a D
  · exists 0
  · rw [show 2 * (k + 1) = 2 * k + 2 from by ring,
        show a + (k + 1) + 1 = (a + 1) + k + 1 from by ring]
    apply stepStar_trans (shrink_round a (2 * k) D)
    exact ih (a + 1) D

-- Shrink chain with b=1: iterate shrink_round k times, leaving remainder 1
theorem shrink_chain1 : ∀ k, ∀ a D,
    ⟨a + 1, 2 * k + 1, (0 : ℕ), D, (0 : ℕ)⟩ [fm]⊢* ⟨a + k + 1, (1 : ℕ), (0 : ℕ), D, (0 : ℕ)⟩ := by
  intro k; induction' k with k ih <;> intro a D
  · exists 0
  · rw [show 2 * (k + 1) + 1 = (2 * k + 1) + 2 from by ring,
        show a + (k + 1) + 1 = (a + 1) + k + 1 from by ring]
    apply stepStar_trans (shrink_round a (2 * k + 1) D)
    exact ih (a + 1) D

-- Odd drain: handle leftover b=1 after shrink chain
theorem odd_drain : ∀ a D,
    ⟨a + 1, (1 : ℕ), (0 : ℕ), D, (0 : ℕ)⟩ [fm]⊢* ⟨(0 : ℕ), (0 : ℕ), (0 : ℕ), D, 2 * a + 3⟩ := by
  intro a D
  step fm  -- R3: (a, 1, 0, D, 2)
  step fm  -- R2: (a+1, 0, 0, D, 1)
  step fm  -- R3: (a, 0, 0, D, 3)
  apply stepStar_trans (r3_chain a D 3)
  ring_nf; finish

-- Main transition: (0, 0, 0, d+1, d+3) →⁺ (0, 0, 0, d+2, d+4)
theorem main_trans (d : ℕ) :
    ⟨(0 : ℕ), (0 : ℕ), (0 : ℕ), d + 1, d + 3⟩ [fm]⊢⁺
    ⟨(0 : ℕ), (0 : ℕ), (0 : ℕ), d + 2, d + 4⟩ := by
  -- Phase 1: R4 × (d+1)
  rw [show d + 1 = 0 + (d + 1) from by ring]
  apply stepStar_stepPlus_stepPlus (d_to_c (d + 1) 0 0 (d + 3))
  rw [show 0 + (d + 1) = d + 1 from by ring]
  -- State: (0, 0, d+1, 0, d+3)
  -- Phase 2: R5
  apply step_stepStar_stepPlus
    (by simp [fm] : (⟨0, 0, d + 1, 0, d + 3⟩ : Q) [fm]⊢
      ⟨1, 0, d + 1, 1, d + 2⟩)
  -- State: (1, 0, d+1, 1, d+2)
  -- Phase 3: R1+R2 × (d+1)
  rw [show d + 2 = 1 + (d + 1) from by ring]
  apply stepStar_trans (r1r2_chain (d + 1) 0 1 1)
  -- State: (1, 0+(d+1), 0, 1+(d+1), 1)
  rw [show (0 : ℕ) + (d + 1) = d + 1 from by ring,
      show (1 : ℕ) + (d + 1) = d + 2 from by ring]
  -- State: (1, d+1, 0, d+2, 1)
  -- Phase 4: R2 × 1: consume 1 from b and e
  show ⟨1, d + 0 + 1, (0 : ℕ), d + 2, 0 + 1⟩ [fm]⊢* ⟨(0 : ℕ), (0 : ℕ), (0 : ℕ), d + 2, d + 4⟩
  apply stepStar_trans (r2_chain 1 1 d (d + 2) 0)
  -- State: (2, d, 0, d+2, 0) = (1+1, d, 0, d+2, 0)
  -- Phase 5: Parity split on d, then shrink + R3 drain
  rcases Nat.even_or_odd d with ⟨m, hm⟩ | ⟨m, hm⟩
  · -- d even: d = 2m
    rw [show m + m = 2 * m from by ring] at hm; subst hm
    -- Goal: (1+1, 2*m, 0, 2*m+2, 0) →* (0, 0, 0, 2*m+2, 2*m+4)
    apply stepStar_trans (shrink_chain0 m 1 (2 * m + 2))
    rw [show 1 + m + 1 = m + 2 from by ring]
    apply stepStar_trans (r3_chain (m + 2) (2 * m + 2) 0)
    ring_nf; finish
  · -- d odd: d = 2m+1
    subst hm
    -- Goal: (1+1, 2*m+1, 0, 2*m+1+2, 0) →* (0, 0, 0, 2*m+1+2, 2*m+1+4)
    rw [show 2 * m + 1 + 2 = 2 * m + 3 from by ring,
        show 2 * m + 1 + 4 = 2 * m + 5 from by ring]
    apply stepStar_trans (shrink_chain1 m 1 (2 * m + 3))
    rw [show 1 + m + 1 = (m + 1) + 1 from by ring]
    apply stepStar_trans (odd_drain (m + 1) (2 * m + 3))
    ring_nf; finish

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨0, 0, 0, 1, 3⟩) (by execute fm 3)
  apply progress_nonhalt_simple (fm := fm) (A := ℕ)
    (fun d ↦ ⟨0, 0, 0, d + 1, d + 3⟩) 0
  intro d
  refine ⟨d + 1, ?_⟩
  show ⟨(0 : ℕ), (0 : ℕ), (0 : ℕ), d + 1, d + 3⟩ [fm]⊢⁺
       ⟨(0 : ℕ), (0 : ℕ), (0 : ℕ), (d + 1) + 1, (d + 1) + 3⟩
  rw [show (d + 1) + 1 = d + 2 from by ring,
      show (d + 1) + 3 = d + 4 from by ring]
  exact main_trans d

end Sz22_2003_unofficial_1326
