import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz21_140_unofficial #26: [35/6, 11/2, 4/55, 3/7, 12/11]

Vector representation:
```
-1 -1  1  1  0
-1  0  0  0  1
 2  0 -1  0 -1
 0  1  0 -1  0
 2  1  0  0 -1
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz21_140_unofficial_26

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a+1, b+1, c, d, e⟩ => some ⟨a, b, c+1, d+1, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b, c, d, e+1⟩
  | ⟨a, b, c+1, d, e+1⟩ => some ⟨a+2, b, c, d, e⟩
  | ⟨a, b, c, d+1, e⟩ => some ⟨a, b+1, c, d, e⟩
  | ⟨a, b, c, d, e+1⟩ => some ⟨a+2, b+1, c, d, e⟩
  | _ => none

-- R2 repeated: a → e (when b=0)
theorem a_to_e : ⟨a+k, 0, c, d, e⟩ [fm]⊢* ⟨a, 0, c, d, e+k⟩ := by
  have many_step : ∀ k a e, ⟨a+k, 0, c, d, e⟩ [fm]⊢* ⟨a, 0, c, d, e+k⟩ := by
    intro k; induction' k with k h <;> intro a e
    · exists 0
    rw [← Nat.add_assoc]
    step fm
    apply stepStar_trans (h _ _)
    ring_nf; finish
  exact many_step k a e

-- R4 repeated: d → b (when a=0, c=0)
theorem d_to_b : ⟨0, b, 0, d+k, e⟩ [fm]⊢* ⟨0, b+k, 0, d, e⟩ := by
  have many_step : ∀ k b d, ⟨0, b, 0, d+k, e⟩ [fm]⊢* ⟨0, b+k, 0, d, e⟩ := by
    intro k; induction' k with k h <;> intro b d
    · exists 0
    rw [← Nat.add_assoc]
    step fm
    apply stepStar_trans (h _ _)
    ring_nf; finish
  exact many_step k b d

-- R1,R1,R3 chain: 3-step rounds
theorem r1r1r3_rounds : ∀ k, ∀ C D, ⟨2, B+2*k, C, D, E+k⟩ [fm]⊢* ⟨2, B, C+k, D+2*k, E⟩ := by
  intro k; induction' k with k h <;> intro C D
  · exists 0
  rw [show B + 2 * (k + 1) = (B + 2 * k) + 1 + 1 from by ring,
      show E + (k + 1) = (E + k) + 1 from by ring]
  step fm
  rw [show E + k + 1 = (E + k) + 1 from by ring]
  step fm
  rw [show C + 2 = (C + 1) + 1 from by ring]
  step fm
  apply stepStar_trans (h (C + 1) (D + 2))
  ring_nf; finish

-- R3,R2,R2 tail: clears c and produces target
-- (0, 0, c+1, d, e+1) →* (2, 0, 0, d, e+c)
theorem full_tail : ∀ c, ∀ e, ⟨0, 0, c+1, d, e+1⟩ [fm]⊢* ⟨2, 0, 0, d, e+c⟩ := by
  intro c; induction' c with c h <;> intro e
  · -- c=0: (0, 0, 1, d, e+1) → R3 → (2, 0, 0, d, e)
    step fm; finish
  · -- c+1: (0, 0, c+2, d, e+1) → R3,R2,R2 → (0, 0, c+1, d, e+2) → IH
    rw [show (c + 1) + 1 = (c + 1) + 1 from rfl]
    step fm
    step fm
    step fm
    apply stepStar_trans (h (e + 1))
    ring_nf; finish

-- Phase 4 for even n = 2m
theorem phase4_even (m : ℕ) : ⟨2, 2*m+2, 0, 0, 2*m+1⟩ [fm]⊢* ⟨2, 0, 0, 2*m+2, 2*m+1⟩ := by
  -- R1,R1,R3 rounds: m rounds → (2, 2, m, 2m, m+1)
  apply stepStar_trans (c₂ := ⟨2, 2, m, 2*m, m+1⟩)
  · have h := @r1r1r3_rounds 2 (m+1) m 0 0
    simp only [Nat.zero_add] at h
    rw [show 2 * m + 2 = 2 + 2 * m from by ring,
        show 2 * m + 1 = m + 1 + m from by ring]
    exact h
  -- R1,R1: (2, 2, m, 2m, m+1) → (0, 0, m+2, 2m+2, m+1)
  apply stepStar_trans (c₂ := ⟨0, 0, m+2, 2*m+2, m+1⟩)
  · rw [show (2 : ℕ) = 1 + 1 from rfl]
    step fm
    step fm
    ring_nf; finish
  -- full_tail: (0, 0, (m+1)+1, 2m+2, m+1) →* (2, 0, 0, 2m+2, m+(m+1))
  rw [show m + 2 = (m + 1) + 1 from by ring,
      show (m + 1 : ℕ) = m + 1 from rfl]
  refine stepStar_trans (@full_tail (2*m+2) (m+1) m) ?_
  ring_nf; finish

-- Phase 4 for odd n = 2m+1
theorem phase4_odd (m : ℕ) : ⟨2, 2*m+3, 0, 0, 2*m+2⟩ [fm]⊢* ⟨2, 0, 0, 2*m+3, 2*m+2⟩ := by
  -- R1,R1,R3 rounds: m rounds → (2, 3, m, 2m, m+2)
  apply stepStar_trans (c₂ := ⟨2, 3, m, 2*m, m+2⟩)
  · have h := @r1r1r3_rounds 3 (m+2) m 0 0
    simp only [Nat.zero_add] at h
    rw [show 2 * m + 3 = 3 + 2 * m from by ring,
        show 2 * m + 2 = m + 2 + m from by ring]
    exact h
  -- Odd tail: 5 steps → (0, 0, m+2, 2m+3, m+2)
  apply stepStar_trans (c₂ := ⟨0, 0, m+2, 2*m+3, m+2⟩)
  · rw [show (3 : ℕ) = 2 + 1 from rfl]
    step fm  -- R1: (1, 2, m+1, 2m+1, m+2)
    step fm  -- R1: (0, 1, m+2, 2m+2, m+2)
    -- Now: (0, 1, m+1+1, 2*m+1+1, m+2). R3 fires (c+1, e+1 pattern)
    step fm  -- R3: (2, 1, m+1, 2m+2, m+1)
    -- Now: (2, 1, ...). R1 fires (a+1, b+1)
    step fm  -- R1: (1, 0, m+2, 2m+3, m+1)
    -- R2: (0, 0, m+2, 2m+3, m+2)
    step fm
    ring_nf; finish
  -- full_tail
  rw [show m + 2 = (m + 1) + 1 from by ring]
  refine stepStar_trans (@full_tail (2*m+3) (m+1) (m+1)) ?_
  ring_nf; finish

-- Main transition: (2, 0, 0, n+1, n) →⁺ (2, 0, 0, n+2, n+1)
theorem main_trans : ⟨2, 0, 0, n+1, n⟩ [fm]⊢⁺ ⟨2, 0, 0, n+2, n+1⟩ := by
  -- Phase 1: R2 x 2: → (0, 0, 0, n+1, n+2)
  apply stepStar_stepPlus_stepPlus (c₂ := ⟨0, 0, 0, n+1, n+2⟩)
  · have h := @a_to_e 0 2 0 (n+1) n
    simp only [Nat.zero_add] at h; exact h
  -- Phase 2: R4 x (n+1): → (0, n+1, 0, 0, n+2)
  apply stepStar_stepPlus_stepPlus (c₂ := ⟨0, n+1, 0, 0, n+2⟩)
  · have h : (0, 0, 0, 0 + (n + 1), n + 2) [fm]⊢* (0, 0 + (n + 1), 0, 0, n + 2) := d_to_b
    simp only [Nat.zero_add] at h; exact h
  -- Phase 3: R5: → (2, n+2, 0, 0, n+1)
  apply step_stepStar_stepPlus (c₂ := ⟨2, n+2, 0, 0, n+1⟩)
  · show fm ⟨0, n+1, 0, 0, (n+1)+1⟩ = some ⟨2, (n+1)+1, 0, 0, n+1⟩
    simp [fm]
  -- Phase 4: parity split
  rcases Nat.even_or_odd n with ⟨K, hK⟩ | ⟨K, hK⟩
  · rw [show K + K = 2 * K from by ring] at hK; subst hK
    refine stepStar_trans (phase4_even K) ?_
    ring_nf; finish
  · subst hK
    rw [show 2 * K + 1 + 2 = 2 * K + 3 from by ring,
        show 2 * K + 1 + 1 = 2 * K + 2 from by ring]
    refine stepStar_trans (phase4_odd K) ?_
    ring_nf; finish

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨2, 0, 0, 1, 0⟩) (by execute fm 5)
  apply progress_nonhalt_simple (fm := fm) (A := ℕ) (fun n ↦ ⟨2, 0, 0, n+1, n⟩) 0
  intro n; exact ⟨n+1, main_trans⟩
