import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #449: [28/15, 1/3, 3/22, 25/2, 11/7, 3/5]

Vector representation:
```
 2 -1 -1  1  0
 0 -1  0  0  0
-1  1  0  0 -1
-1  0  2  0  0
 0  0  0 -1  1
 0  1 -1  0  0
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_449

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a, b+1, c+1, d, e⟩ => some ⟨a+2, b, c, d+1, e⟩
  | ⟨a, b+1, c, d, e⟩ => some ⟨a, b, c, d, e⟩
  | ⟨a+1, b, c, d, e+1⟩ => some ⟨a, b+1, c, d, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b, c+2, d, e⟩
  | ⟨a, b, c, d+1, e⟩ => some ⟨a, b, c, d, e+1⟩
  | ⟨a, b, c+1, d, e⟩ => some ⟨a, b+1, c, d, e⟩
  | _ => none

-- R4 repeated: (a+k, 0, c, d, 0) →* (a, 0, c+2*k, d, 0)
theorem a_to_c : ∀ k a c d, ⟨a+k, 0, c, d, 0⟩ [fm]⊢* ⟨a, 0, c+2*k, d, 0⟩ := by
  intro k; induction' k with k h <;> intro a c d
  · exists 0
  rw [← Nat.add_assoc]
  step fm
  apply stepStar_trans (h _ _ _)
  ring_nf; finish

-- R5 repeated: (0, 0, c, d+k, e) →* (0, 0, c, d, e+k)
theorem d_to_e : ∀ k c d e, ⟨0, 0, c, d+k, e⟩ [fm]⊢* ⟨0, 0, c, d, e+k⟩ := by
  intro k; induction' k with k h <;> intro c d e
  · exists 0
  rw [← Nat.add_assoc]
  step fm
  apply stepStar_trans (h _ _ _)
  ring_nf; finish

-- R1,R3 chain: (a, 1, c+k, d, e+k) →* (a+k, 1, c, d+k, e)
theorem r1r3_chain : ∀ k a c d e, ⟨a, 1, c+k, d, e+k⟩ [fm]⊢* ⟨a+k, 1, c, d+k, e⟩ := by
  intro k; induction' k with k h <;> intro a c d e
  · exists 0
  rw [show c + (k + 1) = (c + k) + 1 from by ring,
      show e + (k + 1) = (e + k) + 1 from by ring]
  step fm
  step fm
  apply stepStar_trans (h _ _ _ _)
  ring_nf; finish

-- Full transition for n≥1: from after R4 phase
-- (0, 0, c + 2*n + 4, n+1, 0) ⊢⁺ (n+3, 0, c+n+1, n+2, 0)
theorem r5_r6_r1r3_r1 : ∀ n c,
    ⟨0, 0, c + 2*n + 4, n+1, 0⟩ [fm]⊢⁺ ⟨n+3, 0, c+n+1, n+2, 0⟩ := by
  intro n; induction' n with n _ih <;> intro c
  · -- n=0: (0, 0, c+4, 1, 0) ⊢⁺ (3, 0, c+1, 2, 0)
    step fm  -- R5: (0, 0, c+4, 0, 1)
    step fm  -- R6: (0, 1, c+3, 0, 1)
    step fm  -- R1: (2, 0, c+2, 1, 1)
    step fm  -- R3: (1, 1, c+2, 1, 0)
    step fm  -- R1: (3, 0, c+1, 2, 0)
    finish
  · -- n+1: (0, 0, c+2*(n+1)+4, n+2, 0) ⊢⁺ (n+4, 0, c+n+2, n+3, 0)
    -- R5: (0, 0, c+2*n+6, n+2, 0) → (0, 0, c+2*n+6, n+1, 1)
    rw [show c + 2 * (n + 1) + 4 = c + 2 * n + 6 from by ring,
        show (n : ℕ) + 1 + 1 = (n + 1) + 1 from rfl]
    step fm
    -- (0, 0, c+2*n+6, n+1, 1)
    -- R5 × n: drain d
    apply stepStar_trans
    · show ⟨0, 0, c+2*n+6, n+1, 1⟩ [fm]⊢* ⟨0, 0, c+2*n+6, 0, n+2⟩
      rw [show (n : ℕ) + 1 = n + 1 from rfl]
      have h := d_to_e (n+1) (c+2*n+6) 0 1
      simp only [Nat.zero_add] at h
      rw [show 1 + (n + 1) = n + 2 from by ring] at h
      exact h
    -- (0, 0, c+2*n+6, 0, n+2)
    -- R6: (0, 0, c+2*n+6, 0, n+2) → (0, 1, c+2*n+5, 0, n+2)
    rw [show c + 2 * n + 6 = (c + 2 * n + 5) + 1 from by ring]
    step fm
    -- R1,R3 chain × (n+2): (0, 1, c+2*n+5, 0, n+2) →* (n+2, 1, c+n+3, n+2, 0)
    apply stepStar_trans
    · have h := r1r3_chain (n+2) 0 (c+n+3) 0 0
      simp only [Nat.zero_add] at h
      rw [show c + n + 3 + (n + 2) = c + 2 * n + 5 from by ring] at h
      exact h
    -- Final R1: (n+2, 1, c+n+3, n+2, 0) → (n+4, 0, c+n+2, n+3, 0)
    rw [show c + n + 3 = (c + n + 2) + 1 from by ring]
    step fm
    ring_nf; finish

-- Main transition: (n+1, 0, c, n, 0) ⊢⁺ (n+2, 0, c+n, n+1, 0)
theorem main_trans (n c : ℕ) : ⟨n+1, 0, c, n, 0⟩ [fm]⊢⁺ ⟨n+2, 0, c+n, n+1, 0⟩ := by
  -- R4 × (n+1): (n+1, 0, c, n, 0) →* (0, 0, c+2*(n+1), n, 0)
  rcases n with _ | n
  · -- n=0: (1, 0, c, 0, 0) ⊢⁺ (2, 0, c, 1, 0)
    step fm  -- R4: (0, 0, c+2, 0, 0)
    step fm  -- R6: (0, 1, c+1, 0, 0)
    step fm  -- R1: (2, 0, c, 1, 0)
    finish
  · -- n ≥ 1: (n+2, 0, c, n+1, 0) ⊢⁺ (n+3, 0, c+n+1, n+2, 0)
    -- R4 phase: (n+2, 0, c, n+1, 0) →* (0, 0, c+2*(n+2), n+1, 0)
    apply stepStar_stepPlus_stepPlus
    · rw [show (n : ℕ) + 1 + 1 = 0 + (n + 2) from by ring]
      exact a_to_c (n+2) 0 c (n+1)
    -- Now: (0, 0, c+2*(n+2), n+1, 0) ⊢⁺ (n+3, 0, c+n+1, n+2, 0)
    rw [show c + 2 * (n + 2) = c + 2 * n + 4 from by ring]
    exact r5_r6_r1r3_r1 n c

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨2, 0, 0, 1, 0⟩) (by execute fm 3)
  apply progress_nonhalt_simple (fm := fm) (A := ℕ × ℕ)
    (fun ⟨n, c⟩ ↦ ⟨n+1, 0, c, n, 0⟩) ⟨1, 0⟩
  intro ⟨n, c⟩
  exact ⟨⟨n+1, c+n⟩, main_trans n c⟩

end Sz22_2003_unofficial_449
