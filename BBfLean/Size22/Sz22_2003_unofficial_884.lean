import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #884: [4/15, 11319/2, 1/3, 5/539, 3/7]

Vector representation:
```
 2 -1 -1  0  0
-1  1  0  3  1
 0 -1  0  0  0
 0  0  1 -2 -1
 0  1  0 -1  0
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_884

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a, b+1, c+1, d, e⟩ => some ⟨a+2, b, c, d, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b+1, c, d+3, e+1⟩
  | ⟨a, b+1, c, d, e⟩ => some ⟨a, b, c, d, e⟩
  | ⟨a, b, c, d+2, e+1⟩ => some ⟨a, b, c+1, d, e⟩
  | ⟨a, b, c, d+1, e⟩ => some ⟨a, b+1, c, d, e⟩
  | _ => none

-- R2 chain: c=0 prevents R1. R2 fires when a≥1.
-- (a+k, b, 0, d, e) →* (a, b+k, 0, d+3k, e+k)
theorem r2_chain : ∀ k, ∀ b d e, ⟨a + k, b, 0, d, e⟩ [fm]⊢* ⟨a, b + k, 0, d + 3 * k, e + k⟩ := by
  intro k; induction' k with k ih <;> intro b d e
  · exists 0
  · rw [show a + (k + 1) = (a + k) + 1 from by ring]
    step fm
    apply stepStar_trans (ih (b + 1) (d + 3) (e + 1))
    ring_nf; finish

-- R3 drain: a=0, c=0. Only R3 fires.
-- (0, b+k, 0, d, e) →* (0, b, 0, d, e)
theorem r3_drain : ∀ k, ∀ d e, ⟨0, b + k, 0, d, e⟩ [fm]⊢* ⟨0, b, 0, d, e⟩ := by
  intro k; induction' k with k ih <;> intro d e
  · exists 0
  · rw [show b + (k + 1) = (b + k) + 1 from by ring]
    step fm
    apply stepStar_trans (ih d e)
    ring_nf; finish

-- R4 chain: a=0, b=0. R4 fires.
-- (0, 0, c, d+2k, e+k) →* (0, 0, c+k, d, e)
theorem r4_chain : ∀ k, ∀ c d e, ⟨0, 0, c, d + 2 * k, e + k⟩ [fm]⊢* ⟨0, 0, c + k, d, e⟩ := by
  intro k; induction' k with k ih <;> intro c d e
  · exists 0
  · rw [show d + 2 * (k + 1) = (d + 2 * k) + 2 from by ring,
        show e + (k + 1) = (e + k) + 1 from by ring]
    step fm
    apply stepStar_trans (ih (c + 1) d e)
    ring_nf; finish

-- R2+R1 interleaving chain.
-- (A+1, 0, k+1, D, E) →* (A+k+2, 0, 0, D+3(k+1), E+k+1)
theorem r2r1_chain : ∀ k, ∀ A D E, ⟨A + 1, 0, k + 1, D, E⟩ [fm]⊢* ⟨A + k + 2, 0, 0, D + 3 * (k + 1), E + k + 1⟩ := by
  intro k; induction' k with k ih <;> intro A D E
  · step fm; step fm; ring_nf; finish
  · rw [show k + 1 + 1 = (k + 1) + 1 from by ring]
    step fm
    step fm
    rw [show A + 2 = (A + 1) + 1 from by ring]
    apply stepStar_trans (ih (A + 1) (D + 3) (E + 1))
    ring_nf; finish

-- Full interleave: R5 + R1 + r2r1_chain.
-- (0, 0, C+1, D+1, 0) →⁺ (C+2, 0, 0, D+3C, C)
theorem interleave : ∀ C D, ⟨0, 0, C + 1, D + 1, 0⟩ [fm]⊢⁺ ⟨C + 2, 0, 0, D + 3 * C, C⟩ := by
  intro C; induction' C with C _ <;> intro D
  · step fm; step fm; ring_nf; finish
  · step fm
    step fm
    rw [show (2 : ℕ) = 1 + 1 from by ring]
    apply stepStar_trans (r2r1_chain C 1 D 0)
    ring_nf; finish

-- Specialized R2 chain from 0: (k, 0, 0, d, e) →* (0, k, 0, d+3k, e+k)
theorem r2_chain_zero : ∀ k d e, ⟨k, 0, 0, d, e⟩ [fm]⊢* ⟨0, k, 0, d + 3 * k, e + k⟩ := by
  intro k d e
  have := r2_chain (a := 0) k 0 d e
  simp only [Nat.zero_add] at this
  exact this

-- Specialized R3 drain from 0: (0, k, 0, d, e) →* (0, 0, 0, d, e)
theorem r3_drain_zero : ∀ k d e, ⟨0, k, 0, d, e⟩ [fm]⊢* ⟨0, 0, 0, d, e⟩ := by
  intro k d e
  have := r3_drain (b := 0) k d e
  simp only [Nat.zero_add] at this
  exact this

-- Specialized R4 chain from 0: (0, 0, 0, d+2k, k) →* (0, 0, k, d, 0)
theorem r4_chain_zero : ∀ k d, ⟨0, 0, 0, d + 2 * k, k⟩ [fm]⊢* ⟨0, 0, k, d, 0⟩ := by
  intro k d
  have := r4_chain k 0 d 0
  simp only [Nat.zero_add] at this
  exact this

-- Main transition.
theorem main_trans (a d : ℕ) (h : d ≥ a) :
    ⟨a + 2, 0, 0, d, a⟩ [fm]⊢⁺ ⟨2 * a + 3, 0, 0, d + 5 * a + 4, 2 * a + 1⟩ := by
  obtain ⟨D, rfl⟩ : ∃ D, d = D + a := ⟨d - a, by omega⟩
  -- Phase 1: R2 chain
  apply stepStar_stepPlus_stepPlus (r2_chain_zero (a + 2) (D + a) a)
  -- Phase 2: R3 drain
  apply stepStar_stepPlus_stepPlus (r3_drain_zero (a + 2) (D + a + 3 * (a + 2)) (a + (a + 2)))
  -- Phase 3: R4 chain
  apply stepStar_stepPlus_stepPlus
  · rw [show D + a + 3 * (a + 2) = (D + 2) + 2 * (2 * a + 2) from by ring,
        show a + (a + 2) = 2 * a + 2 from by ring]
    exact r4_chain_zero (2 * a + 2) (D + 2)
  -- Phase 4: Interleave (⊢⁺)
  rw [show 2 * a + 2 = (2 * a + 1) + 1 from by ring,
      show (D + 2 : ℕ) = (D + 1) + 1 from by ring]
  apply stepPlus_stepStar_stepPlus (interleave (2 * a + 1) (D + 1))
  ring_nf; finish

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨2, 0, 0, 0, 0⟩)
  · execute fm 5
  apply progress_nonhalt (fm := fm)
    (P := fun q ↦ ∃ a d, q = ⟨a + 2, 0, 0, d, a⟩ ∧ d ≥ a)
  · intro c ⟨a, d, hq, hge⟩; subst hq
    exact ⟨⟨2 * a + 3, 0, 0, d + 5 * a + 4, 2 * a + 1⟩,
      ⟨2 * a + 1, d + 5 * a + 4, by ring_nf, by omega⟩,
      main_trans a d hge⟩
  · exact ⟨0, 0, by simp, by omega⟩
