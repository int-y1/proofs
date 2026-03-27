import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #394: [20/3, 18/35, 1/20, 49/2, 3/7]

Vector representation:
```
 2 -1  1  0
 1  2 -1 -1
-2  0 -1  0
-1  0  0  2
 0  1  0 -1
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_394

def Q := ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a, b+1, c, d⟩ => some ⟨a+2, b, c+1, d⟩
  | ⟨a, b, c+1, d+1⟩ => some ⟨a+1, b+2, c, d⟩
  | ⟨a+2, b, c+1, d⟩ => some ⟨a, b, c, d⟩
  | ⟨a+1, b, c, d⟩ => some ⟨a, b, c, d+2⟩
  | ⟨a, b, c, d+1⟩ => some ⟨a, b+1, c, d⟩
  | _ => none

-- Build-up loop: R2, R1, R1 repeated k times
theorem buildup_loop : ⟨a, 0, c+1, k⟩ [fm]⊢* ⟨a+5*k, 0, c+k+1, 0⟩ := by
  have go : ∀ k c a, ⟨a, 0, c+1, k⟩ [fm]⊢* ⟨a+5*k, 0, c+k+1, 0⟩ := by
    intro k; induction' k with k ih <;> intro c a
    · exists 0
    · step fm; step fm; step fm
      apply stepStar_trans (ih _ _)
      ring_nf; finish
  exact go k c a

-- R3 repeated k times with d=0
theorem r3_chain : ⟨a+2*k, 0, k, 0⟩ [fm]⊢* ⟨a, 0, 0, 0⟩ := by
  have go : ∀ k a, ⟨a+2*k, 0, k, 0⟩ [fm]⊢* ⟨a, 0, 0, 0⟩ := by
    intro k; induction' k with k ih <;> intro a
    · exists 0
    · rw [Nat.mul_succ, ← Nat.add_assoc]
      step fm
      exact ih _
  exact go k a

-- R4 repeated k times
theorem r4_chain : ⟨k, 0, 0, d⟩ [fm]⊢* ⟨0, 0, 0, d+2*k⟩ := by
  have go : ∀ k d, ⟨k, 0, 0, d⟩ [fm]⊢* ⟨0, 0, 0, d+2*k⟩ := by
    intro k; induction' k with k ih <;> intro d
    · exists 0
    · step fm
      apply stepStar_trans (ih _)
      ring_nf; finish
  exact go k d

-- Combined buildup + teardown + convert
theorem cycle_from_state (n : ℕ) :
    ⟨2, 0, 1, 2*n+1⟩ [fm]⊢* ⟨0, 0, 0, 12*n+6⟩ := by
  -- Phase 1: buildup: (2, 0, 0+1, 2n+1) →* (2+5*(2n+1), 0, (2n+1)+1, 0)
  apply stepStar_trans (buildup_loop (a := 2) (c := 0) (k := 2*n+1))
  -- Goal: (2+5*(2*n+1), 0, 0+(2*n+1)+1, 0) ⊢* (0, 0, 0, 12*n+6)
  -- Need to rewrite first component for r3_chain
  have h2 : 2 + 5 * (2 * n + 1) = (6*n+3) + 2*(2*n+2) := by ring
  have h3 : 0 + (2 * n + 1) + 1 = 2*n+2 := by ring
  rw [h2, h3]
  -- Phase 2: r3_chain: ((6n+3)+2*(2n+2), 0, 2n+2, 0) →* (6n+3, 0, 0, 0)
  apply stepStar_trans (r3_chain (a := 6*n+3) (k := 2*n+2))
  -- Phase 3: r4_chain: (6n+3, 0, 0, 0) →* (0, 0, 0, 0+2*(6n+3))
  have h4 : (12 : ℕ) * n + 6 = 0 + 2*(6*n+3) := by ring
  rw [h4]
  exact r4_chain (k := 6*n+3) (d := 0)

-- Full cycle: (0, 0, 0, 2*(n+1)) ⊢⁺ (0, 0, 0, 12*n+6)
theorem full_cycle (n : ℕ) : ⟨0, 0, 0, 2*(n+1)⟩ [fm]⊢⁺ ⟨0, 0, 0, 12*n+6⟩ := by
  step fm; step fm
  exact cycle_from_state n

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨0, 0, 0, 2⟩)
  · execute fm 1
  apply progress_nonhalt (fm := fm)
    (P := fun q ↦ ∃ n, q = ⟨0, 0, 0, 2*(n+1)⟩)
  · intro c ⟨n, hq⟩; subst hq
    exact ⟨⟨0, 0, 0, 12*n+6⟩, ⟨6*n+2, by ring_nf⟩, full_cycle n⟩
  · exact ⟨0, by ring_nf⟩

end Sz22_2003_unofficial_394
