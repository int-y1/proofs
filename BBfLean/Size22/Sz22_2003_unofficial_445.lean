import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #445: [28/15, 1/154, 21/2, 11/3, 50/11]

Vector representation:
```
 2 -1 -1  1  0
-1  0  0 -1 -1
-1  1  0  1  0
 0 -1  0  0  1
 1  0  2  0 -1
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_445

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a, b+1, c+1, d, e⟩ => some ⟨a+2, b, c, d+1, e⟩
  | ⟨a+1, b, c, d+1, e+1⟩ => some ⟨a, b, c, d, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b+1, c, d+1, e⟩
  | ⟨a, b+1, c, d, e⟩ => some ⟨a, b, c, d, e+1⟩
  | ⟨a, b, c, d, e+1⟩ => some ⟨a+1, b, c+2, d, e⟩
  | _ => none

-- R3 chain: (a+k, b, 0, d, 0) ->* (a, b+k, 0, d+k, 0)
theorem r3_chain : ∀ k a b d, ⟨a+k, b, 0, d, 0⟩ [fm]⊢* ⟨a, b+k, 0, d+k, 0⟩ := by
  intro k; induction' k with k h <;> intro a b d
  · exists 0
  rw [show a + (k + 1) = (a + k) + 1 from by ring]
  step fm
  apply stepStar_trans (h a (b + 1) (d + 1))
  ring_nf; finish

-- R4 chain: (0, b+k, 0, d, e) ->* (0, b, 0, d, e+k)
theorem r4_chain : ∀ k b d e, ⟨0, b+k, 0, d, e⟩ [fm]⊢* ⟨0, b, 0, d, e+k⟩ := by
  intro k; induction' k with k h <;> intro b d e
  · exists 0
  rw [show b + (k + 1) = (b + k) + 1 from by ring]
  step fm
  apply stepStar_trans (h b d (e + 1))
  ring_nf; finish

-- R5/R2 pairs: (0, 0, c, D+k, 2*k+1) ->* (1, 0, c+2*k+2, D, 0)
theorem r5r2_pairs : ∀ k c D, ⟨0, 0, c, D+k, 2*k+1⟩ [fm]⊢* ⟨1, 0, c+2*k+2, D, 0⟩ := by
  intro k; induction' k with k h <;> intro c D
  · -- k=0: (0, 0, c, D, 1) -> R5 -> (1, 0, c+2, D, 0)
    step fm; ring_nf; finish
  rw [show D + (k + 1) = (D + k) + 1 from by ring,
      show 2 * (k + 1) + 1 = (2 * k + 1) + 1 + 1 from by ring]
  step fm  -- R5: (1, 0, c+2, (D+k)+1, (2*k+1)+1)
  rw [show (2 * k + 1) + 1 = (2 * k) + 1 + 1 from by ring]
  step fm  -- R2: (0, 0, c+2, D+k, 2*k+1)
  apply stepStar_trans (h (c + 2) D)
  ring_nf; finish

-- R3/R1 alternation: (a+1, 0, C+k, D, 0) ->* (a+1+k, 0, C, D+2*k, 0)
theorem r3r1_chain : ∀ k a C D, ⟨a+1, 0, C+k, D, 0⟩ [fm]⊢* ⟨a+1+k, 0, C, D+2*k, 0⟩ := by
  intro k; induction' k with k h <;> intro a C D
  · exists 0
  rw [show C + (k + 1) = (C + k) + 1 from by ring]
  step fm  -- R3: (a, 1, (C+k)+1, D+1, 0)
  rw [show (C + k) + 1 = (C + k) + 1 from rfl]
  step fm  -- R1: (a+2, 0, C+k, D+2, 0)
  apply stepStar_trans (h (a + 1) C (D + 2))
  ring_nf; finish

-- Main transition: (2*n+3, 0, 0, d, 0) ->+ (2*n+5, 0, 0, d+5*n+10, 0)
theorem main_trans (n d : ℕ) : ⟨2*n+3, 0, 0, d, 0⟩ [fm]⊢⁺ ⟨2*n+5, 0, 0, d+5*n+10, 0⟩ := by
  apply stepStar_stepPlus_stepPlus (c₂ := ⟨0, 0, 0, d+2*n+3, 2*n+3⟩)
  · -- Phase 1: R3 chain + Phase 2: R4 chain
    apply stepStar_trans (c₂ := ⟨0, 2*n+3, 0, d+2*n+3, 0⟩)
    · have h := r3_chain (2*n+3) 0 0 d
      simp only [Nat.zero_add] at h; exact h
    have h := r4_chain (2*n+3) 0 (d+2*n+3) 0
    simp only [Nat.zero_add] at h; exact h
  -- Phase 3: R5/R2 pairs
  apply step_stepStar_stepPlus
  · show fm ⟨0, 0, 0, d + 2 * n + 3, 2 * n + 3⟩ = some ⟨1, 0, 2, d + 2 * n + 3, 2 * n + 2⟩
    rw [show 2 * n + 3 = (2 * n + 2) + 1 from by ring]; rfl
  rw [show 2 * n + 2 = (2 * n + 1) + 1 from by ring,
      show d + 2 * n + 3 = (d + 2 * n + 2) + 1 from by ring]
  step fm  -- R2: (0, 0, 2, d+2n+2, 2n+1)
  apply stepStar_trans (c₂ := ⟨1, 0, 2*n+4, d+n+2, 0⟩)
  · have h := r5r2_pairs n 2 (d+n+2)
    rw [show d + n + 2 + n = d + 2 * n + 2 from by ring,
        show 2 + 2 * n + 2 = 2 * n + 4 from by ring] at h
    exact h
  -- Phase 4: R3/R1 chain
  have h := r3r1_chain (2*n+4) 0 0 (d+n+2)
  simp only [Nat.zero_add,
             (by ring : 0 + 1 + (2 * n + 4) = 2 * n + 5),
             (by ring : d + n + 2 + 2 * (2 * n + 4) = d + 5 * n + 10)] at h
  exact h

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨3, 0, 0, 5, 0⟩) (by execute fm 7)
  apply progress_nonhalt_simple (fm := fm) (A := ℕ × ℕ)
    (fun ⟨n, d⟩ ↦ ⟨2*n+3, 0, 0, d, 0⟩) ⟨0, 5⟩
  intro ⟨n, d⟩
  exact ⟨⟨n+1, d+5*n+10⟩, main_trans n d⟩

end Sz22_2003_unofficial_445
