import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #1905: [9/35, 65/33, 14/3, 11/13, 99/2]

Vector representation:
```
 0  2 -1 -1  0  0
 0 -1  1  0 -1  1
 1 -1  0  1  0  0
 0  0  0  0  1 -1
-1  2  0  0  1  0
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_1905

def Q := ℕ × ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a, b, c+1, d+1, e, f⟩ => some ⟨a, b+2, c, d, e, f⟩
  | ⟨a, b+1, c, d, e+1, f⟩ => some ⟨a, b, c+1, d, e, f+1⟩
  | ⟨a, b+1, c, d, e, f⟩ => some ⟨a+1, b, c, d+1, e, f⟩
  | ⟨a, b, c, d, e, f+1⟩ => some ⟨a, b, c, d, e+1, f⟩
  | ⟨a+1, b, c, d, e, f⟩ => some ⟨a, b+2, c, d, e+1, f⟩
  | _ => none

-- R2/R1 interleaving: each round R2 then R1.
-- Net per round: b += 1, d -= 1, e -= 1, f += 1.
theorem r2r1_chain : ∀ k, ∀ a b d f,
    ⟨a, b + 2, 0, d + k, k, f⟩ [fm]⊢* ⟨a, b + k + 2, 0, d, 0, f + k⟩ := by
  intro k; induction' k with k ih <;> intro a b d f
  · exists 0
  · rw [show d + (k + 1) = (d + k) + 1 from by ring]
    step fm; step fm
    rw [show b + 2 + 1 = (b + 1) + 2 from by ring]
    apply stepStar_trans (ih a (b + 1) d (f + 1))
    ring_nf; finish

-- R3 chain: drain b into a and d.
theorem r3_chain : ∀ k, ∀ a d f,
    ⟨a, k, 0, d, 0, f⟩ [fm]⊢* ⟨a + k, 0, 0, d + k, 0, f⟩ := by
  intro k; induction' k with k ih <;> intro a d f
  · exists 0
  · step fm
    apply stepStar_trans (ih (a + 1) (d + 1) f)
    ring_nf; finish

-- R4 chain: move f to e.
theorem r4_chain : ∀ k, ∀ a d e,
    ⟨a, 0, 0, d, e, k⟩ [fm]⊢* ⟨a, 0, 0, d, e + k, 0⟩ := by
  intro k; induction' k with k ih <;> intro a d e
  · exists 0
  · step fm
    apply stepStar_trans (ih a d (e + 1))
    ring_nf; finish

-- Main transition: from canonical (a+3, 0, 0, 2*(n+1), n+1, 0) to next canonical.
theorem main_trans : ∀ n, ∀ a,
    ⟨a + 3, 0, 0, 2 * (n + 1), n + 1, 0⟩ [fm]⊢⁺
    ⟨a + n + 6, 0, 0, 2 * (n + 2), n + 2, 0⟩ := by
  intro n a
  -- Phase 1: R5
  rw [show a + 3 = (a + 2) + 1 from by ring]
  step fm
  -- After R5: (a+2, 2, 0, 2*(n+1), n+1+1, 0)
  rw [show 2 * (n + 1) = n + (n + 1 + 1) from by ring]
  -- Phase 2: R2/R1 chain with k = n+1+1
  apply stepStar_trans (r2r1_chain (n + 1 + 1) (a + 2) 0 n 0)
  -- After chain: (a+2, n+1+1+2, 0, n, 0, n+1+1)
  -- Phase 3: R3 chain
  apply stepStar_trans (r3_chain (0 + (n + 1 + 1) + 2) (a + 2) n (0 + (n + 1 + 1)))
  -- Phase 4: R4 chain
  apply stepStar_trans (r4_chain (0 + (n + 1 + 1)) (a + 2 + (0 + (n + 1 + 1) + 2)) (n + (0 + (n + 1 + 1) + 2)) 0)
  ring_nf; finish

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨3, 0, 0, 2, 1, 0⟩) (by execute fm 7)
  apply progress_nonhalt_simple (fm := fm) (A := ℕ × ℕ)
    (fun ⟨α, n⟩ ↦ ⟨α + 3, 0, 0, 2 * (n + 1), n + 1, 0⟩) ⟨0, 0⟩
  intro ⟨α, n⟩; exact ⟨⟨α + n + 3, n + 1⟩, main_trans n α⟩
