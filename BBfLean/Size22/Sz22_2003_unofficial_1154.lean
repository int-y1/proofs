import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #1154: [5/6, 44/35, 7/2, 3/11, 132/7]

Vector representation:
```
-1 -1  1  0  0
 2  0 -1 -1  1
-1  0  0  1  0
 0  1  0  0 -1
 2  1  0 -1  1
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_1154

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a+1, b+1, c, d, e⟩ => some ⟨a, b, c+1, d, e⟩
  | ⟨a, b, c+1, d+1, e⟩ => some ⟨a+2, b, c, d, e+1⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b, c, d+1, e⟩
  | ⟨a, b, c, d, e+1⟩ => some ⟨a, b+1, c, d, e⟩
  | ⟨a, b, c, d+1, e⟩ => some ⟨a+2, b+1, c, d, e+1⟩
  | _ => none

-- R3 chain: drain a into d when b=0, c=0
theorem a_to_d : ∀ k d, ⟨k, 0, 0, d, e⟩ [fm]⊢* ⟨0, 0, 0, k + d, e⟩ := by
  intro k; induction' k with k ih <;> intro d
  · ring_nf; finish
  · step fm
    apply stepStar_trans (ih (d + 1))
    ring_nf; finish

-- R4 chain: drain e into b when a=0, c=0
theorem e_to_b : ∀ k b, ⟨0, b, 0, d, k⟩ [fm]⊢* ⟨0, k + b, 0, d, 0⟩ := by
  intro k; induction' k with k ih <;> intro b
  · ring_nf; finish
  · step fm
    apply stepStar_trans (ih (b + 1))
    ring_nf; finish

-- R1,R1,R2 interleaved chain: each round does (2, B+2, c, D+1, E) →3→ (2, B, c+1, D, E+1)
theorem r1r1r2_chain : ∀ k, ∀ b c d e, ⟨2, 2 * k + b, c, k + d, e⟩ [fm]⊢* ⟨2, b, k + c, d, k + e⟩ := by
  intro k; induction' k with k ih <;> intro b c d e
  · ring_nf; finish
  · rw [show 2 * (k + 1) + b = 2 * k + b + 1 + 1 from by ring,
        show (k + 1) + d = (k + d) + 1 from by ring]
    step fm; step fm; step fm
    apply stepStar_trans (ih b (c + 1) d (e + 1))
    ring_nf; finish

-- Tail: (2, 1, n, 0, n+1) →* (2, 0, n, 0, n+2)
-- R1: (1, 0, n+1, 0, n+1) → R3: (0, 0, n+1, 1, n+1) → R2: (2, 0, n, 0, n+2)
theorem tail : ⟨2, 1, n, 0, n + 1⟩ [fm]⊢* ⟨2, 0, n, 0, n + 2⟩ := by
  step fm; step fm; step fm; finish

-- R3,R2 chain: each pair (a+1, 0, k+1, 0, e) → R3 → R2 → (a+2, 0, k, 0, e+1)
-- Net per round: a += 1, c -= 1, e += 1
theorem r3r2_chain : ∀ k a e, ⟨a + 1, 0, k + 1, 0, e⟩ [fm]⊢* ⟨a + k + 2, 0, 0, 0, e + k + 1⟩ := by
  intro k; induction' k with k ih <;> intro a e
  · step fm; step fm; finish
  · step fm; step fm
    apply stepStar_trans (ih (a + 1) (e + 1))
    ring_nf; finish

-- Combined drain: (n+2, 0, 0, 0, 2n+2) →* (0, 2n+2, 0, n+2, 0)
theorem drain (n : ℕ) : ⟨n + 2, 0, 0, 0, 2 * n + 2⟩ [fm]⊢* ⟨0, 2 * n + 2, 0, n + 2, 0⟩ := by
  apply stepStar_trans (a_to_d (n + 2) 0 (e := 2 * n + 2))
  exact e_to_b (2 * n + 2) 0 (d := n + 2)

-- Main transition: (n+2, 0, 0, 0, 2n+2) →⁺ (n+3, 0, 0, 0, 2n+4)
theorem main_trans (n : ℕ) : ⟨n + 2, 0, 0, 0, 2 * n + 2⟩ [fm]⊢⁺ ⟨n + 3, 0, 0, 0, 2 * n + 4⟩ := by
  apply stepStar_stepPlus_stepPlus (drain n)
  -- Goal: (0, 2n+2, 0, n+2, 0) →⁺ (n+3, 0, 0, 0, 2n+4)
  -- R5 fires
  rw [show n + 2 = (n + 1) + 1 from by ring]
  step fm
  -- R1,R1,R2 chain
  apply stepStar_trans (r1r1r2_chain (n + 1) 1 0 0 1)
  -- Goal: (2, 1, n+1, 0, n+2) →* (n+3, 0, 0, 0, 2n+4)
  -- Tail
  apply stepStar_trans (tail (n := n + 1))
  -- Goal: (2, 0, n+1, 0, n+3) →* (n+3, 0, 0, 0, 2n+4)
  -- R3,R2 chain
  rw [show (2 : ℕ) = 1 + 1 from by ring]
  apply stepStar_trans (r3r2_chain n 1 (n + 3))
  ring_nf; finish

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨2, 0, 0, 0, 2⟩)
  · execute fm 5
  apply progress_nonhalt_simple (fm := fm) (A := ℕ)
    (fun n ↦ ⟨n + 2, 0, 0, 0, 2 * n + 2⟩) 0
  intro n; exists n + 1; exact main_trans n

end Sz22_2003_unofficial_1154
