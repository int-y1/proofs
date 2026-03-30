import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #865: [4/105, 3/22, 175/2, 11/7, 21/5]

Vector representation:
```
 2 -1 -1 -1  0
-1  1  0  0 -1
-1  0  2  1  0
 0  0  0 -1  1
 0  1 -1  1  0
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_865

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a, b+1, c+1, d+1, e⟩ => some ⟨a+2, b, c, d, e⟩
  | ⟨a+1, b, c, d, e+1⟩ => some ⟨a, b+1, c, d, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b, c+2, d+1, e⟩
  | ⟨a, b, c, d+1, e⟩ => some ⟨a, b, c, d, e+1⟩
  | ⟨a, b, c+1, d, e⟩ => some ⟨a, b+1, c, d+1, e⟩
  | _ => none

-- R4 chain: move d to e
theorem d_to_e : ∀ k, ∀ d e, ⟨0, 0, c, d + k, e⟩ [fm]⊢* ⟨(0 : ℕ), 0, c, d, e + k⟩ := by
  intro k; induction' k with k ih <;> intro d e
  · exists 0
  · rw [show d + (k + 1) = (d + k) + 1 from by ring]
    step fm
    rw [show e + (k + 1) = (e + 1) + k from by ring]
    exact ih d (e + 1)

-- R3 chain: convert a to c,d
theorem r3_chain : ∀ k, ∀ c d, ⟨a + k, 0, c, d, 0⟩ [fm]⊢* ⟨a, 0, c + 2 * k, d + k, 0⟩ := by
  intro k; induction' k with k ih <;> intro c d
  · exists 0
  · rw [show a + (k + 1) = (a + k) + 1 from by ring]
    step fm
    apply stepStar_trans (ih (c + 2) (d + 1))
    ring_nf; finish

-- One spiral round: (0, b, c+2, 0, e+2) →4→ (0, b+2, c, 0, e)
theorem spiral_round : ∀ b c e, ⟨0, b, c + 2, 0, e + 2⟩ [fm]⊢* ⟨(0 : ℕ), b + 2, c, 0, e⟩ := by
  intro b c e
  rw [show c + 2 = c + 1 + 1 from by ring,
      show e + 2 = (e + 1) + 1 from by ring]
  step fm  -- R5
  step fm  -- R1
  show ⟨1 + 1, b, c, 0, (e + 1) + 1⟩ [fm]⊢* _
  step fm  -- R2
  show ⟨0 + 1, b + 1, c, 0, e + 1⟩ [fm]⊢* _
  step fm  -- R2
  rw [show b + 1 + 1 = b + 2 from by ring]
  finish

-- Spiral: repeated rounds
theorem spiral : ∀ k, ∀ b c, ⟨0, b, c + 2 * k, 0, 2 * k⟩ [fm]⊢* ⟨(0 : ℕ), b + 2 * k, c, 0, 0⟩ := by
  intro k; induction' k with k ih <;> intro b c
  · exists 0
  · rw [show c + 2 * (k + 1) = (c + 2 * k) + 2 from by ring,
        show 2 * (k + 1) = 2 * k + 2 from by ring]
    apply stepStar_trans (spiral_round b (c + 2 * k) (2 * k))
    rw [show b + (2 * k + 2) = (b + 2) + 2 * k from by ring]
    exact ih (b + 2) c

-- One r3r1 round: (a+1, b+1, c, 0, 0) →2→ (a+2, b, c+1, 0, 0)
theorem r3r1_round : ∀ a b c, ⟨a + 1, b + 1, c, 0, 0⟩ [fm]⊢* ⟨a + 2, b, c + 1, 0, 0⟩ := by
  intro a b c
  step fm  -- R3
  step fm  -- R1
  finish

-- R3+R1 chain
theorem r3r1_chain : ∀ k, ∀ a b c, ⟨a + 1, b + k, c, 0, 0⟩ [fm]⊢* ⟨a + 1 + k, b, c + k, 0, 0⟩ := by
  intro k; induction' k with k ih <;> intro a b c
  · exists 0
  · rw [show b + (k + 1) = (b + k) + 1 from by ring]
    apply stepStar_trans (r3r1_round a (b + k) c)
    rw [show a + 1 + (k + 1) = (a + 2) + k from by ring,
        show a + 2 = (a + 1) + 1 from by ring,
        show c + (k + 1) = (c + 1) + k from by ring]
    exact ih (a + 1) b (c + 1)

-- R5+R1: (0, b+1, c+1+1, 0, 0) →2→ (2, b+1, c, 0, 0)
-- R5: (a, b, c+1, d, e) => (a, b+1, c, d+1, e)
-- From (0, b+1, c+1+1, 0, 0): R5 fires → (0, b+2, c+1, 1, 0)
-- R1: (a, b+1, c+1, d+1, e) => (a+2, b, c, d, e)
-- From (0, b+2, c+1, 1, 0): b+2 = (b+1)+1, c+1, d+1=1→d=0
-- R1 fires → (2, b+1, c, 0, 0)
theorem r5r1 : ∀ b c, ⟨0, b + 1, c + 1 + 1, 0, 0⟩ [fm]⊢* ⟨(2 : ℕ), b + 1, c, 0, 0⟩ := by
  intro b c
  step fm  -- R5
  step fm  -- R1
  finish

-- Combined phase 3: R5+R1 + r3r1_chain
-- (0, b+1, c+1+1, 0, 0) →* (2, b+1, c, 0, 0) →* (2+b+1, 0, c+b+1, 0, 0)
-- = (b+3, 0, c+b+1, 0, 0)
theorem phase3 : ∀ b c, ⟨0, b + 1, c + 1 + 1, 0, 0⟩ [fm]⊢* ⟨b + 3, 0, c + b + 1, 0, 0⟩ := by
  intro b c
  apply stepStar_trans (r5r1 b c)
  -- (2, b+1, c, 0, 0) = (1+1, 0+(b+1), c, 0, 0)
  rw [show (2 : ℕ) = 1 + 1 from rfl,
      show b + 1 = 0 + (b + 1) from by ring]
  apply stepStar_trans (r3r1_chain (b + 1) 1 0 c)
  rw [show 1 + 1 + (b + 1) = b + 3 from by ring,
      show c + (b + 1) = c + b + 1 from by ring]
  finish

-- Main transition
theorem main_trans (n : ℕ) :
    ⟨0, 0, 2 * n ^ 2 + 4 * n + 5, 2 * n + 2, 0⟩ [fm]⊢⁺
    ⟨(0 : ℕ), 0, 2 * n ^ 2 + 8 * n + 11, 2 * n + 4, 0⟩ := by
  -- Phase 1: d_to_e
  rw [show 2 * n + 2 = 0 + (2 * n + 2) from by ring]
  apply stepStar_stepPlus_stepPlus (d_to_e (2 * n + 2) 0 0 (c := 2 * n ^ 2 + 4 * n + 5))
  -- (0, 0, 2*n^2+4*n+5, 0, 2*n+2)
  -- Phase 2: spiral with k = n+1
  rw [show (0 : ℕ) + (2 * n + 2) = 2 * (n + 1) from by ring,
      show 2 * n ^ 2 + 4 * n + 5 = (2 * n ^ 2 + 2 * n + 3) + 2 * (n + 1) from by ring]
  apply stepStar_stepPlus_stepPlus (spiral (n + 1) 0 (2 * n ^ 2 + 2 * n + 3))
  -- (0, 0+2*(n+1), 2*n^2+2*n+3, 0, 0)
  -- Phase 3a: R5 (one step for ⊢⁺)
  rw [show (0 : ℕ) + 2 * (n + 1) = (2 * n + 1) + 1 from by ring,
      show 2 * n ^ 2 + 2 * n + 3 = (2 * n ^ 2 + 2 * n + 1) + 1 + 1 from by ring]
  step fm  -- R5: gives ⊢⁺, remaining ⊢*
  -- Phase 3b: R1 + r3r1_chain + r3_chain (all as ⊢*)
  -- After R5: (0, (2*n+1)+1+1, (2*n^2+2*n+1)+1, 1, 0)
  step fm  -- R1: (2, (2*n+1)+1, 2*n^2+2*n+1, 0, 0)
  -- Now remaining goal is ⊢*
  -- (2, 2*n+2, 2*n^2+2*n+1, 0, 0) = (1+1, 0+(2*n+2), 2*n^2+2*n+1, 0, 0)
  rw [show (2 * n + 2 : ℕ) = 0 + (2 * n + 2) from by ring]
  apply stepStar_trans (r3r1_chain (2 * n + 2) 1 0 (2 * n ^ 2 + 2 * n + 1))
  -- (1+1+(2*n+2), 0, (2*n^2+2*n+1)+(2*n+2), 0, 0)
  rw [show 1 + 1 + (2 * n + 2) = 0 + (2 * n + 4) from by ring,
      show 2 * n ^ 2 + 2 * n + 1 + (2 * n + 2) = 2 * n ^ 2 + 4 * n + 3 from by ring]
  -- Phase 4: r3_chain
  apply stepStar_trans (r3_chain (2 * n + 4) (2 * n ^ 2 + 4 * n + 3) 0 (a := 0))
  ring_nf; finish

theorem nonhalt : ¬halts fm c₀ := by
  have h9 : c₀ [fm]⊢* ⟨0, 0, 2 * 0 ^ 2 + 4 * 0 + 5, 2 * 0 + 2, 0⟩ := by
    execute fm 9
  apply stepStar_not_halts_not_halts h9
  apply progress_nonhalt_simple (fm := fm) (A := ℕ)
    (fun n ↦ ⟨0, 0, 2 * n ^ 2 + 4 * n + 5, 2 * n + 2, 0⟩) 0
  intro n
  refine ⟨n + 1, ?_⟩
  rw [show 2 * (n + 1) ^ 2 + 4 * (n + 1) + 5 = 2 * n ^ 2 + 8 * n + 11 from by ring,
      show 2 * (n + 1) + 2 = 2 * n + 4 from by ring]
  exact main_trans n
