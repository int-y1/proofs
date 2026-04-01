import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #1386: [63/10, 5/363, 22/3, 11/7, 15/2]

Vector representation:
```
-1  2 -1  1  0
 0 -1  1  0 -2
 1 -1  0  0  1
 0  0  0 -1  1
-1  1  1  0  0
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_1386

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a+1, b, c+1, d, e⟩ => some ⟨a, b+2, c, d+1, e⟩
  | ⟨a, b+1, c, d, e+2⟩ => some ⟨a, b, c+1, d, e⟩
  | ⟨a, b+1, c, d, e⟩ => some ⟨a+1, b, c, d, e+1⟩
  | ⟨a, b, c, d+1, e⟩ => some ⟨a, b, c, d, e+1⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b+1, c+1, d, e⟩
  | _ => none

-- R4 chain: transfer d to e
theorem d_to_e : ∀ k e, ∀ d, ⟨a, 0, 0, d + k, e⟩ [fm]⊢* ⟨a, 0, 0, d, e + k⟩ := by
  intro k; induction' k with k ih <;> intro e d
  · exists 0
  · rw [show d + (k + 1) = d + k + 1 from by ring]; step fm
    have := ih (e + 1) d
    rw [show e + 1 + k = e + (k + 1) from by ring] at this; exact this

-- R1R2 pairs
theorem r1r2_pairs : ∀ k, ∀ a b d,
    ⟨a + k + 1, b, 1, d, e + 2 * k + 2⟩ [fm]⊢*
    ⟨a + 1, b + k, 1, d + k, e + 2⟩ := by
  intro k; induction' k with k ih <;> intro a b d
  · exists 0
  · rw [show a + (k + 1) + 1 = (a + k + 1) + 1 from by ring,
        show (1 : ℕ) = 0 + 1 from by ring,
        show e + 2 * (k + 1) + 2 = (e + 2 * k + 2) + 2 from by ring]
    step fm; step fm
    apply stepStar_trans (ih a (b + 1) (d + 1)); ring_nf; finish

-- R2 drain
theorem r2_drain : ∀ k, ∀ b c d, ⟨0, b + k + 1, c, d, 2 * k + 2⟩ [fm]⊢*
    ⟨0, b + 1, c + k, d, 2⟩ := by
  intro k; induction' k with k ih <;> intro b c d
  · exists 0
  · rw [show b + (k + 1) + 1 = (b + k + 1) + 1 from by ring,
        show 2 * (k + 1) + 2 = (2 * k + 2) + 2 from by ring]
    step fm
    apply stepStar_trans (ih b (c + 1) d); ring_nf; finish

-- Middle 5-step cycle
theorem middle_cycle : ∀ k, ∀ b c d,
    ⟨0, b + 1, c + k + 1, d, 0⟩ [fm]⊢* ⟨0, b + k + 1, c + 1, d + 2 * k, 0⟩ := by
  intro k; induction' k with k ih <;> intro b c d
  · exists 0
  · rw [show c + (k + 1) + 1 = (c + k + 1) + 1 from by ring]
    step fm; step fm
    rw [show b + 2 = (b + 1) + 1 from by ring]; step fm
    rw [show c + k + 1 = (c + k) + 1 from by ring]; step fm
    rw [show b + 1 + 2 = (b + 2) + 1 from by ring, show (2 : ℕ) = 0 + 2 from by ring]
    step fm
    rw [show b + 2 = (b + 1) + 1 from by ring]
    apply stepStar_trans (ih (b + 1) c (d + 2)); ring_nf; finish

-- Tail chain: k rounds of R3,R3,R2,R1
theorem tail_chain : ∀ k, ∀ a d,
    ⟨a, k + 3, 0, d, 0⟩ [fm]⊢* ⟨a + k, 3, 0, d + k, 0⟩ := by
  intro k; induction' k with k ih <;> intro a d
  · exists 0
  · rw [show (k + 1) + 3 = (k + 3) + 1 from by ring]
    step fm  -- R3
    rw [show k + 3 = (k + 2) + 1 from by ring]
    step fm  -- R3
    rw [show k + 2 = (k + 1) + 1 from by ring, show (2 : ℕ) = 0 + 2 from by ring]
    step fm  -- R2
    -- After R2: (a+2, k+1, 1, d, 0). Now R1:
    rw [show a + 1 + 1 = (a + 1) + 1 from by ring, show (1 : ℕ) = 0 + 1 from by ring]
    step fm  -- R1
    -- (a+1, k+3, 0, d+1, 0)
    rw [show k + 1 + 2 = k + 3 from by ring]
    apply stepStar_trans (ih (a + 1) (d + 1)); ring_nf; finish

-- Phase 1-3: (n+2, 0, 1, 4n+5, 0) ⊢⁺ (1, 0, n+3, n+2, 1)
theorem phases_1_to_3 (n : ℕ) :
    ⟨n + 2, 0, 1, 4 * n + 5, 0⟩ [fm]⊢⁺ ⟨1, 0, n + 3, n + 2, 1⟩ := by
  -- R1: (n+2, 0, 1, 4n+5, 0) -> (n+1, 2, 0, 4n+6, 0)
  rw [show n + 2 = (n + 1) + 1 from by ring,
      show (1 : ℕ) = 0 + 1 from by ring,
      show 4 * n + 5 = (4 * n + 4) + 1 from by ring]
  step fm
  -- R3: (n+1, 2, 0, 4n+6, 0) -> (n+2, 1, 0, 4n+6, 1)
  rw [show (2 : ℕ) = 1 + 1 from by ring]; step fm
  -- R3: (n+2, 1, 0, 4n+6, 1) -> (n+3, 0, 0, 4n+6, 2)
  rw [show (1 : ℕ) = 0 + 1 from by ring]; step fm
  -- d_to_e: (n+3, 0, 0, 4n+6, 2) -> (n+3, 0, 0, 0, 4n+8)
  rw [show 4 * n + 4 + 1 + 1 = 0 + (4 * n + 6) from by ring]
  apply stepStar_trans (d_to_e (a := n + 3) (4 * n + 6) 2 0)
  rw [show 2 + (4 * n + 6) = 4 * n + 8 from by ring]
  -- R5: (n+3, 0, 0, 0, 4n+8) -> (n+2, 1, 1, 0, 4n+8)
  rw [show n + 3 = (n + 2) + 1 from by ring]; step fm
  -- R1R2 pairs: k=n+1
  rw [show n + 2 = 0 + (n + 1) + 1 from by ring,
      show (1 : ℕ) = 0 + 1 from by ring,
      show 4 * n + 8 = (2 * n + 4) + 2 * (n + 1) + 2 from by ring]
  apply stepStar_trans (r1r2_pairs (e := 2 * n + 4) (n + 1) 0 1 0)
  rw [show 0 + 1 = 1 from by ring, show 1 + (n + 1) = n + 2 from by ring,
      show 0 + (n + 1) = n + 1 from by ring, show 2 * n + 4 + 2 = 2 * n + 6 from by ring]
  -- (1, n+2, 1, n+1, 2n+6)
  -- R1: -> (0, n+4, 0, n+2, 2n+6)
  rw [show (1 : ℕ) = 0 + 1 from by ring, show (1 : ℕ) = 0 + 1 from by ring]; step fm
  rw [show n + 2 + 2 = 1 + (n + 2) + 1 from by ring,
      show n + 1 + 1 = n + 2 from by ring,
      show 2 * n + 6 = 2 * (n + 2) + 2 from by ring]
  -- R2 drain: k=n+2
  apply stepStar_trans (r2_drain (n + 2) 1 0 (n + 2))
  rw [show 0 + (n + 2) = n + 2 from by ring]
  -- (0, 2, n+2, n+2, 2). State in Lean: (0, 1+1, n+(1+1), n+(1+1), 1+1)
  -- R2: -> (0, 1, n+3, n+2, 0)
  step fm
  -- R3: -> (1, 0, n+3, n+2, 1)
  step fm
  ring_nf; finish

-- Phase 4: (1, 0, n+3, n+2, 1) ⊢* (0, n+3, 1, 3n+6, 0)
theorem phase_4 (n : ℕ) :
    ⟨1, 0, n + 3, n + 2, 1⟩ [fm]⊢* ⟨0, n + 3, 1, 3 * n + 6, 0⟩ := by
  -- R1: -> (0, 2, n+2, n+3, 1)
  rw [show (1 : ℕ) = 0 + 1 from by ring, show n + 3 = (n + 2) + 1 from by ring]; step fm
  -- R3: -> (1, 1, n+2, n+3, 2)
  rw [show (2 : ℕ) = 1 + 1 from by ring]; step fm
  -- R1: -> (0, 3, n+1, n+4, 2)
  rw [show (1 : ℕ) = 0 + 1 from by ring, show n + 2 = (n + 1) + 1 from by ring]; step fm
  -- R2: -> (0, 2, n+2, n+4, 0)
  rw [show (3 : ℕ) = 2 + 1 from by ring,
      show n + 3 + 1 = n + 4 from by ring,
      show (2 : ℕ) = 0 + 2 from by ring]; step fm
  -- (0, 2, n+2, n+4, 0)
  rw [show n + 1 + 1 = n + 2 from by ring]
  -- middle_cycle: k=n+1, b=1, c=0, d=n+4
  rw [show (2 : ℕ) = 1 + 1 from by ring,
      show n + 2 = 0 + (n + 1) + 1 from by ring]
  apply stepStar_trans (middle_cycle (n + 1) 1 0 (n + 4))
  ring_nf; finish

-- Phase 5: (0, n+3, 1, 3n+6, 0) ⊢* (n+3, 0, 1, 4n+9, 0)
theorem phase_5 (n : ℕ) :
    ⟨0, n + 3, 1, 3 * n + 6, 0⟩ [fm]⊢* ⟨n + 3, 0, 1, 4 * n + 9, 0⟩ := by
  -- R3: -> (1, n+2, 1, 3n+6, 1)
  rw [show n + 3 = (n + 2) + 1 from by ring]; step fm
  -- R1: -> (0, n+4, 0, 3n+7, 1)
  rw [show (1 : ℕ) = 0 + 1 from by ring, show (1 : ℕ) = 0 + 1 from by ring]; step fm
  -- R3: -> (1, n+3, 0, 3n+7, 2)
  rw [show n + 2 + 2 = (n + 3) + 1 from by ring,
      show 3 * n + 6 + 1 = 3 * n + 7 from by ring]; step fm
  -- R2: -> (1, n+2, 1, 3n+7, 0)
  rw [show n + 3 = (n + 2) + 1 from by ring, show (2 : ℕ) = 0 + 2 from by ring]; step fm
  -- R1: -> (0, n+4, 0, 3n+8, 0)
  rw [show n + 2 + 1 = (n + 2) + 1 from by ring,
      show (1 : ℕ) = 0 + 1 from by ring]; step fm
  rw [show n + 2 + 2 = n + 4 from by ring,
      show 3 * n + 7 + 1 = 3 * n + 8 from by ring]
  -- tail_chain: k=n+1
  rw [show n + 4 = (n + 1) + 3 from by ring]
  apply stepStar_trans (tail_chain (n + 1) 0 (3 * n + 8))
  rw [show 0 + (n + 1) = n + 1 from by ring,
      show 3 * n + 8 + (n + 1) = 4 * n + 9 from by ring]
  -- (n+1, 3, 0, 4n+9, 0). Final 3 steps: R3, R3, R2
  rw [show (3 : ℕ) = 2 + 1 from by ring]; step fm
  rw [show (2 : ℕ) = 1 + 1 from by ring]; step fm
  rw [show (1 : ℕ) = 0 + 1 from by ring, show (2 : ℕ) = 0 + 2 from by ring]; step fm
  ring_nf; finish

-- Main transition
theorem main_trans (n : ℕ) :
    ⟨n + 2, 0, 1, 4 * n + 5, 0⟩ [fm]⊢⁺ ⟨n + 3, 0, 1, 4 * n + 9, 0⟩ := by
  apply stepPlus_stepStar_stepPlus (phases_1_to_3 n)
  apply stepStar_trans (phase_4 n)
  exact phase_5 n

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨2, 0, 1, 5, 0⟩)
  · execute fm 27
  apply progress_nonhalt_simple (fm := fm) (A := ℕ)
    (fun n ↦ ⟨n + 2, 0, 1, 4 * n + 5, 0⟩) 0
  intro n; exact ⟨n + 1, main_trans n⟩

end Sz22_2003_unofficial_1386
