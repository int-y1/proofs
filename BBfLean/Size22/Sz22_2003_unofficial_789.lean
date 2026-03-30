import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #789: [35/6, 605/2, 20/77, 3/5, 7/11]

Vector representation:
```
-1 -1  1  1  0
-1  0  1  0  2
 2  0  1 -1 -1
 0  1 -1  0  0
 0  0  0  1 -1
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_789

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a+1, b+1, c, d, e⟩ => some ⟨a, b, c+1, d+1, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b, c+1, d, e+2⟩
  | ⟨a, b, c, d+1, e+1⟩ => some ⟨a+2, b, c+1, d, e⟩
  | ⟨a, b, c+1, d, e⟩ => some ⟨a, b+1, c, d, e⟩
  | ⟨a, b, c, d, e+1⟩ => some ⟨a, b, c, d+1, e⟩
  | _ => none

-- R4 chain: move c to b
theorem c_to_b : ∀ k b c e, ⟨0, b, c + k, 0, e⟩ [fm]⊢* ⟨0, b + k, c, 0, e⟩ := by
  intro k; induction' k with k ih <;> intro b c e
  · exists 0
  · rw [show c + (k + 1) = (c + k) + 1 from by ring]
    step fm
    apply stepStar_trans (ih (b + 1) c e)
    ring_nf; finish

-- R1R1R3 chain: k rounds of (R1, R1, R3) from a=2, even b
theorem r1r1r3_chain : ∀ k c d e,
    ⟨2, 2 * k, c, d, e + k⟩ [fm]⊢* ⟨2, 0, c + 3 * k, d + k, e⟩ := by
  intro k; induction' k with k ih <;> intro c d e
  · exists 0
  · rw [show 2 * (k + 1) = (2 * k + 1) + 1 from by ring,
        show e + (k + 1) = e + k + 1 from by ring,
        show (2 : ℕ) = 1 + 1 from by ring]
    step fm
    rw [show (1 : ℕ) = 0 + 1 from by ring]
    step fm
    rw [show d + 1 + 1 = (d + 1) + 1 from by ring,
        show e + k + 1 = (e + k) + 1 from by ring]
    step fm
    show ⟨2, 2 * k, c + 1 + 1 + 1, d + 1, e + k⟩ [fm]⊢* _
    rw [show c + 1 + 1 + 1 = c + 3 from by ring]
    apply stepStar_trans (ih (c + 3) (d + 1) e)
    ring_nf; finish

-- R1R3R1 chain: k rounds of (R1, R3, R1) from a=1, even b
-- (1, 2k, c, d, e+k) →* (1, 0, c+3k, d+k, e)
-- Each round: R1 → R3 → R1, b decreases by 2
theorem r1r3r1_chain : ∀ k c d e,
    ⟨1, 2 * k, c, d, e + k⟩ [fm]⊢* ⟨1, 0, c + 3 * k, d + k, e⟩ := by
  intro k; induction' k with k ih <;> intro c d e
  · exists 0
  · -- State: (1, 2(k+1), c, d, e+k+1)
    rw [show 2 * (k + 1) = (2 * k) + 1 + 1 from by ring,
        show e + (k + 1) = e + k + 1 from by ring,
        show (1 : ℕ) = 0 + 1 from by ring]
    -- R1: (0+1, (2k)+1+1, c, d, e+k+1) → (0, 2k+1, c+1, d+1, e+k+1)
    step fm
    -- R3: (0, 2k+1, c+1, d+1, e+k+1). d+1 >= 1, e+k+1 >= 1.
    rw [show e + k + 1 = (e + k) + 1 from by ring]
    step fm
    -- Result: (2, 2k+1, c+2, d, e+k)
    -- R1: (2, 2k+1, c+2, d, e+k). a=2=1+1, b=2k+1=(2k)+1.
    rw [show (2 : ℕ) = 1 + 1 from by ring,
        show 2 * k + 1 = (2 * k) + 1 from by ring]
    step fm
    -- Result: (1, 2k, c+3, d+1, e+k)
    show ⟨1, 2 * k, c + 1 + 1 + 1, d + 1, e + k⟩ [fm]⊢* _
    rw [show c + 1 + 1 + 1 = c + 3 from by ring]
    apply stepStar_trans (ih (c + 3) (d + 1) e)
    ring_nf; finish

-- R3R2R2 chain: k rounds of (R3, R2, R2)
-- (0, 0, c, d+k, e+1) →* (0, 0, c+3k, d, e+3k+1)
theorem r3r2r2_chain : ∀ k c d e,
    ⟨0, 0, c, d + k, e + 1⟩ [fm]⊢* ⟨0, 0, c + 3 * k, d, e + 3 * k + 1⟩ := by
  intro k; induction' k with k ih <;> intro c d e
  · exists 0
  · -- State: (0, 0, c, d+k+1, e+1)
    rw [show d + (k + 1) = (d + k) + 1 from by ring]
    -- R3: (0, 0, c, (d+k)+1, e+1) → (2, 0, c+1, d+k, e)
    step fm
    -- R2: (2, 0, c+1, d+k, e). a=2=1+1.
    rw [show (2 : ℕ) = 1 + 1 from by ring]
    step fm
    -- R2: (1, 0, c+2, d+k, e+2). a=1=0+1.
    rw [show (1 : ℕ) = 0 + 1 from by ring]
    step fm
    -- Result: (0, 0, c+3, d+k, e+4)
    show ⟨0, 0, c + 1 + 1 + 1, d + k, e + 2 + 2⟩ [fm]⊢* _
    rw [show c + 1 + 1 + 1 = c + 3 from by ring,
        show e + 2 + 2 = (e + 3) + 1 from by ring]
    apply stepStar_trans (ih (c + 3) d (e + 3))
    ring_nf; finish

-- Even transition: (0, 0, 2(k+1), 0, e+k+3) →⁺ (0, 0, 6k+9, 0, e+3k+7)
theorem even_trans (k e : ℕ) :
    ⟨0, 0, 2 * (k + 1), 0, e + k + 3⟩ [fm]⊢⁺ ⟨0, 0, 6 * k + 9, 0, e + 3 * k + 7⟩ := by
  -- c_to_b
  apply stepStar_stepPlus_stepPlus
  · rw [show (2 * (k + 1) : ℕ) = 0 + 2 * (k + 1) from by ring]
    exact c_to_b (2 * (k + 1)) 0 0 (e + k + 3)
  rw [show (0 : ℕ) + 2 * (k + 1) = 2 * (k + 1) from by ring]
  -- R5
  rw [show e + k + 3 = (e + k + 2) + 1 from by ring]
  step fm
  -- R3
  rw [show e + k + 2 = (e + k + 1) + 1 from by ring]
  step fm
  -- State: (2, 2*(k+1), 1, 0, e+k+1)
  -- r1r1r3_chain(k+1)
  show ⟨2, 2 * (k + 1), 0 + 1, 0, e + k + 1⟩ [fm]⊢* _
  rw [show (0 : ℕ) + 1 = 1 from by ring,
      show e + k + 1 = e + (k + 1) from by ring]
  apply stepStar_trans (r1r1r3_chain (k + 1) 1 0 e)
  -- State: (2, 0, 3k+4, k+1, e)
  rw [show 1 + 3 * (k + 1) = 3 * k + 4 from by ring,
      show (0 : ℕ) + (k + 1) = k + 1 from by ring]
  -- R2
  rw [show (2 : ℕ) = 1 + 1 from by ring]
  step fm
  -- R2
  rw [show (1 : ℕ) = 0 + 1 from by ring]
  step fm
  -- State: (0, 0, 3k+6, k+1, e+4)
  show ⟨0, 0, 3 * k + 4 + 1 + 1, k + 1, e + 2 + 2⟩ [fm]⊢* _
  rw [show 3 * k + 4 + 1 + 1 = 3 * k + 6 from by ring,
      show k + 1 = 0 + (k + 1) from by ring,
      show e + 2 + 2 = (e + 3) + 1 from by ring]
  apply stepStar_trans (r3r2r2_chain (k + 1) (3 * k + 6) 0 (e + 3))
  ring_nf; finish

-- Odd transition: (0, 0, 2k+1, 0, e+k+2) →⁺ (0, 0, 6k+6, 0, e+3k+5)
theorem odd_trans (k e : ℕ) :
    ⟨0, 0, 2 * k + 1, 0, e + k + 2⟩ [fm]⊢⁺ ⟨0, 0, 6 * k + 6, 0, e + 3 * k + 5⟩ := by
  -- c_to_b
  apply stepStar_stepPlus_stepPlus
  · rw [show (2 * k + 1 : ℕ) = 0 + (2 * k + 1) from by ring]
    exact c_to_b (2 * k + 1) 0 0 (e + k + 2)
  rw [show (0 : ℕ) + (2 * k + 1) = 2 * k + 1 from by ring]
  -- R5
  rw [show e + k + 2 = (e + k + 1) + 1 from by ring]
  step fm
  -- R3
  rw [show e + k + 1 = (e + k) + 1 from by ring]
  step fm
  -- State: (2, 2k+1, 1, 0, e+k)
  -- R1
  show ⟨2, 2 * k + 1, 0 + 1, 0, e + k⟩ [fm]⊢* _
  rw [show (0 : ℕ) + 1 = 1 from by ring,
      show (2 : ℕ) = 1 + 1 from by ring,
      show 2 * k + 1 = (2 * k) + 1 from by ring]
  step fm
  -- State: (1, 2k, 2, 1, e+k)
  -- r1r3r1_chain(k)
  apply stepStar_trans (r1r3r1_chain k 2 1 e)
  -- State: (1, 0, 3k+2, k+1, e)
  rw [show 2 + 3 * k = 3 * k + 2 from by ring,
      show 1 + k = k + 1 from by ring]
  -- R2
  rw [show (1 : ℕ) = 0 + 1 from by ring]
  step fm
  -- State: (0, 0, 3k+3, k+1, e+2)
  show ⟨0, 0, 3 * k + 2 + 1, k + 1, e + 2⟩ [fm]⊢* _
  rw [show 3 * k + 2 + 1 = 3 * k + 3 from by ring,
      show k + 1 = 0 + (k + 1) from by ring,
      show e + 2 = (e + 1) + 1 from by ring]
  apply stepStar_trans (r3r2r2_chain (k + 1) (3 * k + 3) 0 (e + 1))
  ring_nf; finish

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨0, 0, 1, 0, 2⟩) (by execute fm 1)
  apply progress_nonhalt_simple (fm := fm) (A := ℕ × ℕ × Bool)
    (fun p ↦ match p with
      | ⟨k, e, true⟩ => ⟨0, 0, 2 * k + 1, 0, e + k + 2⟩
      | ⟨k, e, false⟩ => ⟨0, 0, 2 * (k + 1), 0, e + k + 3⟩)
    ⟨0, 0, true⟩
  intro ⟨k, e, p⟩
  rcases p with rfl | rfl
  · -- p = false: even case
    refine ⟨⟨3 * k + 4, e + 1, true⟩, ?_⟩
    show ⟨0, 0, 2 * (k + 1), 0, e + k + 3⟩ [fm]⊢⁺ ⟨0, 0, 2 * (3 * k + 4) + 1, 0, e + 1 + (3 * k + 4) + 2⟩
    rw [show 2 * (3 * k + 4) + 1 = 6 * k + 9 from by ring,
        show e + 1 + (3 * k + 4) + 2 = e + 3 * k + 7 from by ring]
    exact even_trans k e
  · -- p = true: odd case
    refine ⟨⟨3 * k + 2, e, false⟩, ?_⟩
    show ⟨0, 0, 2 * k + 1, 0, e + k + 2⟩ [fm]⊢⁺ ⟨0, 0, 2 * (3 * k + 2 + 1), 0, e + (3 * k + 2) + 3⟩
    rw [show 2 * (3 * k + 2 + 1) = 6 * k + 6 from by ring,
        show e + (3 * k + 2) + 3 = e + 3 * k + 5 from by ring]
    exact odd_trans k e
