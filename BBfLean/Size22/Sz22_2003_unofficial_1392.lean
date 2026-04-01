import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #1392: [63/10, 847/2, 4/33, 5/7, 3/5]

Vector representation:
```
-1  2 -1  1  0
-1  0  0  1  2
 2 -1  0  0 -1
 0  0  1 -1  0
 0  1 -1  0  0
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_1392

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a+1, b, c+1, d, e⟩ => some ⟨a, b+2, c, d+1, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b, c, d+1, e+2⟩
  | ⟨a, b+1, c, d, e+1⟩ => some ⟨a+2, b, c, d, e⟩
  | ⟨a, b, c, d+1, e⟩ => some ⟨a, b, c+1, d, e⟩
  | ⟨a, b, c+1, d, e⟩ => some ⟨a, b+1, c, d, e⟩
  | _ => none

-- R4 repeated: move d to c.
theorem d_to_c : ∀ k, ∀ c d, ⟨0, 0, c, d + k, e⟩ [fm]⊢* ⟨0, 0, c + k, d, e⟩ := by
  intro k; induction' k with k ih
  · intro c d; exists 0
  · intro c d
    rw [show d + (k + 1) = (d + k) + 1 from by ring]
    step fm
    apply stepStar_trans (ih (c + 1) d)
    ring_nf; finish

-- R1R1R3 chain: k rounds of (R1, R1, R3).
-- (2, b, 2k+1, d, e+k) →* (2, b+3k, 1, d+2k, e)
theorem r1r1r3_chain : ∀ k, ∀ b d e, ⟨2, b, 2 * k + 1, d, e + k⟩ [fm]⊢*
    ⟨2, b + 3 * k, 1, d + 2 * k, e⟩ := by
  intro k; induction' k with k ih
  · intro b d e; exists 0
  · intro b d e
    rw [show 2 * (k + 1) + 1 = (2 * k + 1 + 1) + 1 from by ring,
        show e + (k + 1) = (e + k) + 1 from by ring]
    step fm -- R1: (1, b+2, 2k+1+1, d+1, (e+k)+1)
    rw [show 2 * k + 1 + 1 = (2 * k + 1) + 1 from by ring]
    step fm -- R1: (0, b+2+2, 2k+1, d+1+1, (e+k)+1)
    -- Now state: (0, b+4, 2k+1, d+2, (e+k)+1) with b+4 = (b+3)+1 and (e+k)+1.
    -- Need R3 to fire. R3 needs (a, b+1, c, d, e+1).
    -- a=0, b+1 matches b+2+2 if b+2+2 = (b+2+1)+1. But step fm already did simp.
    -- After step fm's simp, b+2+2 might become b+4. Then we need b+4 = (b+3)+1.
    rw [show b + 2 + 2 = (b + 3) + 1 from by ring,
        show d + 1 + 1 = d + 2 from by ring]
    step fm -- R3: (2, b+3, 2k+1, d+2, e+k)
    apply stepStar_trans (ih (b + 3) (d + 2) e)
    ring_nf; finish

-- Drain phase: R3R2R2 repeated.
-- (0, b+k, 0, d, e+1) →* (0, b, 0, d+2k, e+3k+1)
theorem drain : ∀ k, ∀ b d e, ⟨0, b + k, 0, d, e + 1⟩ [fm]⊢*
    ⟨0, b, 0, d + 2 * k, e + 3 * k + 1⟩ := by
  intro k; induction' k with k ih
  · intro b d e; exists 0
  · intro b d e
    rw [show b + (k + 1) = (b + k) + 1 from by ring]
    step fm -- R3: (2, b+k, 0, d, e)
    step fm -- R2: (1, b+k, 0, d+1, e+2)
    step fm -- R2: (0, b+k, 0, d+1+1, e+2+2)
    rw [show d + 1 + 1 = d + 2 from by ring,
        show e + 2 + 2 = (e + 3) + 1 from by ring]
    apply stepStar_trans (ih b (d + 2) (e + 3))
    ring_nf; finish

-- Full transition: (0, 0, 0, 2*(k+1), k+m+2) ⊢⁺ (0, 0, 0, 2*(4k+3), 9k+m+9)
theorem main_trans (k m : ℕ) :
    ⟨0, 0, 0, 2 * (k + 1), k + m + 2⟩ [fm]⊢⁺ ⟨0, 0, 0, 2 * (4 * k + 3), 9 * k + m + 9⟩ := by
  -- Phase 1: d_to_c: (0,0,0,2(k+1),k+m+2) →* (0,0,2(k+1),0,k+m+2)
  rw [show (2 * (k + 1) : ℕ) = 0 + 2 * (k + 1) from by ring]
  apply stepStar_stepPlus_stepPlus
    (d_to_c (2 * (k + 1)) (c := 0) (d := 0) (e := k + m + 2))
  -- Now at (0, 0, 2*(k+1), 0, k+m+2)
  rw [show 0 + 2 * (k + 1) = (2 * k + 1) + 1 from by ring,
      show k + m + 2 = (k + m + 1) + 1 from by ring]
  -- R5
  step fm -- R5: (0, 1, 2k+1, 0, k+m+1+1)
  -- R3: 1 = 0+1 matches b+1, k+m+1+1 = (k+m+1)+1 matches e+1
  step fm -- R3: (2, 0, 2k+1, 0, k+m+1)
  -- Interleave
  rw [show k + m + 1 = (m + 1) + k from by ring]
  apply stepStar_trans (r1r1r3_chain k 0 0 (m + 1))
  -- Now at (2, 3k, 1, 2k, m+1)
  simp only [Nat.zero_add]
  -- R1
  rw [show (1 : ℕ) = 0 + 1 from by ring]
  step fm -- R1: (1, 3k+2, 0, 2k+1, m+1)
  -- R2
  step fm -- R2: (0, 3k+2, 0, 2k+1+1, m+1+2)
  -- Drain
  rw [show 2 * k + 1 + 1 = 2 * k + 2 from by ring,
      show m + 1 + 2 = (m + 2) + 1 from by ring,
      show (3 * k + 2 : ℕ) = 0 + (3 * k + 2) from by ring]
  apply stepStar_trans (drain (3 * k + 2) 0 (2 * k + 2) (m + 2))
  ring_nf; finish

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨0, 0, 0, 2, 5⟩) (by execute fm 6)
  apply progress_nonhalt_simple (fm := fm) (A := ℕ × ℕ)
    (fun ⟨k, m⟩ ↦ ⟨0, 0, 0, 2 * (k + 1), k + m + 2⟩) ⟨0, 3⟩
  intro ⟨k, m⟩
  exact ⟨⟨4 * k + 2, 5 * k + m + 5⟩, by
    show ⟨0, 0, 0, 2 * (k + 1), k + m + 2⟩ [fm]⊢⁺
      ⟨0, 0, 0, 2 * (4 * k + 2 + 1), 4 * k + 2 + (5 * k + m + 5) + 2⟩
    rw [show 4 * k + 2 + 1 = 4 * k + 3 from by ring,
        show 4 * k + 2 + (5 * k + m + 5) + 2 = 9 * k + m + 9 from by ring]
    exact main_trans k m⟩

end Sz22_2003_unofficial_1392
