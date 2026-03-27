import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #385: [2/15, 99/14, 25/2, 7/11, 28/5]

Vector representation:
```
 1 -1 -1  0  0
-1  2  0 -1  1
-1  0  2  0  0
 0  0  0  1 -1
 2  0 -1  1  0
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_385

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a, b+1, c+1, d, e⟩ => some ⟨a+1, b, c, d, e⟩
  | ⟨a+1, b, c, d+1, e⟩ => some ⟨a, b+2, c, d, e+1⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b, c+2, d, e⟩
  | ⟨a, b, c, d, e+1⟩ => some ⟨a, b, c, d+1, e⟩
  | ⟨a, b, c+1, d, e⟩ => some ⟨a+2, b, c, d+1, e⟩
  | _ => none

-- R2+R1+R1 loop: each iteration consumes 1 from d and 2 from c, producing 1 to a and 1 to e
-- (a+k+2, 0, c+2*k, d, k+e) →* (a+2, 0, c, d+k, e)
-- We go backwards: from (a+2, 0, c, d+k, e) we came from (a+k+2, 0, c+2k, d, k+e)
-- Actually let's define it forwards from the starting point.
-- Start: (2, 0, c+2k, d+k, 0). After k iters of R2,R1,R1: (k+2, 0, c, d, k)
theorem r2r1r1_loop (k : ℕ) : ∀ a c d e,
    ⟨a+2, 0, c+2*k, d+k, e⟩ [fm]⊢* ⟨a+k+2, 0, c, d, k+e⟩ := by
  induction' k with k ih <;> intro a c d e
  · simp; exists 0
  -- Start: (a+2, 0, c+2*(k+1), d+(k+1), e)
  -- = (a+2, 0, (c+2)+2*k, (d+1)+k, e)
  -- By ih: →* (a+k+2, 0, c+2, d+1, k+e)
  -- R2: →  (a+k+1, 2, c+2, d, k+e+1)
  -- R1: →  (a+k+2, 1, c+1, d, k+e+1)
  -- R1: →  (a+k+3, 0, c, d, k+e+1)
  rw [show c + 2 * (k + 1) = (c + 2) + 2 * k from by ring,
      show d + (k + 1) = (d + 1) + k from by ring]
  apply stepStar_trans (ih a (c + 2) (d + 1) e)
  step fm; step fm; step fm
  ring_nf; finish

-- R3 repeated: a → c (2 per a)
theorem r3_repeat (k : ℕ) : ∀ c e,
    ⟨k, 0, c, 0, e⟩ [fm]⊢* ⟨0, 0, c+2*k, 0, e⟩ := by
  induction' k with k ih <;> intro c e
  · simp; exists 0
  step fm
  apply stepStar_trans (ih (c + 2) e)
  ring_nf; finish

-- R4 repeated: e → d
theorem r4_repeat (k : ℕ) : ∀ c d,
    ⟨0, 0, c, d, k⟩ [fm]⊢* ⟨0, 0, c, d+k, 0⟩ := by
  induction' k with k ih <;> intro c d
  · simp; exists 0
  step fm
  apply stepStar_trans (ih c (d + 1))
  ring_nf; finish

-- Main transition for n ≥ 1: C(n+1) ⊢⁺ C(n+2)
-- C(m) = (2, 0, 3m+1, m+1, 0)
-- For m = n+1: (2, 0, 3n+4, n+2, 0) ⊢⁺ (2, 0, 3n+7, n+3, 0)
theorem main_trans_succ (n : ℕ) :
    ⟨2, 0, 3*n+4, n+2, 0⟩ [fm]⊢⁺ ⟨2, 0, 3*n+7, n+3, 0⟩ := by
  -- Phase 1: R2+R1+R1 loop (n+2) times
  -- (2, 0, 3n+4, n+2, 0) = (0+2, 0, n+2*(n+2), 0+(n+2), 0)
  -- →* (0+(n+2)+2, 0, n, 0, (n+2)+0) = (n+4, 0, n, 0, n+2)
  have h1 : ⟨2, 0, 3*n+4, n+2, 0⟩ [fm]⊢* ⟨n+4, 0, n, 0, n+2⟩ := by
    have := r2r1r1_loop (n+2) 0 n 0 0
    simp only [Nat.zero_add, Nat.add_zero] at this
    convert this using 2; ring_nf
  -- Phase 2: R3 (n+4) times
  -- (n+4, 0, n, 0, n+2) →* (0, 0, n+2*(n+4), 0, n+2) = (0, 0, 3n+8, 0, n+2)
  have h2 : ⟨n+4, 0, n, 0, n+2⟩ [fm]⊢* ⟨0, 0, 3*n+8, 0, n+2⟩ := by
    have := r3_repeat (n+4) n (n+2)
    convert this using 2; ring_nf
  -- Phase 3: R4 (n+2) times
  -- (0, 0, 3n+8, 0, n+2) →* (0, 0, 3n+8, n+2, 0)
  have h3 : ⟨0, 0, 3*n+8, 0, n+2⟩ [fm]⊢* ⟨0, 0, 3*n+8, n+2, 0⟩ := by
    have := r4_repeat (n+2) (3*n+8) 0
    simp only [Nat.zero_add] at this; exact this
  -- Phase 4: R5 once
  -- (0, 0, 3n+8, n+2, 0) = (0, 0, (3n+7)+1, n+2, 0) → (2, 0, 3n+7, n+3, 0)
  have h4 : ⟨0, 0, 3*n+8, n+2, 0⟩ [fm]⊢⁺ ⟨2, 0, 3*n+7, n+3, 0⟩ := by
    rw [show 3 * n + 8 = (3 * n + 7) + 1 from by ring]
    step fm; ring_nf; finish
  exact stepStar_stepPlus_stepPlus (stepStar_trans h1 (stepStar_trans h2 h3)) h4

theorem main_trans (n : ℕ) :
    ⟨2, 0, 3*n+1, n+1, 0⟩ [fm]⊢⁺ ⟨2, 0, 3*(n+1)+1, (n+1)+1, 0⟩ := by
  rcases n with _ | n
  · execute fm 8
  · show ⟨2, 0, 3*(n+1)+1, (n+1)+1, 0⟩ [fm]⊢⁺ ⟨2, 0, 3*(n+1+1)+1, (n+1+1)+1, 0⟩
    rw [show 3 * (n + 1) + 1 = 3 * n + 4 from by ring,
        show (n + 1) + 1 = n + 2 from by ring,
        show 3 * (n + 1 + 1) + 1 = 3 * n + 7 from by ring,
        show (n + 1 + 1) + 1 = n + 3 from by ring]
    exact main_trans_succ n

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨2, 0, 3*0+1, 0+1, 0⟩) (by execute fm 2)
  exact progress_nonhalt_simple (fm := fm) (A := ℕ)
    (fun n ↦ ⟨2, 0, 3*n+1, n+1, 0⟩) 0
    (fun n ↦ ⟨n+1, main_trans n⟩)

end Sz22_2003_unofficial_385
