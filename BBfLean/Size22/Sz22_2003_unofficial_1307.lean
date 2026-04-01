import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #1307: [63/10, 121/2, 4/77, 5/3, 10/11]

Vector representation:
```
-1  2 -1  1  0
-1  0  0  0  2
 2  0  0 -1 -1
 0 -1  1  0  0
 1  0  1  0 -1
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_1307

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a+1, b, c+1, d, e⟩ => some ⟨a, b+2, c, d+1, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b, c, d, e+2⟩
  | ⟨a, b, c, d+1, e+1⟩ => some ⟨a+2, b, c, d, e⟩
  | ⟨a, b+1, c, d, e⟩ => some ⟨a, b, c+1, d, e⟩
  | ⟨a, b, c, d, e+1⟩ => some ⟨a+1, b, c+1, d, e⟩
  | _ => none

-- R4 chain: move b to c when a=0, d=0
theorem b_to_c : ∀ k, ⟨(0 : ℕ), b + k, c, (0 : ℕ), e⟩ [fm]⊢* ⟨(0 : ℕ), b, c + k, (0 : ℕ), e⟩ := by
  intro k; induction' k with k ih generalizing b c
  · exists 0
  · rw [show b + (k + 1) = (b + k) + 1 from by ring]
    step fm
    apply stepStar_trans (ih (b := b) (c := c + 1))
    ring_nf; finish

-- Triple chain: R1, R1, R3 repeated n times
-- Each round: (2, b, c+2, d, e+1) → (2, b+4, c, d+1, e)
-- (2, b, 2n, d, n+e) →* (2, b+4n, 0, d+n, e)
theorem triple_chain : ∀ n, ∀ b d e, ⟨(2 : ℕ), b, 2 * n, d, n + e⟩ [fm]⊢* ⟨(2 : ℕ), b + 4 * n, 0, d + n, e⟩ := by
  intro n; induction' n with n ih <;> intro b d e
  · ring_nf; exists 0
  · rw [show 2 * (n + 1) = 2 * n + 1 + 1 from by ring,
        show (n + 1) + e = (n + e) + 1 from by ring]
    step fm
    step fm
    rw [show d + 1 + 1 = (d + 1) + 1 from by ring]
    step fm
    apply stepStar_trans (ih (b + 4) (d + 1) e)
    ring_nf; finish

-- R2R2R3 drain: (2, b, 0, k, e) →* (2, b, 0, 0, e+3k)
theorem r2r2r3_drain : ∀ k, ∀ b e, ⟨(2 : ℕ), b, (0 : ℕ), k, e⟩ [fm]⊢* ⟨(2 : ℕ), b, (0 : ℕ), 0, e + 3 * k⟩ := by
  intro k; induction' k with k ih <;> intro b e
  · exists 0
  · rw [show (k + 1 : ℕ) = k + 1 from rfl]
    step fm
    step fm
    rw [show e + 2 + 2 = (e + 3) + 1 from by ring]
    step fm
    apply stepStar_trans (ih b (e + 3))
    ring_nf; finish

-- Main transition: (0, 0, 2k, 0, 2k+2) ⊢⁺ (0, 0, 4k+2, 0, 4k+4)
theorem main_trans : ⟨(0 : ℕ), (0 : ℕ), 2 * k, (0 : ℕ), 2 * k + 2⟩ [fm]⊢⁺
    ⟨(0 : ℕ), (0 : ℕ), 4 * k + 2, (0 : ℕ), 4 * k + 4⟩ := by
  -- R5: (0,0,2k,0,2k+2) → (1,0,2k+1,0,2k+1)
  rw [show 2 * k + 2 = 2 * k + 1 + 1 from by ring]
  step fm
  -- R1: (1,0,2k+1,0,2k+1) → (0,2,2k,1,2k+1)
  step fm
  -- R3: (0,2,2k,1,2k+1) → (2,2,2k,0,2k)
  rw [show 2 * k + 1 = 2 * k + 1 from rfl]
  step fm
  -- Triple chain: (2,2,2k,0,2k) →* (2,4k+2,0,k,k)
  have h1 := triple_chain k 2 0 k
  rw [show k + k = 2 * k from by ring] at h1
  apply stepStar_trans h1
  -- R2R2R3 drain: (2, 4k+2, 0, k, k) →* (2, 4k+2, 0, 0, 4k)
  rw [show (0 : ℕ) + k = k from by ring]
  apply stepStar_trans (r2r2r3_drain k (2 + 4 * k) k)
  -- R2: (2, 4k+2, 0, 0, 4k) → (1, 4k+2, 0, 0, 4k+2)
  rw [show k + 3 * k = 4 * k from by ring]
  step fm
  -- R2: (1, 4k+2, 0, 0, 4k+2) → (0, 4k+2, 0, 0, 4k+4)
  step fm
  -- R4 chain: (0, 4k+2, 0, 0, 4k+4) →* (0, 0, 4k+2, 0, 4k+4)
  rw [show 2 + 4 * k = 0 + (4 * k + 2) from by ring]
  apply stepStar_trans (b_to_c (4 * k + 2) (b := 0) (c := 0) (e := 4 * k + 2 + 2))
  ring_nf; finish

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨0, 0, 2, 0, 4⟩) (by execute fm 8)
  apply progress_nonhalt_simple (fm := fm) (A := ℕ)
    (fun k ↦ ⟨0, 0, 2 * (k + 1), 0, 2 * (k + 1) + 2⟩) 0
  intro k; exists 2 * k + 2
  show ⟨(0 : ℕ), (0 : ℕ), 2 * (k + 1), (0 : ℕ), 2 * (k + 1) + 2⟩ [fm]⊢⁺
    ⟨(0 : ℕ), (0 : ℕ), 2 * (2 * k + 2 + 1), (0 : ℕ), 2 * (2 * k + 2 + 1) + 2⟩
  have h := @main_trans (k + 1)
  rw [show 4 * (k + 1) + 2 = 2 * (2 * k + 2 + 1) from by ring,
      show 4 * (k + 1) + 4 = 2 * (2 * k + 2 + 1) + 2 from by ring] at h
  exact h
