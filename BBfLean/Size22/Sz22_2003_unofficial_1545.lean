import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #1545: [7/30, 4/21, 363/2, 5/3, 6/11]

Vector representation:
```
-1 -1 -1  1  0
 2 -1  0 -1  0
-1  1  0  0  2
 0 -1  1  0  0
 1  1  0  0 -1
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_1545

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a+1, b+1, c+1, d, e⟩ => some ⟨a, b, c, d+1, e⟩
  | ⟨a, b+1, c, d+1, e⟩ => some ⟨a+2, b, c, d, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b+1, c, d, e+2⟩
  | ⟨a, b+1, c, d, e⟩ => some ⟨a, b, c+1, d, e⟩
  | ⟨a, b, c, d, e+1⟩ => some ⟨a+1, b+1, c, d, e⟩
  | _ => none

-- Phase 1: R3 drain a to b (c=0, d=0)
theorem r3_drain : ∀ k b e, ⟨a + k, b, 0, 0, e⟩ [fm]⊢* ⟨a, b + k, 0, 0, e + 2 * k⟩ := by
  intro k; induction' k with k ih
  · intro b e; exists 0
  · intro b e
    rw [show a + (k + 1) = (a + k) + 1 from by ring]
    step fm
    apply stepStar_trans (ih (b + 1) (e + 2)); ring_nf; finish

-- Phase 2: R4 drain b to c (a=0, d=0)
theorem r4_drain : ∀ k c e, ⟨0, b + k, c, 0, e⟩ [fm]⊢* ⟨0, b, c + k, 0, e⟩ := by
  intro k; induction' k with k ih
  · intro c e; exists 0
  · intro c e
    rw [show b + (k + 1) = (b + k) + 1 from by ring]
    step fm
    apply stepStar_trans (ih (c + 1) e); ring_nf; finish

-- Phase 3: R5,R1 chain draining c and e to d
theorem r5r1_chain : ∀ k c d e, ⟨0, 0, c + k, d, e + k⟩ [fm]⊢* ⟨0, 0, c, d + k, e⟩ := by
  intro k; induction' k with k ih
  · intro c d e; exists 0
  · intro c d e
    rw [show c + (k + 1) = (c + k) + 1 from by ring,
        show e + (k + 1) = (e + k) + 1 from by ring]
    step fm; step fm
    apply stepStar_trans (ih c (d + 1) e); ring_nf; finish

-- Phase 4b: R3,R2 chain draining d, growing a and e
theorem r3r2_chain : ∀ k a d e, ⟨a + 1, 0, 0, d + k, e⟩ [fm]⊢* ⟨a + k + 1, 0, 0, d, e + 2 * k⟩ := by
  intro k; induction' k with k ih
  · intro a d e; exists 0
  · intro a d e
    rw [show d + (k + 1) = (d + k) + 1 from by ring]
    step fm; step fm
    apply stepStar_trans (ih (a + 1) d (e + 2)); ring_nf; finish

-- Main transition: (2n+3, 0, 0, 0, 3n(n+1)) ⊢⁺ (2n+5, 0, 0, 0, 3(n+1)(n+2))
theorem main_trans (n : ℕ) :
    ⟨2 * n + 3, 0, 0, 0, 3 * n * (n + 1)⟩ [fm]⊢⁺ ⟨2 * n + 5, 0, 0, 0, 3 * (n + 1) * (n + 2)⟩ := by
  -- First step: R3
  rw [show 2 * n + 3 = (2 * n + 2) + 1 from by ring]
  step fm
  -- Now at (2n+2, 1, 0, 0, 3n(n+1)+2) with ⊢* remaining
  -- Continue R3 drain
  rw [show (2 * n + 2 : ℕ) = 0 + (2 * n + 2) from by ring]
  apply stepStar_trans (r3_drain (2 * n + 2) 1 (3 * n * (n + 1) + 2) (a := 0))
  -- Now at (0, 1+(2n+2), 0, 0, 3n(n+1)+2+2(2n+2))
  rw [show 1 + (2 * n + 2) = 2 * n + 3 from by ring,
      show 3 * n * (n + 1) + 2 + 2 * (2 * n + 2) = 3 * n * (n + 1) + 4 * n + 6 from by ring]
  -- Phase 2: R4 drain b -> c
  rw [show (2 * n + 3 : ℕ) = 0 + (2 * n + 3) from by ring]
  apply stepStar_trans (r4_drain (2 * n + 3) 0 (3 * n * (n + 1) + 4 * n + 6) (b := 0))
  rw [show (0 + (2 * n + 3) : ℕ) = 2 * n + 3 from by ring]
  -- Phase 3: R5,R1 chain
  rw [show (2 * n + 3 : ℕ) = 0 + (2 * n + 3) from by ring,
      show 3 * n * (n + 1) + 4 * n + 6 = (3 * n * (n + 1) + 2 * n + 3) + (2 * n + 3) from by ring]
  apply stepStar_trans (r5r1_chain (2 * n + 3) 0 0 (3 * n * (n + 1) + 2 * n + 3))
  rw [show (0 + (2 * n + 3) : ℕ) = 2 * n + 3 from by ring]
  -- Phase 4a: R5,R2 opener
  rw [show (2 * n + 3 : ℕ) = (2 * n + 2) + 1 from by ring,
      show 3 * n * (n + 1) + 2 * n + 3 = (3 * n * (n + 1) + 2 * n + 2) + 1 from by ring]
  step fm; step fm
  -- Phase 4b: R3,R2 chain
  rw [show (3 : ℕ) = 2 + 1 from by ring,
      show (2 * n + 2 : ℕ) = 0 + (2 * n + 2) from by ring]
  apply stepStar_trans (r3r2_chain (2 * n + 2) 2 0 (3 * n * (n + 1) + 2 * n + 2))
  rw [show 2 + (2 * n + 2) + 1 = 2 * n + 5 from by ring,
      show 3 * n * (n + 1) + 2 * n + 2 + 2 * (2 * n + 2) = 3 * (n + 1) * (n + 2) from by ring]
  finish

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨3, 0, 0, 0, 0⟩)
  · execute fm 6
  apply progress_nonhalt_simple (fm := fm) (A := ℕ)
    (fun n ↦ ⟨2 * n + 3, 0, 0, 0, 3 * n * (n + 1)⟩) 0
  intro n; exact ⟨n + 1, main_trans n⟩

end Sz22_2003_unofficial_1545
