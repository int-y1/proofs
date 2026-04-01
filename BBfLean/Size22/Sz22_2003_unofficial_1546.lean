import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #1546: [7/30, 44/21, 9/2, 5/11, 49/3]

Vector representation:
```
-1 -1 -1  1  0
 2 -1  0 -1  1
-1  2  0  0  0
 0  0  1  0 -1
 0 -1  0  2  0
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_1546

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a+1, b+1, c+1, d, e⟩ => some ⟨a, b, c, d+1, e⟩
  | ⟨a, b+1, c, d+1, e⟩ => some ⟨a+2, b, c, d, e+1⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b+2, c, d, e⟩
  | ⟨a, b, c, d, e+1⟩ => some ⟨a, b, c+1, d, e⟩
  | ⟨a, b+1, c, d, e⟩ => some ⟨a, b, c, d+2, e⟩
  | _ => none

-- R2R1R1 chain: each round drains c by 2.
theorem r2r1r1_chain : ∀ k b d e,
    ⟨0, b + 3 * k, 2 * k, d + 1, e⟩ [fm]⊢* ⟨0, b, 0, d + k + 1, e + k⟩ := by
  intro k; induction' k with k ih <;> intro b d e
  · exists 0
  · rw [show b + 3 * (k + 1) = (b + 3 * k) + 3 from by ring,
        show 2 * (k + 1) = (2 * k + 1) + 1 from by ring,
        show ((b + 3 * k) + 3 : ℕ) = ((b + 3 * k) + 2) + 1 from by ring]
    step fm
    rw [show ((b + 3 * k + 2) : ℕ) = (b + 3 * k + 1) + 1 from by ring]
    step fm
    rw [show (2 * k + 1 : ℕ) = (2 * k) + 1 from by ring,
        show (b + 3 * k + 1 : ℕ) = (b + 3 * k) + 1 from by ring]
    step fm
    apply stepStar_trans (ih b (d + 1) (e + 1))
    ring_nf; finish

-- R2 chain.
theorem r2_chain : ∀ k a b e,
    ⟨a, b + k, 0, k, e⟩ [fm]⊢* ⟨a + 2 * k, b, 0, 0, e + k⟩ := by
  intro k; induction' k with k ih <;> intro a b e
  · exists 0
  · rw [show b + (k + 1) = (b + k) + 1 from by ring,
        show (k + 1 : ℕ) = k + 1 from by ring]
    step fm
    apply stepStar_trans (ih (a + 2) b (e + 1))
    ring_nf; finish

-- R3 chain.
theorem r3_chain : ∀ j b e,
    ⟨j, b, 0, 0, e⟩ [fm]⊢* ⟨0, b + 2 * j, 0, 0, e⟩ := by
  intro j; induction' j with j ih <;> intro b e
  · exists 0
  · step fm
    apply stepStar_trans (ih (b + 2) e)
    ring_nf; finish

-- R4 chain.
theorem r4_chain : ∀ k b c,
    ⟨0, b, c, 0, k⟩ [fm]⊢* ⟨0, b, c + k, 0, 0⟩ := by
  intro k; induction' k with k ih <;> intro b c
  · exists 0
  · rw [show (k + 1 : ℕ) = k + 1 from by ring]
    step fm
    apply stepStar_trans (ih b (c + 1))
    ring_nf; finish

-- Main transition.
theorem main_trans (n : ℕ) :
    ⟨0, 5 * n + 7, 2 * n + 2, 0, 0⟩ [fm]⊢⁺ ⟨0, 5 * n + 12, 2 * n + 4, 0, 0⟩ := by
  rw [show 5 * n + 7 = (5 * n + 6) + 1 from by ring]
  step fm
  rw [show 5 * n + 6 = (2 * n + 3) + 3 * (n + 1) from by ring,
      show 2 * n + 2 = 2 * (n + 1) from by ring]
  change ⟨0, (2 * n + 3) + 3 * (n + 1), 2 * (n + 1), 1 + 1, 0⟩ [fm]⊢*
         ⟨0, 5 * n + 12, 2 * n + 4, 0, 0⟩
  apply stepStar_trans (r2r1r1_chain (n + 1) (2 * n + 3) 1 0)
  rw [show 1 + (n + 1) + 1 = n + 3 from by ring,
      show (0 + (n + 1) : ℕ) = n + 1 from by ring,
      show 2 * n + 3 = n + (n + 3) from by ring]
  apply stepStar_trans (r2_chain (n + 3) 0 n (n + 1))
  rw [show 0 + 2 * (n + 3) = 2 * n + 6 from by ring,
      show n + 1 + (n + 3) = 2 * n + 4 from by ring]
  apply stepStar_trans (r3_chain (2 * n + 6) n (2 * n + 4))
  rw [show n + 2 * (2 * n + 6) = 5 * n + 12 from by ring]
  apply stepStar_trans (r4_chain (2 * n + 4) (5 * n + 12) 0)
  ring_nf; finish

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨0, 7, 2, 0, 0⟩)
  · execute fm 10
  apply progress_nonhalt_simple (fm := fm) (A := ℕ)
    (fun n ↦ ⟨0, 5 * n + 7, 2 * n + 2, 0, 0⟩) 0
  intro n; exact ⟨n + 1, main_trans n⟩

end Sz22_2003_unofficial_1546
