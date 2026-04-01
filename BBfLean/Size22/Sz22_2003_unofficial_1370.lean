import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #1370: [63/10, 4/77, 121/2, 5/3, 6/11]

Vector representation:
```
-1  2 -1  1  0
 2  0  0 -1 -1
-1  0  0  0  2
 0 -1  1  0  0
 1  1  0  0 -1
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_1370

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a+1, b, c+1, d, e⟩ => some ⟨a, b+2, c, d+1, e⟩
  | ⟨a, b, c, d+1, e+1⟩ => some ⟨a+2, b, c, d, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b, c, d, e+2⟩
  | ⟨a, b+1, c, d, e⟩ => some ⟨a, b, c+1, d, e⟩
  | ⟨a, b, c, d, e+1⟩ => some ⟨a+1, b+1, c, d, e⟩
  | _ => none

-- R1R1R2 chain: k rounds of (R1, R1, R2).
theorem r1r1r2_chain : ∀ k b c d e,
    ⟨2, b, c + 2 * k, d, e + k⟩ [fm]⊢* ⟨2, b + 4 * k, c, d + k, e⟩ := by
  intro k; induction' k with k ih <;> intro b c d e
  · exists 0
  · rw [show c + 2 * (k + 1) = (c + 2 * k + 1) + 1 from by ring,
        show e + (k + 1) = (e + k) + 1 from by ring]
    step fm
    rw [show c + 2 * k + 1 = (c + 2 * k) + 1 from by ring]
    step fm
    rw [show d + 1 + 1 = (d + 1) + 1 from by ring,
        show e + k + 1 = (e + k) + 1 from by ring]
    step fm
    apply stepStar_trans (ih (b + 2 + 2) c (d + 1) e)
    ring_nf; finish

-- R2 drain: (a, b, 0, k, e+k) →* (a+2k, b, 0, 0, e)
theorem r2_drain : ∀ k a b e,
    ⟨a, b, 0, k, e + k⟩ [fm]⊢* ⟨a + 2 * k, b, 0, 0, e⟩ := by
  intro k; induction' k with k ih <;> intro a b e
  · exists 0
  · rw [show e + (k + 1) = (e + k) + 1 from by ring,
        show (k : ℕ) + 1 = k + 1 from rfl]
    step fm
    apply stepStar_trans (ih (a + 2) b e)
    ring_nf; finish

-- R3 drain: (k, b, 0, 0, e) →* (0, b, 0, 0, e+2k)
theorem r3_drain : ∀ k b e,
    ⟨k, b, 0, 0, e⟩ [fm]⊢* ⟨0, b, 0, 0, e + 2 * k⟩ := by
  intro k; induction' k with k ih <;> intro b e
  · exists 0
  · step fm
    apply stepStar_trans (ih b (e + 2))
    ring_nf; finish

-- R4 drain: (0, k, c, 0, e) →* (0, 0, c+k, 0, e)
theorem r4_drain : ∀ k c e,
    ⟨0, k, c, 0, e⟩ [fm]⊢* ⟨0, 0, c + k, 0, e⟩ := by
  intro k; induction' k with k ih <;> intro c e
  · exists 0
  · step fm
    apply stepStar_trans (ih (c + 1) e)
    ring_nf; finish

-- Main transition: (0, 0, 2k+1, 0, 2k+3) ⊢⁺ (0, 0, 4k+3, 0, 4k+5)
theorem main_trans (k : ℕ) :
    ⟨0, 0, 2 * k + 1, 0, 2 * k + 3⟩ [fm]⊢⁺ ⟨0, 0, 4 * k + 3, 0, 4 * k + 5⟩ := by
  rw [show 2 * k + 3 = (2 * k + 2) + 1 from by ring,
      show 2 * k + 1 = (2 * k) + 1 from by ring]
  step fm
  rw [show 2 * k + 2 = (2 * k + 1) + 1 from by ring]
  step fm
  -- State: (0, 3, 2*k, 1, 2*k+1+1)
  -- R2 fires: d=1=0+1, e=2*k+1+1=(2*k+1)+1
  step fm
  -- State: (2, 3, 2*k, 0, 2*k+1)
  rw [show (2 : ℕ) * k + 1 = (k + 1) + k from by ring,
      show (2 : ℕ) * k = 0 + 2 * k from by ring]
  apply stepStar_trans (r1r1r2_chain k 3 0 0 (k + 1))
  rw [show (0 : ℕ) + k = k from by ring,
      show k + 1 = 1 + k from by ring]
  apply stepStar_trans (r2_drain k 2 (3 + 4 * k) 1)
  apply stepStar_trans (r3_drain (2 + 2 * k) (3 + 4 * k) 1)
  apply stepStar_trans (r4_drain (3 + 4 * k) 0 (1 + 2 * (2 + 2 * k)))
  ring_nf; finish

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨0, 0, 3, 0, 5⟩)
  · execute fm 12
  · apply progress_nonhalt_simple (fm := fm) (A := ℕ)
      (fun k ↦ ⟨0, 0, 2 * k + 1, 0, 2 * k + 3⟩) 1
    intro k
    refine ⟨2 * k + 1, ?_⟩
    show ⟨0, 0, 2 * k + 1, 0, 2 * k + 3⟩ [fm]⊢⁺ ⟨0, 0, 2 * (2 * k + 1) + 1, 0, 2 * (2 * k + 1) + 3⟩
    rw [show 2 * (2 * k + 1) + 1 = 4 * k + 3 from by ring,
        show 2 * (2 * k + 1) + 3 = 4 * k + 5 from by ring]
    exact main_trans k
