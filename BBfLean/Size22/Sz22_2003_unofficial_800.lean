import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #800: [35/6, 605/2, 4/77, 3/5, 7/11]

Vector representation:
```
-1 -1  1  1  0
-1  0  1  0  2
 2  0  0 -1 -1
 0  1 -1  0  0
 0  0  0  1 -1
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_800

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a+1, b+1, c, d, e⟩ => some ⟨a, b, c+1, d+1, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b, c+1, d, e+2⟩
  | ⟨a, b, c, d+1, e+1⟩ => some ⟨a+2, b, c, d, e⟩
  | ⟨a, b, c+1, d, e⟩ => some ⟨a, b+1, c, d, e⟩
  | ⟨a, b, c, d, e+1⟩ => some ⟨a, b, c, d+1, e⟩
  | _ => none

-- R4 chain: move c to b when a=0, d=0.
theorem c_to_b : ∀ k, ⟨0, b, c + k, 0, e⟩ [fm]⊢* ⟨0, b + k, c, 0, e⟩ := by
  intro k; induction' k with k ih generalizing b c
  · exists 0
  · rw [show c + (k + 1) = (c + k) + 1 from by ring]
    step fm
    apply stepStar_trans (ih (b := b + 1))
    ring_nf; finish

-- R1,R1,R3 chain: each round drains 2 from b and 1 from e.
theorem r1r1r3_chain : ∀ k, ∀ b c d e,
    ⟨2, b + 2 * k, c, d, e + k⟩ [fm]⊢* ⟨2, b, c + 2 * k, d + k, e⟩ := by
  intro k; induction' k with k ih <;> intro b c d e
  · exists 0
  · rw [show b + 2 * (k + 1) = (b + 2 * k) + 1 + 1 from by ring,
        show e + (k + 1) = (e + k) + 1 from by ring]
    step fm
    rw [show b + 2 * k + 1 = (b + 2 * k) + 1 from by ring]
    step fm
    rw [show e + k + 1 = (e + k) + 1 from by ring]
    step fm
    rw [show c + 1 + 1 = c + 2 from by ring]
    apply stepStar_trans (ih b (c + 2) (d + 1) e)
    ring_nf; finish

-- R2,R2,R3 chain: each round drains 1 from d.
theorem r2r2r3_chain : ∀ k, ∀ c e,
    ⟨2, 0, c, k, e⟩ [fm]⊢* ⟨2, 0, c + 2 * k, 0, e + 3 * k⟩ := by
  intro k; induction' k with k ih <;> intro c e
  · exists 0
  · step fm
    step fm
    rw [show e + 4 = (e + 3) + 1 from by ring]
    step fm
    apply stepStar_trans (ih (c + 2) (e + 3))
    ring_nf; finish

-- Main transition: (1, 0, 2K+1, 0, 2K+1) →⁺ (1, 0, 4K+5, 0, 4K+5).
theorem main_transition (K : ℕ) :
    ⟨1, 0, 2 * K + 1, 0, 2 * K + 1⟩ [fm]⊢⁺ ⟨1, 0, 4 * K + 5, 0, 4 * K + 5⟩ := by
  -- R2: → (0, 0, 2K+2, 0, 2K+3)
  step fm
  -- R4 chain: →* (0, 2K+2, 0, 0, 2K+3)
  rw [show 2 * K + 1 + 1 = 0 + (2 * K + 2) from by ring]
  apply stepStar_trans (c_to_b (2 * K + 2) (b := 0) (c := 0) (e := 2 * K + 1 + 2))
  rw [show 2 * K + 1 + 2 = 2 * K + 3 from by ring]
  -- R5: → (0, 2K+2, 0, 1, 2K+2)
  rw [show (2 * K + 3 : ℕ) = (2 * K + 2) + 1 from by ring]
  step fm
  -- R3: → (2, 2K+2, 0, 0, 2K+1)
  rw [show (2 * K + 2 : ℕ) = (2 * K + 1) + 1 from by ring]
  step fm
  -- R1,R1,R3 chain × (K+1): →* (2, 0, 2K+2, K+1, K)
  show ⟨2, 0 + 2 * K + 2, 0, 0, 2 * K + 1⟩ [fm]⊢* _
  rw [show 0 + 2 * K + 2 = 0 + 2 * (K + 1) from by ring,
      show (2 * K + 1 : ℕ) = K + (K + 1) from by ring]
  apply stepStar_trans (r1r1r3_chain (K + 1) 0 0 0 K)
  -- R2,R2,R3 chain × (K+1): →* (2, 0, 4K+4, 0, 4K+3)
  rw [show 0 + 2 * (K + 1) = 2 * (K + 1) from by ring,
      show 0 + (K + 1) = K + 1 from by ring]
  apply stepStar_trans (r2r2r3_chain (K + 1) (2 * (K + 1)) K)
  -- R2: → (1, 0, 4K+5, 0, 4K+5)
  rw [show 2 * (K + 1) + 2 * (K + 1) = 4 * K + 4 from by ring,
      show K + 3 * (K + 1) = 4 * K + 3 from by ring]
  step fm; finish

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨1, 0, 3, 0, 3⟩) (by execute fm 8)
  apply progress_nonhalt_simple (fm := fm) (A := ℕ)
    (fun K ↦ ⟨1, 0, 2 * K + 1, 0, 2 * K + 1⟩) 1
  intro K
  refine ⟨2 * K + 2, ?_⟩
  rw [show 2 * (2 * K + 2) + 1 = 4 * K + 5 from by ring]
  exact main_transition K
