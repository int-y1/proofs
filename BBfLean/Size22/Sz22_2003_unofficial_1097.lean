import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #1097: [5/6, 343/2, 484/35, 3/11, 5/7]

Vector representation:
```
-1 -1  1  0  0
-1  0  0  3  0
 2  0 -1 -1  2
 0  1  0  0 -1
 0  0  1 -1  0
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_1097

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a+1, b+1, c, d, e⟩ => some ⟨a, b, c+1, d, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b, c, d+3, e⟩
  | ⟨a, b, c+1, d+1, e⟩ => some ⟨a+2, b, c, d, e+2⟩
  | ⟨a, b, c, d, e+1⟩ => some ⟨a, b+1, c, d, e⟩
  | ⟨a, b, c, d+1, e⟩ => some ⟨a, b, c+1, d, e⟩
  | _ => none

-- R4 chain: move e to b.
theorem e_to_b : ∀ k, ⟨0, b, 0, d, e + k⟩ [fm]⊢* ⟨0, b + k, 0, d, e⟩ := by
  intro k; induction' k with k ih generalizing b e
  · exists 0
  · rw [show e + (k + 1) = (e + k) + 1 from by ring]
    step fm
    apply stepStar_trans (ih (b := b + 1))
    ring_nf; finish

-- R1×2 + R3 chain: each round b-=2, c+=1, d-=1, e+=2.
theorem r1r1r3_chain : ∀ k b c d e,
    ⟨2, b + 2 * k, c, d + k, e⟩ [fm]⊢* ⟨2, b, c + k, d, e + 2 * k⟩ := by
  intro k; induction' k with k ih <;> intro b c d e
  · exists 0
  · rw [show b + 2 * (k + 1) = (b + 2 * k) + 1 + 1 from by ring,
        show d + (k + 1) = (d + k) + 1 from by ring]
    step fm
    rw [show b + 2 * k + 1 = (b + 2 * k) + 1 from by ring]
    step fm
    step fm
    apply stepStar_trans (ih b (c + 1) d (e + 2))
    ring_nf; finish

-- R3 + R2×2 chain: each round c-=1, d+=5, e+=2.
theorem r3r2r2_chain : ∀ k c d e,
    ⟨0, 0, c + k, d + k, e⟩ [fm]⊢* ⟨0, 0, c, d + 6 * k, e + 2 * k⟩ := by
  intro k; induction' k with k ih <;> intro c d e
  · exists 0
  · rw [show c + (k + 1) = (c + k) + 1 from by ring,
        show d + (k + 1) = (d + k) + 1 from by ring]
    step fm
    step fm
    step fm
    rw [show d + k + 6 = (d + 6) + k from by ring]
    apply stepStar_trans (ih c (d + 6) (e + 2))
    ring_nf; finish

-- Even case transition helper.
-- From (2, 2k, 0, 4k+1, 2) to (0, 0, 0, 8k+7, 4k+2).
-- Phase: R1×2+R3 chain (k rounds) + R2×2 + R3+R2×2 chain (k rounds).
theorem even_helper : ∀ k,
    ⟨2, 2 * k, 0, 4 * k + 1, 2⟩ [fm]⊢* ⟨0, 0, 0, 8 * k + 7, 4 * k + 2⟩ := by
  intro k
  have h1 := r1r1r3_chain k 0 0 (3 * k + 1) 2
  rw [show 0 + 2 * k = 2 * k from by ring,
      show (3 * k + 1) + k = 4 * k + 1 from by ring] at h1
  apply stepStar_trans h1
  -- State: (2, 0, 0+k, 3k+1, 2+2k)
  rw [show (0 : ℕ) + k = k from by omega,
      show 2 + 2 * k = 2 * k + 2 from by ring]
  step fm
  step fm
  -- State: (0, 0, k, 3k+7, 2k+2)
  have h2 := r3r2r2_chain k 0 (2 * k + 7) (2 * k + 2)
  rw [show (0 : ℕ) + k = k from by omega,
      show (2 * k + 7) + k = 3 * k + 7 from by ring] at h2
  rw [show 3 * k + 1 + 3 + 3 = 3 * k + 7 from by ring]
  apply stepStar_trans h2
  ring_nf; finish

-- Odd case transition helper.
-- From (2, 2k+1, 0, 4k+3, 2) to (0, 0, 0, 8k+11, 4k+4).
theorem odd_helper : ∀ k,
    ⟨2, 2 * k + 1, 0, 4 * k + 3, 2⟩ [fm]⊢* ⟨0, 0, 0, 8 * k + 11, 4 * k + 4⟩ := by
  intro k
  have h1 := r1r1r3_chain k 1 0 (3 * k + 3) 2
  rw [show 1 + 2 * k = 2 * k + 1 from by ring,
      show (3 * k + 3) + k = 4 * k + 3 from by ring] at h1
  apply stepStar_trans h1
  -- State: (2, 1, 0+k, 3k+3, 2+2k)
  rw [show (0 : ℕ) + k = k from by omega,
      show 2 + 2 * k = 2 * k + 2 from by ring]
  step fm  -- R1: (1, 0, k+1, 3k+3, 2k+2)
  step fm  -- R2: (0, 0, k+1, 3k+6, 2k+2)
  have h2 := r3r2r2_chain (k + 1) 0 (2 * k + 5) (2 * k + 2)
  rw [show (0 : ℕ) + (k + 1) = k + 1 from by omega,
      show (2 * k + 5) + (k + 1) = 3 * k + 6 from by ring] at h2
  rw [show 3 * k + 3 + 3 = 3 * k + 6 from by ring]
  apply stepStar_trans h2
  ring_nf; finish

-- Main transition: (0, 0, 0, 2e+3, e) →⁺ (0, 0, 0, 4e+7, 2e+2)
theorem main_trans (e : ℕ) :
    ⟨0, 0, 0, 2 * e + 3, e⟩ [fm]⊢⁺ ⟨0, 0, 0, 4 * e + 7, 2 * e + 2⟩ := by
  -- Phase 1: R4 chain
  have h1 : ⟨0, 0, 0, 2 * e + 3, e⟩ [fm]⊢* ⟨0, e, 0, 2 * e + 3, 0⟩ := by
    have := e_to_b e (b := 0) (d := 2 * e + 3) (e := 0)
    simpa using this
  apply stepStar_stepPlus_stepPlus h1
  -- Phase 2: R5
  rw [show 2 * e + 3 = (2 * e + 2) + 1 from by ring]
  step fm
  -- Phase 3: R3
  rw [show 2 * e + 2 = (2 * e + 1) + 1 from by ring]
  step fm
  -- State: (2, e, 0, 2e+1, 2)
  -- Split on parity of e
  rcases Nat.even_or_odd e with ⟨k, hk⟩ | ⟨k, hk⟩
  · rw [show k + k = 2 * k from by ring] at hk; subst hk
    rw [show 2 * (2 * k) + 1 = 4 * k + 1 from by ring]
    apply stepStar_trans (even_helper k)
    ring_nf; finish
  · subst hk
    rw [show 2 * (2 * k + 1) + 1 = 4 * k + 3 from by ring]
    apply stepStar_trans (odd_helper k)
    ring_nf; finish

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨0, 0, 0, 3, 0⟩)
  · execute fm 1
  apply progress_nonhalt_simple (fm := fm) (A := ℕ)
    (fun e ↦ ⟨0, 0, 0, 2 * e + 3, e⟩) 0
  intro e; exists (2 * e + 2)
  show ⟨0, 0, 0, 2 * e + 3, e⟩ [fm]⊢⁺ ⟨0, 0, 0, 2 * (2 * e + 2) + 3, 2 * e + 2⟩
  rw [show 2 * (2 * e + 2) + 3 = 4 * e + 7 from by ring]
  exact main_trans e

end Sz22_2003_unofficial_1097
