import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #1805: [9/10, 55/21, 2/3, 7/11, 1089/2]

Vector representation:
```
-1  2 -1  0  0
 0 -1  1 -1  1
 1 -1  0  0  0
 0  0  0  1 -1
-1  2  0  0  2
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_1805

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a+1, b, c+1, d, e⟩ => some ⟨a, b+2, c, d, e⟩
  | ⟨a, b+1, c, d+1, e⟩ => some ⟨a, b, c+1, d, e+1⟩
  | ⟨a, b+1, c, d, e⟩ => some ⟨a+1, b, c, d, e⟩
  | ⟨a, b, c, d, e+1⟩ => some ⟨a, b, c, d+1, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b+2, c, d, e+2⟩
  | _ => none

-- R4 repeated: move e to d.
theorem e_to_d : ∀ k, ⟨a, 0, 0, d, e + k⟩ [fm]⊢* ⟨a, 0, 0, d + k, e⟩ := by
  intro k; induction' k with k ih generalizing d e
  · exists 0
  · rw [show e + (k + 1) = (e + k) + 1 from by ring]
    step fm
    apply stepStar_trans (ih (d := d + 1))
    ring_nf; finish

-- R3 repeated: move b to a (when c=0, d=0).
theorem b_to_a : ∀ k, ⟨a, b + k, 0, 0, e⟩ [fm]⊢* ⟨a + k, b, 0, 0, e⟩ := by
  intro k; induction' k with k ih generalizing a b
  · exists 0
  · rw [show b + (k + 1) = (b + k) + 1 from by ring]
    step fm
    apply stepStar_trans (ih (a := a + 1))
    ring_nf; finish

-- R2+R1 interleave: k rounds.
-- (k, b+1, 0, d+k, b+1) →* (0, b+k+1, 0, d, b+k+1)
theorem r2r1_chain : ∀ k, ⟨k, b + 1, 0, d + k, b + 1⟩ [fm]⊢* ⟨0, b + k + 1, 0, d, b + k + 1⟩ := by
  intro k; induction' k with k ih generalizing b d
  · exists 0
  · rw [show d + (k + 1) = (d + k) + 1 from by ring]
    step fm  -- R2
    step fm  -- R1
    apply stepStar_trans (ih (b := b + 1) (d := d))
    ring_nf; finish

-- R2 chain: drain d while a=0.
-- (0, b+k, c, d+k, e) →* (0, b, c+k, d, e+k)
theorem r2_chain : ∀ k, ∀ c, ⟨0, b + k, c, d + k, e⟩ [fm]⊢* ⟨0, b, c + k, d, e + k⟩ := by
  intro k; induction' k with k ih generalizing b d e
  · intro c; exists 0
  · intro c
    rw [show b + (k + 1) = (b + k) + 1 from by ring,
        show d + (k + 1) = (d + k) + 1 from by ring]
    step fm
    apply stepStar_trans (ih (b := b) (d := d) (e := e + 1) (c + 1))
    ring_nf; finish

-- R3+R1 interleave: k rounds.
-- (0, b+1, k, 0, e) →* (0, b+k+1, 0, 0, e)
theorem r3r1_chain : ∀ k, ⟨0, b + 1, k, 0, e⟩ [fm]⊢* ⟨0, b + k + 1, 0, 0, e⟩ := by
  intro k; induction' k with k ih generalizing b e
  · exists 0
  · step fm  -- R3: (1, b, k+1, 0, e)
    step fm  -- R1: (0, b+2, k, 0, e)
    apply stepStar_trans (ih (b := b + 1))
    ring_nf; finish

-- R2 chain specialized: (0, n+3, 0, n+1, n+3) →* (0, 2, n+1, 0, 2n+4)
theorem r2_phase : ⟨0, n + 3, 0, n + 1, n + 3⟩ [fm]⊢* ⟨0, 2, n + 1, 0, 2 * n + 4⟩ := by
  rw [show n + 3 = 2 + (n + 1) from by ring,
      show (n + 1 : ℕ) = 0 + (n + 1) from by ring]
  have h := r2_chain (n + 1) (b := 2) (d := 0) (e := 2 + (0 + (n + 1))) 0
  simp only [Nat.zero_add] at h
  convert h using 2; ring_nf

-- Compose phases into a single stepStar.
theorem phase12 : ⟨n + 1, 2, 0, (n + 1) + (n + 1), 2⟩ [fm]⊢*
    ⟨0, 2, n + 1, 0, 2 * n + 4⟩ := by
  apply stepStar_trans (r2r1_chain (n + 1) (b := 1) (d := n + 1))
  -- Now: (0, 1+(n+1)+1, 0, n+1, 1+(n+1)+1)
  rw [show 1 + (n + 1) + 1 = n + 3 from by ring]
  exact r2_phase

-- Compose remaining phases.
theorem phase34 : ⟨0, 2, n + 1, 0, 2 * n + 4⟩ [fm]⊢*
    ⟨n + 3, 0, 0, 2 * n + 4, 0⟩ := by
  -- R3+R1 chain
  apply stepStar_trans (r3r1_chain (n + 1) (b := 1) (e := 2 * n + 4))
  -- Now: (0, 1+(n+1)+1, 0, 0, 2*n+4)
  rw [show 1 + (n + 1) + 1 = 0 + (n + 3) from by ring]
  -- R3 chain
  apply stepStar_trans (b_to_a (n + 3) (a := 0) (b := 0) (e := 2 * n + 4))
  -- Now: (0+(n+3), 0, 0, 0, 2*n+4)
  rw [show (0 : ℕ) + (n + 3) = n + 3 from by ring,
      show 2 * n + 4 = 0 + (2 * n + 4) from by ring]
  -- R4 chain
  apply stepStar_trans (e_to_d (2 * n + 4) (a := n + 3) (d := 0) (e := 0))
  ring_nf; finish

-- Main transition: (n+2, 0, 0, 2n+2, 0) →⁺ (n+3, 0, 0, 2n+4, 0)
theorem main_trans : ⟨n + 2, 0, 0, 2 * n + 2, 0⟩ [fm]⊢⁺ ⟨n + 3, 0, 0, 2 * n + 4, 0⟩ := by
  rw [show 2 * n + 2 = (n + 1) + (n + 1) from by ring]
  step fm
  apply stepStar_trans phase12
  exact phase34

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨2, 0, 0, 2, 0⟩) (by execute fm 5)
  apply progress_nonhalt_simple (fm := fm) (A := ℕ)
    (fun n ↦ ⟨n + 2, 0, 0, 2 * n + 2, 0⟩) 0
  intro n; exists n + 1; exact main_trans

end Sz22_2003_unofficial_1805
