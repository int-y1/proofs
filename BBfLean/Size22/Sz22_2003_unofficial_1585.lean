import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #1585: [7/45, 605/3, 3/77, 2/11, 63/2]

Vector representation:
```
 0 -2 -1  1  0
 0 -1  1  0  2
 0  1  0 -1 -1
 1  0  0  0 -1
-1  2  0  1  0
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_1585

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a, b+2, c+1, d, e⟩ => some ⟨a, b, c, d+1, e⟩
  | ⟨a, b+1, c, d, e⟩ => some ⟨a, b, c+1, d, e+2⟩
  | ⟨a, b, c, d+1, e+1⟩ => some ⟨a, b+1, c, d, e⟩
  | ⟨a, b, c, d, e+1⟩ => some ⟨a+1, b, c, d, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b+2, c, d+1, e⟩
  | _ => none

-- R3/R2 chain: drain d while increasing c and e.
theorem r3r2_chain : ∀ k, ∀ c e,
    ⟨a, 0, c, k, e + 1⟩ [fm]⊢* ⟨a, 0, c + k, 0, e + k + 1⟩ := by
  intro k; induction' k with k ih <;> intro c e
  · exists 0
  · step fm; step fm
    apply stepStar_trans (ih (c + 1) (e + 1)); ring_nf; finish

-- R4 chain: drain e into a (when b=0, d=0).
theorem r4_chain : ∀ k, ∀ a c,
    ⟨a, 0, c, 0, k⟩ [fm]⊢* ⟨a + k, 0, c, 0, 0⟩ := by
  intro k; induction' k with k ih <;> intro a c
  · exists 0
  · step fm
    apply stepStar_trans (ih (a + 1) c); ring_nf; finish

-- R5/R1 chain: drain a and c while building d.
theorem r5r1_chain : ∀ k, ∀ a c d,
    ⟨a + k, 0, c + k, d, 0⟩ [fm]⊢* ⟨a, 0, c, d + 2 * k, 0⟩ := by
  intro k; induction' k with k ih <;> intro a c d
  · exists 0
  · rw [show a + (k + 1) = (a + k) + 1 from by ring,
        show c + (k + 1) = (c + k) + 1 from by ring]
    step fm; step fm
    apply stepStar_trans (ih a c (d + 2)); ring_nf; finish

-- Main transition: (n+1, 0, 0, d, 0) ⊢⁺ (n+2, 0, 0, 2*d+6, 0)
theorem main_trans (n d : ℕ) :
    ⟨n + 1, 0, 0, d, 0⟩ [fm]⊢⁺ ⟨n + 2, 0, 0, 2 * d + 6, 0⟩ := by
  -- R5, R2, R2: (n+1, 0, 0, d, 0) → (n, 0, 2, d+1, 4)
  step fm; step fm; step fm
  -- R3/R2 chain (d+1 rounds): (n, 0, 2, d+1, 4) → (n, 0, d+3, 0, d+5)
  rw [show (4 : ℕ) = 3 + 1 from rfl]
  apply stepStar_trans (r3r2_chain (d + 1) 2 3 (a := n))
  rw [show 2 + (d + 1) = d + 3 from by ring,
      show 3 + (d + 1) + 1 = d + 5 from by ring]
  -- R4 chain (d+5 rounds): (n, 0, d+3, 0, d+5) → (n+d+5, 0, d+3, 0, 0)
  -- Then R5/R1 chain (d+3 rounds): → (n+2, 0, 0, 2*(d+3), 0)
  have h1 := r4_chain (d + 5) n (d + 3)
  rw [show n + (d + 5) = (n + 2) + (d + 3) from by omega] at h1
  have h2 := r5r1_chain (d + 3) (n + 2) 0 0
  rw [show (0 : ℕ) + (d + 3) = d + 3 from by omega,
      show 0 + 2 * (d + 3) = 2 * d + 6 from by ring] at h2
  apply stepStar_trans h1
  apply stepStar_trans h2
  finish

theorem nonhalt : ¬halts fm c₀ := by
  apply progress_nonhalt_simple (fm := fm) (A := ℕ × ℕ)
    (fun ⟨n, d⟩ ↦ ⟨n + 1, 0, 0, d, 0⟩) ⟨0, 0⟩
  intro ⟨n, d⟩; exact ⟨⟨n + 1, 2 * d + 6⟩, main_trans n d⟩

end Sz22_2003_unofficial_1585
