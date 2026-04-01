import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #1575: [7/45, 4/21, 121/3, 15/2, 9/11]

Vector representation:
```
 0 -2 -1  1  0
 2 -1  0 -1  0
 0 -1  0  0  2
-1  1  1  0  0
 0  2  0  0 -1
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_1575

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a, b+2, c+1, d, e⟩ => some ⟨a, b, c, d+1, e⟩
  | ⟨a, b+1, c, d+1, e⟩ => some ⟨a+2, b, c, d, e⟩
  | ⟨a, b+1, c, d, e⟩ => some ⟨a, b, c, d, e+2⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b+1, c+1, d, e⟩
  | ⟨a, b, c, d, e+1⟩ => some ⟨a, b+2, c, d, e⟩
  | _ => none

-- R5+R1 chain: (0, 0, c+k, d, e+k) ⊢* (0, 0, c, d+k, e)
theorem r5r1_chain : ∀ k, ∀ c d e, ⟨0, 0, c + k, d, e + k⟩ [fm]⊢* ⟨0, 0, c, d + k, e⟩ := by
  intro k; induction' k with k ih
  · intro c d e; exists 0
  · intro c d e
    rw [show c + (k + 1) = (c + k) + 1 from by ring,
        show e + (k + 1) = e + k + 1 from by ring]
    step fm
    rw [show c + k + 1 = (c + k) + 1 from by ring]
    step fm
    apply stepStar_trans (ih c (d + 1) e)
    ring_nf; finish

-- R4+R2 chain: (a+1, 0, c, k, g) ⊢* (a+1+k, 0, c+k, 0, g)
theorem r4r2_chain : ∀ k, ∀ a c g, ⟨a + 1, 0, c, k, g⟩ [fm]⊢* ⟨a + 1 + k, 0, c + k, 0, g⟩ := by
  intro k; induction' k with k ih
  · intro a c g; exists 0
  · intro a c g
    step fm
    step fm
    rw [show a + 2 = (a + 1) + 1 from by ring]
    apply stepStar_trans (ih (a + 1) (c + 1) g)
    ring_nf; finish

-- R4+R3 descent: (a, 0, c, 0, e) ⊢* (0, 0, c+a, 0, e+2*a)
theorem r4r3_descent : ∀ a, ∀ c e, ⟨a, 0, c, 0, e⟩ [fm]⊢* ⟨0, 0, c + a, 0, e + 2 * a⟩ := by
  intro a; induction' a with a ih
  · intro c e; exists 0
  · intro c e
    step fm
    step fm
    apply stepStar_trans (ih (c + 1) (e + 2))
    ring_nf; finish

-- Main transition: (0, 0, c+2, 0, c+g+3) ⊢⁺ (0, 0, 2*c+4, 0, 2*c+g+8)
theorem main_trans (c g : ℕ) :
    ⟨0, 0, c + 2, 0, c + g + 3⟩ [fm]⊢⁺ ⟨0, 0, 2 * c + 4, 0, 2 * c + g + 8⟩ := by
  -- Phase 1: R5+R1 chain
  rw [show c + 2 = 0 + (c + 2) from by ring,
      show c + g + 3 = (g + 1) + (c + 2) from by ring]
  apply stepStar_stepPlus_stepPlus (r5r1_chain (c + 2) 0 0 (g + 1))
  -- Now at (0, 0, 0, c+2, g+1). Goal is ⊢⁺.
  rw [show 0 + (c + 2) = c + 2 from by ring]
  -- Phase 2: first step converts ⊢⁺ to ⊢*, remaining steps are ⊢*
  step fm  -- R5: (0, 2, 0, c+2, g). Now goal is ⊢*.
  rw [show (2 : ℕ) = 1 + 1 from by ring]
  step fm  -- R2: (2, 0, 0, c+1, g)
  step fm  -- R2: (4, 0, 0, c, g)
  -- Phase 3: R4+R2 chain
  rw [show (4 : ℕ) = 3 + 1 from by ring]
  apply stepStar_trans (r4r2_chain c 3 0 g)
  rw [show 3 + 1 + c = c + 4 from by ring, show 0 + c = c from by ring]
  -- Phase 4: R4+R3 descent
  apply stepStar_trans (r4r3_descent (c + 4) c g)
  rw [show c + (c + 4) = 2 * c + 4 from by ring,
      show g + 2 * (c + 4) = 2 * c + g + 8 from by ring]
  finish

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨0, 0, 2, 0, 6⟩) (by execute fm 11)
  rw [show (2 : ℕ) = 0 + 2 from by ring, show (6 : ℕ) = 0 + 3 + 3 from by ring]
  apply progress_nonhalt_simple (fm := fm) (A := ℕ × ℕ)
    (fun ⟨c, g⟩ ↦ ⟨0, 0, c + 2, 0, c + g + 3⟩) ⟨0, 3⟩
  intro ⟨c, g⟩; simp only
  exact ⟨⟨2 * c + 2, g + 3⟩, by
    show ⟨0, 0, c + 2, 0, c + g + 3⟩ [fm]⊢⁺ ⟨0, 0, (2 * c + 2) + 2, 0, (2 * c + 2) + (g + 3) + 3⟩
    rw [show (2 * c + 2) + 2 = 2 * c + 4 from by ring,
        show (2 * c + 2) + (g + 3) + 3 = 2 * c + g + 8 from by ring]
    exact main_trans c g⟩

end Sz22_2003_unofficial_1575
