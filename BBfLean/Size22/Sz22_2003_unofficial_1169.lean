import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #1169: [5/6, 45/77, 7/3, 2/35, 363/2]

Vector representation:
```
-1 -1  1  0  0
 0  2  1 -1 -1
 0 -1  0  1  0
 1  0 -1 -1  0
-1  1  0  0  2
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_1169

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a+1, b+1, c, d, e⟩ => some ⟨a, b, c+1, d, e⟩
  | ⟨a, b, c, d+1, e+1⟩ => some ⟨a, b+2, c+1, d, e⟩
  | ⟨a, b+1, c, d, e⟩ => some ⟨a, b, c, d+1, e⟩
  | ⟨a, b, c+1, d+1, e⟩ => some ⟨a+1, b, c, d, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b+1, c, d, e+2⟩
  | _ => none

-- R5+R1 chain with e accumulator.
-- (2*k+1, 0, c, 0, e) ->* (0, 1, c+k, 0, e+2*k+2).
theorem r5r1_chain : ∀ k, ∀ c e, ⟨2 * k + 1, 0, c, 0, e⟩ [fm]⊢* ⟨0, 1, c + k, 0, e + 2 * k + 2⟩ := by
  intro k; induction' k with k ih <;> intro c e
  · step fm; ring_nf; finish
  · rw [show 2 * (k + 1) + 1 = (2 * k + 1) + 1 + 1 from by ring]
    step fm
    step fm
    apply stepStar_trans (ih (c + 1) (e + 2))
    ring_nf; finish

-- R3+R2 interleaving.
-- (0, b+1, C, 0, E+1) ->* (0, b+E+2, C+E+1, 0, 0).
theorem r3r2_chain : ∀ E, ∀ b C, ⟨0, b + 1, C, 0, E + 1⟩ [fm]⊢* ⟨0, b + E + 2, C + E + 1, 0, 0⟩ := by
  intro E; induction' E with E ih <;> intro b C
  · step fm; step fm; ring_nf; finish
  · step fm
    step fm
    rw [show b + 2 = (b + 1) + 1 from by ring]
    apply stepStar_trans (ih (b + 1) (C + 1))
    ring_nf; finish

-- R3 drains b to d.
-- (0, B, C, d, 0) ->* (0, 0, C, d+B, 0).
theorem b_to_d : ∀ B, ∀ C d, ⟨0, B, C, d, 0⟩ [fm]⊢* ⟨0, 0, C, d + B, 0⟩ := by
  intro B; induction' B with B ih <;> intro C d
  · exists 0
  · step fm
    apply stepStar_trans (ih C (d + 1))
    ring_nf; finish

-- R4 chain.
-- (a, 0, c+D, D, 0) ->* (a+D, 0, c, 0, 0).
theorem r4_chain : ∀ D, ∀ a c, ⟨a, 0, c + D, D, 0⟩ [fm]⊢* ⟨a + D, 0, c, 0, 0⟩ := by
  intro D; induction' D with D ih <;> intro a c
  · exists 0
  · rw [show c + (D + 1) = (c + D) + 1 from by ring]
    step fm
    apply stepStar_trans (ih (a + 1) c)
    ring_nf; finish

-- Main transition: (2*n+5, 0, c, 0, 0) ->+ (2*n+7, 0, c+n+1, 0, 0).
theorem main_trans : ⟨2 * n + 5, 0, c, 0, 0⟩ [fm]⊢⁺ ⟨2 * n + 7, 0, c + n + 1, 0, 0⟩ := by
  rw [show 2 * n + 5 = 2 * (n + 2) + 1 from by ring]
  step fm
  step fm
  apply stepStar_trans (r5r1_chain (n + 1) (c + 1) 2)
  rw [show c + 1 + (n + 1) = c + n + 2 from by ring,
      show 2 + 2 * (n + 1) + 2 = (2 * n + 5) + 1 from by ring]
  apply stepStar_trans (r3r2_chain (2 * n + 5) 0 (c + n + 2))
  rw [show 0 + (2 * n + 5) + 2 = 2 * n + 7 from by ring,
      show c + n + 2 + (2 * n + 5) + 1 = c + 3 * n + 8 from by ring]
  apply stepStar_trans (b_to_d (2 * n + 7) (c + 3 * n + 8) 0)
  rw [show 0 + (2 * n + 7) = 2 * n + 7 from by ring,
      show c + 3 * n + 8 = (c + n + 1) + (2 * n + 7) from by ring]
  apply stepStar_trans (r4_chain (2 * n + 7) 0 (c + n + 1))
  rw [show 0 + (2 * n + 7) = 2 * n + 7 from by ring]
  finish

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨5, 0, 0, 0, 0⟩) (by execute fm 42)
  apply progress_nonhalt_simple (fm := fm) (A := ℕ × ℕ)
    (fun ⟨n, c⟩ ↦ ⟨2 * n + 5, 0, c, 0, 0⟩) ⟨0, 0⟩
  intro ⟨n, c⟩; exact ⟨⟨n + 1, c + n + 1⟩, main_trans⟩

end Sz22_2003_unofficial_1169
