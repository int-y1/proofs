import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #107: [1/30, 49/3, 15/77, 4/7, 363/2]

Vector representation:
```
-1 -1 -1  0  0
 0 -1  0  2  0
 0  1  1 -1 -1
 2  0  0 -1  0
-1  1  0  0  2
```

This Fractran program doesn't halt. The canonical state is (1, 0, 0, 0, e) which
maps to (1, 0, 0, 0, 2*e+4), so e grows without bound.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_107

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a+1, b+1, c+1, d, e⟩ => some ⟨a, b, c, d, e⟩
  | ⟨a, b+1, c, d, e⟩ => some ⟨a, b, c, d+2, e⟩
  | ⟨a, b, c, d+1, e+1⟩ => some ⟨a, b+1, c+1, d, e⟩
  | ⟨a, b, c, d+1, e⟩ => some ⟨a+2, b, c, d, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b+1, c, d, e+2⟩
  | _ => none

-- R3+R2 loop: each pair does c+1, d+1, e-1
theorem r3r2_loop : ∀ k c d, ⟨0, 0, c, d + 1, k + 1⟩ [fm]⊢* ⟨0, 0, c + k + 1, d + k + 2, 0⟩ := by
  intro k; induction' k with k ih <;> intro c d
  · step fm; step fm; finish
  · step fm; step fm
    apply stepStar_trans (ih (c + 1) (d + 1))
    ring_nf; finish

-- R4 loop: convert d to a
theorem r4_loop : ∀ k a c, ⟨a, 0, c, k, 0⟩ [fm]⊢* ⟨a + 2 * k, 0, c, 0, 0⟩ := by
  intro k; induction' k with k ih <;> intro a c
  · exists 0
  · step fm
    apply stepStar_trans (ih _ c)
    ring_nf; finish

-- R5+R1 loop: each pair does a-2, c-1, e+2
theorem r5r1_loop : ∀ k a e, ⟨a + 2 * k + 2, 0, k, 0, e⟩ [fm]⊢* ⟨a + 2, 0, 0, 0, e + 2 * k⟩ := by
  intro k; induction' k with k ih <;> intro a e
  · exists 0
  · rw [show a + 2 * (k + 1) + 2 = (a + 2 * k + 2) + 1 + 1 from by ring]
    step fm; step fm
    apply stepStar_trans (ih a _)
    ring_nf; finish

-- Tail: (4, 0, 0, 0, E) →⁺ (1, 0, 0, 0, E)
theorem tail : ∀ E, ⟨4, 0, 0, 0, E⟩ [fm]⊢⁺ ⟨1, 0, 0, 0, E⟩ := by
  intro E; execute fm 6

-- Main transition: (1, 0, 0, 0, e) →⁺ (1, 0, 0, 0, 2*e+4)
theorem main_trans : ⟨1, 0, 0, 0, e⟩ [fm]⊢⁺ ⟨1, 0, 0, 0, 2 * e + 4⟩ := by
  step fm; step fm
  -- Goal: (0, 0, 0, 2, e+2) ⊢* (1, 0, 0, 0, 2*e+4)
  -- Phase 2: r3r2_loop with k=e+1, c=0, d=1
  rw [show (2 : ℕ) = 1 + 1 from rfl, show e + 2 = (e + 1) + 1 from by ring]
  apply stepStar_trans (r3r2_loop (e + 1) 0 1)
  ring_nf
  -- Phase 3: r4_loop
  apply stepStar_trans (r4_loop (4 + e) 0 (2 + e))
  ring_nf
  -- Phase 4: r5r1_loop with k=2+e, a=2, e'=0
  rw [show 8 + e * 2 = 2 + 2 * (2 + e) + 2 from by ring]
  apply stepStar_trans (r5r1_loop (2 + e) 2 0)
  ring_nf
  -- Phase 5: tail
  exact stepPlus_stepStar (tail _)

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨1, 0, 0, 0, 0⟩)
  · exists 0
  exact progress_nonhalt_simple (fun e : ℕ ↦ (⟨1, 0, 0, 0, e⟩ : Q)) 0
    (fun e ↦ ⟨2 * e + 4, main_trans⟩)

end Sz22_2003_unofficial_107
