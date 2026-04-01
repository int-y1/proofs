import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #1582: [7/45, 5324/5, 5/77, 3/11, 5/2]

Vector representation:
```
 0 -2 -1  1  0
 2  0 -1  0  3
 0  0  1 -1 -1
 0  1  0  0 -1
-1  0  1  0  0
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_1582

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a, b+2, c+1, d, e⟩ => some ⟨a, b, c, d+1, e⟩
  | ⟨a, b, c+1, d, e⟩ => some ⟨a+2, b, c, d, e+3⟩
  | ⟨a, b, c, d+1, e+1⟩ => some ⟨a, b, c+1, d, e⟩
  | ⟨a, b, c, d, e+1⟩ => some ⟨a, b+1, c, d, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b, c+1, d, e⟩
  | _ => none

-- R3R2 chain (b=0): drains d while e >= 1
theorem r3r2_b0 : ∀ k, ⟨a, 0, 0, k, e + 1⟩ [fm]⊢* ⟨a + 2 * k, 0, 0, 0, e + 2 * k + 1⟩ := by
  intro k; induction' k with k ih generalizing a e
  · exists 0
  · rw [show k + 1 = k + 1 from rfl]
    step fm; step fm
    apply stepStar_trans (ih (a := a + 2) (e := e + 2))
    ring_nf; finish

-- R3R2 chain (b=1)
theorem r3r2_b1 : ∀ k, ⟨a, 1, 0, k, e + 1⟩ [fm]⊢* ⟨a + 2 * k, 1, 0, 0, e + 2 * k + 1⟩ := by
  intro k; induction' k with k ih generalizing a e
  · exists 0
  · step fm; step fm
    apply stepStar_trans (ih (a := a + 2) (e := e + 2))
    ring_nf; finish

-- R4 drain: transfers e to b
theorem r4_drain : ∀ k, ⟨a, b, 0, 0, k⟩ [fm]⊢* ⟨a, b + k, 0, 0, 0⟩ := by
  intro k; induction' k with k ih generalizing b
  · exists 0
  · step fm
    apply stepStar_trans (ih (b := b + 1))
    ring_nf; finish

-- R5R1 chain: a -= 1, b -= 2, d += 1 per round
theorem r5r1_chain : ∀ k, ⟨a + k, b + 2 * k, 0, d, 0⟩ [fm]⊢* ⟨a, b, 0, d + k, 0⟩ := by
  intro k; induction' k with k ih generalizing a b d
  · exists 0
  · rw [show a + (k + 1) = (a + k) + 1 from by ring,
        show b + 2 * (k + 1) = (b + 2 * k) + 2 from by ring]
    step fm; step fm
    apply stepStar_trans (ih (a := a) (b := b) (d := d + 1))
    ring_nf; finish

-- Main transition: (a+1, 0, 0, d, 0) ⊢⁺ (a+2*d+1, 0, 0, d+3, 0)
theorem main_trans (a d : ℕ) :
    ⟨a + 1, 0, 0, d, 0⟩ [fm]⊢⁺ ⟨a + 2 * d + 1, 0, 0, d + 3, 0⟩ := by
  -- Phase 1: R5, R2: -> (a+2, 0, 0, d, 3)
  step fm; step fm
  -- Phase 2: R3R2 chain (d rounds, b=0): -> (a+2d+2, 0, 0, 0, 2d+3)
  rw [show (3 : ℕ) = 2 + 1 from rfl]
  apply stepStar_trans (r3r2_b0 d (a := a + 2) (e := 2))
  -- Phase 3: R4 drain: -> (a+2d+2, 2d+3, 0, 0, 0)
  rw [show 2 + 2 * d + 1 = 2 * d + 3 from by ring]
  apply stepStar_trans (r4_drain (2 * d + 3) (a := a + 2 + 2 * d) (b := 0))
  -- Phase 4: R5R1 chain (d+1 rounds): -> (a+d+1, 1, 0, d+1, 0)
  rw [show a + 2 + 2 * d = (a + d + 1) + (d + 1) from by ring,
      show 0 + (2 * d + 3) = 1 + 2 * (d + 1) from by ring]
  apply stepStar_trans (r5r1_chain (d + 1) (a := a + d + 1) (b := 1) (d := 0))
  rw [show 0 + (d + 1) = d + 1 from by ring]
  -- Phase 5: R5, R2: -> (a+d+2, 1, 0, d+1, 3)
  rw [show a + d + 1 = (a + d) + 1 from by ring]
  step fm; step fm
  -- Phase 6: R3R2 chain (d+1 rounds, b=1): -> (a+3d+4, 1, 0, 0, 2d+5)
  rw [show (3 : ℕ) = 2 + 1 from rfl]
  apply stepStar_trans (r3r2_b1 (d + 1) (a := a + d + 2) (e := 2))
  -- Phase 7: R4 drain: -> (a+3d+4, 2d+6, 0, 0, 0)
  rw [show 2 + 2 * (d + 1) + 1 = 2 * d + 5 from by ring]
  apply stepStar_trans (r4_drain (2 * d + 5) (a := a + d + 2 + 2 * (d + 1)) (b := 1))
  -- Phase 8: R5R1 chain (d+3 rounds): -> (a+2d+1, 0, 0, d+3, 0)
  rw [show a + d + 2 + 2 * (d + 1) = (a + 2 * d + 1) + (d + 3) from by ring,
      show 1 + (2 * d + 5) = 0 + 2 * (d + 3) from by ring]
  apply stepStar_trans (r5r1_chain (d + 3) (a := a + 2 * d + 1) (b := 0) (d := 0))
  ring_nf; finish

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨1, 0, 0, 3, 0⟩) (by execute fm 22)
  apply progress_nonhalt_simple (fm := fm) (A := ℕ × ℕ)
    (fun ⟨a, d⟩ ↦ ⟨a + 1, 0, 0, d, 0⟩) ⟨0, 3⟩
  intro ⟨a, d⟩
  exact ⟨⟨a + 2 * d, d + 3⟩, main_trans a d⟩

end Sz22_2003_unofficial_1582
