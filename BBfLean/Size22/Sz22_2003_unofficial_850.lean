import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #850: [36/35, 5/22, 49/2, 11/3, 6/7]

Vector representation:
```
 2  2 -1 -1  0
-1  0  1  0 -1
-1  0  0  2  0
 0 -1  0  0  1
 1  1  0 -1  0
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_850

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a, b, c+1, d+1, e⟩ => some ⟨a+2, b+2, c, d, e⟩
  | ⟨a+1, b, c, d, e+1⟩ => some ⟨a, b, c+1, d, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b, c, d+2, e⟩
  | ⟨a, b+1, c, d, e⟩ => some ⟨a, b, c, d, e+1⟩
  | ⟨a, b, c, d+1, e⟩ => some ⟨a+1, b+1, c, d, e⟩
  | _ => none

-- R2+R1 loop: (a+1, b, 0, d+k, k) →* (a+k+1, b+2*k, 0, d, 0)
theorem r2r1_loop : ∀ k, ⟨a + 1, b, 0, d + k, k⟩ [fm]⊢* ⟨a + k + 1, b + 2 * k, 0, d, 0⟩ := by
  intro k; induction' k with k ih generalizing a b d
  · exists 0
  · rw [show d + (k + 1) = d + k + 1 from by ring]
    step fm -- R2: (a, b, 1, d+k+1, k)
    step fm -- R1: (a+2, b+2, 0, d+k, k)
    rw [show a + 2 = (a + 1) + 1 from by ring,
        show b + 2 = b + 2 from rfl]
    apply stepStar_trans (ih (a := a + 1) (b := b + 2) (d := d))
    ring_nf; finish

-- R3 loop: (a+k, b, 0, d, 0) →* (a, b, 0, d+2*k, 0)
theorem r3_loop : ∀ k, ⟨a + k, b, 0, d, 0⟩ [fm]⊢* ⟨a, b, 0, d + 2 * k, 0⟩ := by
  intro k; induction' k with k ih generalizing a d
  · exists 0
  · rw [show a + (k + 1) = (a + k) + 1 from by ring]
    step fm -- R3: (a+k, b, 0, d+2, 0)
    apply stepStar_trans (ih (a := a) (d := d + 2))
    ring_nf; finish

-- R4 loop: (0, b+k, 0, d, e) →* (0, b, 0, d, e+k)
theorem r4_loop : ∀ k, ⟨0, b + k, 0, d, e⟩ [fm]⊢* ⟨0, b, 0, d, e + k⟩ := by
  intro k; induction' k with k ih generalizing b e
  · exists 0
  · rw [show b + (k + 1) = (b + k) + 1 from by ring]
    step fm -- R4: (0, b+k, 0, d, e+1)
    apply stepStar_trans (ih (b := b) (e := e + 1))
    ring_nf; finish

-- Main transition: (0, 0, 0, e+2, e) →⁺ (0, 0, 0, 2*e+3, 2*e+1)
-- Phase 1: R5
-- Phase 2: R2+R1 loop (e rounds)
-- Phase 3: R3 loop (e+1 rounds)
-- Phase 4: R4 loop (2*e+1 rounds)
theorem main_trans : ⟨0, 0, 0, e + 2, e⟩ [fm]⊢⁺ ⟨0, 0, 0, 2 * e + 3, 2 * e + 1⟩ := by
  -- R5: (0, 0, 0, e+2, e) → (1, 1, 0, e+1, e)
  rw [show e + 2 = (e + 1) + 1 from by ring]
  step fm
  -- Now at (1, 1, 0, e+1, e). Apply R2+R1 loop with a=0, b=1, d=1, k=e.
  rw [show (1 : ℕ) = 0 + 1 from by ring,
      show e + 1 = 1 + e from by ring]
  apply stepStar_trans (r2r1_loop e (a := 0) (b := 1) (d := 1))
  rw [show 0 + e + 1 = 0 + (e + 1) from by ring,
      show 1 + 2 * e = 2 * e + 1 from by ring]
  apply stepStar_trans (r3_loop (e + 1) (a := 0) (b := 2 * e + 1) (d := 1))
  rw [show 1 + 2 * (e + 1) = 2 * e + 3 from by ring,
      show (2 * e + 1 : ℕ) = 0 + (2 * e + 1) from by ring]
  apply stepStar_trans (r4_loop (2 * e + 1) (b := 0) (d := 2 * e + 3) (e := 0))
  ring_nf; finish

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨0, 0, 0, 3, 1⟩) (by execute fm 4)
  apply progress_nonhalt_simple (fm := fm) (A := ℕ)
    (fun n ↦ ⟨0, 0, 0, n + 2, n⟩) 1
  intro n; exists 2 * n + 1
  show ⟨0, 0, 0, n + 2, n⟩ [fm]⊢⁺ ⟨0, 0, 0, (2 * n + 1) + 2, 2 * n + 1⟩
  rw [show (2 * n + 1) + 2 = 2 * n + 3 from by ring]
  exact main_trans

end Sz22_2003_unofficial_850
