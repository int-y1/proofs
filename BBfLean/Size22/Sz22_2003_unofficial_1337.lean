import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #1337: [63/10, 2/33, 1573/2, 5/7, 14/13]

Vector representation:
```
-1  2 -1  1  0  0
 1 -1  0  0 -1  0
-1  0  0  0  2  1
 0  0  1 -1  0  0
 1  0  0  1  0 -1
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_1337

def Q := ℕ × ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a+1, b, c+1, d, e, f⟩ => some ⟨a, b+2, c, d+1, e, f⟩
  | ⟨a, b+1, c, d, e+1, f⟩ => some ⟨a+1, b, c, d, e, f⟩
  | ⟨a+1, b, c, d, e, f⟩ => some ⟨a, b, c, d, e+2, f+1⟩
  | ⟨a, b, c, d+1, e, f⟩ => some ⟨a, b, c+1, d, e, f⟩
  | ⟨a, b, c, d, e, f+1⟩ => some ⟨a+1, b, c, d+1, e, f⟩
  | _ => none

theorem r3_chain : ∀ k, ⟨a + k, 0, 0, d, e, f⟩ [fm]⊢* ⟨a, 0, 0, d, e + 2 * k, f + k⟩ := by
  intro k; induction' k with k ih generalizing a d e f
  · exists 0
  · rw [show a + (k + 1) = (a + k) + 1 from by ring]
    step fm
    apply stepStar_trans (ih (e := e + 2) (f := f + 1))
    ring_nf; finish

theorem r4_chain : ∀ k, ⟨0, 0, c, d + k, e, f⟩ [fm]⊢* ⟨0, 0, c + k, d, e, f⟩ := by
  intro k; induction' k with k ih generalizing c d e f
  · exists 0
  · rw [show d + (k + 1) = (d + k) + 1 from by ring]
    step fm
    apply stepStar_trans (ih (c := c + 1))
    ring_nf; finish

theorem r2_drain : ∀ k, ⟨a, b + k, 0, d, e + k, f⟩ [fm]⊢* ⟨a + k, b, 0, d, e, f⟩ := by
  intro k; induction' k with k ih generalizing a b d e f
  · exists 0
  · rw [show b + (k + 1) = (b + k) + 1 from by ring,
        show e + (k + 1) = (e + k) + 1 from by ring]
    step fm
    apply stepStar_trans (ih (a := a + 1))
    ring_nf; finish

theorem r1r2_spiral : ∀ k, ⟨1, b, k, d, e + k, f⟩ [fm]⊢* ⟨1, b + k, 0, d + k, e, f⟩ := by
  intro k; induction' k with k ih generalizing b d e f
  · exists 0
  · rw [show e + (k + 1) = (e + k) + 1 from by ring]
    step fm
    step fm
    apply stepStar_trans (ih (b := b + 1) (d := d + 1))
    ring_nf; finish

theorem main_trans : ⟨0, 0, 0, d + 2, 2 * (d + 3), F + 1⟩ [fm]⊢⁺ ⟨0, 0, 0, d + 3, 2 * (d + 4), F + d + 3⟩ := by
  -- Phase 1: R4 chain (d+2 steps)
  rw [show (d + 2 : ℕ) = 0 + (d + 2) from by ring]
  apply stepStar_stepPlus_stepPlus (r4_chain (d + 2) (c := 0) (d := 0) (e := 2 * (d + 3)) (f := F + 1))
  -- State: (0, 0, 0+(d+2), 0, 2*(d+3), F+1) ⊢⁺ target
  -- Phase 2: R5 step
  apply step_stepStar_stepPlus (c₂ := ⟨0 + 1, 0, 0 + (d + 2), 0 + 1, 2 * (d + 3), F⟩)
  · show fm (0, 0, 0 + (d + 2), 0, 2 * (d + 3), F + 1) =
        some (0 + 1, 0, 0 + (d + 2), 0 + 1, 2 * (d + 3), F)
    unfold fm; rfl
  -- State: (0+1, 0, 0+(d+2), 0+1, 2*(d+3), F) ⊢* target
  -- Normalize and prepare for spiral
  simp only [Nat.zero_add]
  -- State: (1, 0, d+2, 1, 2*(d+3), F) ⊢* target
  rw [show 2 * (d + 3) = (d + 4) + (d + 2) from by ring]
  -- Phase 3: spiral (d+2 rounds)
  apply stepStar_trans (r1r2_spiral (d + 2) (b := 0) (d := 1) (e := d + 4) (f := F))
  -- State: (1, 0+(d+2), 0, 1+(d+2), d+4, F) ⊢* target
  -- Phase 4: drain with k = d+2.
  -- Need d+4 expressed as 2 + (d+2). This rewrites target too.
  rw [show (d + 4 : ℕ) = 2 + (d + 2) from by ring]
  apply stepStar_trans (r2_drain (d + 2) (a := 1) (b := 0) (d := 1 + (d + 2)) (e := 2) (f := F))
  -- State: (1+(d+2), 0, 0, 1+(d+2), 2, F) ⊢* (0,0,0,d+3, 2*(2+(d+2)), F+d+3)
  -- Phase 5: R3 chain (d+3 steps)
  rw [show 1 + (d + 2) = 0 + (d + 3) from by ring]
  apply stepStar_trans (r3_chain (d + 3) (a := 0) (d := 0 + (d + 3)) (e := 2) (f := F))
  rw [show 2 + 2 * (d + 3) = 2 * (2 + (d + 2)) from by ring,
      show (0 : ℕ) + (d + 3) = d + 3 from by ring,
      show F + (d + 3) = F + d + 3 from by ring]
  finish

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨0, 0, 0, 2, 6, 2⟩)
  · execute fm 10
  apply progress_nonhalt_simple (fm := fm) (A := ℕ × ℕ)
    (fun ⟨d, F⟩ ↦ ⟨0, 0, 0, d + 2, 2 * (d + 3), F + 1⟩) ⟨0, 1⟩
  intro ⟨d, F⟩
  exact ⟨⟨d + 1, F + d + 2⟩, main_trans⟩

end Sz22_2003_unofficial_1337
