import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #527: [28/15, 363/2, 1/3, 5/11, 1/35, 3/5]

Vector representation:
```
 2 -1 -1  1  0
-1  1  0  0  2
 0 -1  0  0  0
 0  0  1  0 -1
 0  0 -1 -1  0
 0  1 -1  0  0
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_527

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a, b+1, c+1, d, e⟩ => some ⟨a+2, b, c, d+1, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b+1, c, d, e+2⟩
  | ⟨a, b+1, c, d, e⟩ => some ⟨a, b, c, d, e⟩
  | ⟨a, b, c, d, e+1⟩ => some ⟨a, b, c+1, d, e⟩
  | ⟨a, b, c+1, d+1, e⟩ => some ⟨a, b, c, d, e⟩
  | ⟨a, b, c+1, d, e⟩ => some ⟨a, b+1, c, d, e⟩
  | _ => none

-- R1/R2 interleaved chain
theorem r1r2_chain : ∀ k, ∀ a d e, ⟨a, 1, k+1, d, e⟩ [fm]⊢* ⟨a+k+2, 0, 0, d+k+1, e+2*k⟩ := by
  intro k; induction' k with k ih <;> intro a d e
  · step fm; ring_nf; finish
  · rw [show k + 1 + 1 = (k + 1) + 1 from by omega]
    step fm; step fm
    apply stepStar_trans (ih _ _ _)
    ring_nf; finish

-- R2 drain with accumulating b
theorem r2_drain : ∀ a, ∀ b d e, ⟨a, b, 0, d, e⟩ [fm]⊢* ⟨0, a+b, 0, d, e+2*a⟩ := by
  intro a; induction' a with a ih <;> intro b d e
  · ring_nf; finish
  · step fm
    apply stepStar_trans (ih _ _ _)
    ring_nf; finish

-- R3 drain
theorem r3_drain : ∀ b, ∀ d e, ⟨0, b, 0, d, e⟩ [fm]⊢* ⟨0, 0, 0, d, e⟩ := by
  intro b; induction' b with b ih <;> intro d e
  · exists 0
  · step fm; exact ih _ _

-- R4 transfer e to c
theorem r4_transfer : ∀ e, ∀ c d, ⟨0, 0, c, d, e⟩ [fm]⊢* ⟨0, 0, c+e, d, 0⟩ := by
  intro e; induction' e with e ih <;> intro c d
  · ring_nf; finish
  · step fm
    apply stepStar_trans (ih _ _)
    ring_nf; finish

-- R5 annihilate c and d
theorem r5_annihilate : ∀ d, ∀ c, ⟨0, 0, c+d, d, 0⟩ [fm]⊢* ⟨0, 0, c, 0, 0⟩ := by
  intro d; induction' d with d ih <;> intro c
  · exists 0
  · rw [show c + (d + 1) = (c + d) + 1 from by omega]
    step fm
    exact ih _

-- Main transition: (0, 0, n+2, 0, 0) ->+ (0, 0, 3*n+3, 0, 0)
theorem main_trans (n : ℕ) : ⟨0, 0, n+2, 0, 0⟩ [fm]⊢⁺ ⟨0, 0, 3*n+3, 0, 0⟩ := by
  -- Phase 1: R6 gives (0, 1, n+1, 0, 0)
  rw [show n + 2 = (n + 1) + 1 from by omega]
  step fm
  -- Phase 2: R1/R2 chain
  apply stepStar_trans (r1r2_chain n 0 0 0)
  -- Now at (n+2, 0, 0, n+1, 2*n)
  -- Phase 3: R2 drain
  apply stepStar_trans (r2_drain (0 + n + 2) 0 (0 + n + 1) (0 + 2 * n))
  -- Phase 4: R3 drain
  apply stepStar_trans (r3_drain _ _ _)
  -- Phase 5: R4 transfer
  apply stepStar_trans (r4_transfer _ _ _)
  -- Phase 6: R5 annihilate
  rw [show 0 + (0 + 2 * n + 2 * (0 + n + 2)) = (3 * n + 3) + (0 + n + 1) from by ring]
  apply r5_annihilate

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨0, 0, 2, 0, 0⟩) (by execute fm 4)
  apply progress_nonhalt_simple (fm := fm) (A := ℕ)
    (fun n ↦ ⟨0, 0, n + 2, 0, 0⟩) 0
  intro n; exact ⟨3 * n + 1, by
    rw [show 3 * n + 1 + 2 = 3 * n + 3 from by omega]; exact main_trans n⟩

end Sz22_2003_unofficial_527
