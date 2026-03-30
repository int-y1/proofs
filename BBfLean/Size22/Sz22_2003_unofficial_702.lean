import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #702: [35/6, 4/55, 121/2, 3/7, 18/11]

Vector representation:
```
-1 -1  1  1  0
 2  0 -1  0 -1
-1  0  0  0  2
 0  1  0 -1  0
 1  2  0  0 -1
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_702

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a+1, b+1, c, d, e⟩ => some ⟨a, b, c+1, d+1, e⟩
  | ⟨a, b, c+1, d, e+1⟩ => some ⟨a+2, b, c, d, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b, c, d, e+2⟩
  | ⟨a, b, c, d+1, e⟩ => some ⟨a, b+1, c, d, e⟩
  | ⟨a, b, c, d, e+1⟩ => some ⟨a+1, b+2, c, d, e⟩
  | _ => none

theorem r4_chain : ∀ k b d e, ⟨0, b, 0, d + k, e⟩ [fm]⊢* ⟨0, b + k, 0, d, e⟩ := by
  intro k; induction' k with k ih <;> intro b d e
  · exists 0
  · rw [show d + (k + 1) = (d + k) + 1 from by ring]
    step fm
    apply stepStar_trans (ih (b + 1) d e)
    ring_nf; finish

theorem r3_chain : ∀ k d e, ⟨k, 0, 0, d, e⟩ [fm]⊢* ⟨0, 0, 0, d, e + 2 * k⟩ := by
  intro k; induction' k with k ih <;> intro d e
  · exists 0
  · rw [show k + 1 = k + 1 from rfl]
    step fm
    apply stepStar_trans (ih d (e + 2))
    ring_nf; finish

theorem r2_drain : ∀ k a d e, ⟨a, 0, k, d, e + k⟩ [fm]⊢* ⟨a + 2 * k, 0, 0, d, e⟩ := by
  intro k; induction' k with k ih <;> intro a d e
  · exists 0
  · rw [show e + (k + 1) = (e + k) + 1 from by ring]
    step fm
    apply stepStar_trans (ih (a + 2) d e)
    ring_nf; finish

theorem r2r1r1_chain : ∀ k b c d e, ⟨0, b + 2 * k, c + 1, d, e + k⟩ [fm]⊢* ⟨0, b, c + k + 1, d + 2 * k, e⟩ := by
  intro k; induction' k with k ih <;> intro b c d e
  · exists 0
  · rw [show b + 2 * (k + 1) = (b + 2 * k) + 2 from by ring,
        show e + (k + 1) = (e + k) + 1 from by ring]
    step fm; step fm; step fm
    apply stepStar_trans (ih b (c + 1) (d + 2) e)
    ring_nf; finish

theorem main_trans (n : ℕ) :
    ⟨0, 0, 0, 2 * n + 2, n * n + 4 * n + 5⟩ [fm]⊢⁺
    ⟨0, 0, 0, 2 * n + 4, n * n + 6 * n + 10⟩ := by
  -- Phase 1: R4 chain (2n+2 steps)
  rw [show 2 * n + 2 = 0 + (2 * n + 2) from by ring]
  apply step_stepStar_stepPlus
  · show fm ⟨0, 0, 0, 0 + (2 * n + 2), n * n + 4 * n + 5⟩ =
         some ⟨0, 1, 0, 0 + (2 * n + 1), n * n + 4 * n + 5⟩
    simp [fm]
  apply stepStar_trans (r4_chain (2 * n + 1) 1 0 (n * n + 4 * n + 5))
  rw [show 1 + (2 * n + 1) = 2 * n + 2 from by ring]
  -- Phase 2: R5 (1 step)
  rw [show n * n + 4 * n + 5 = (n * n + 4 * n + 4) + 1 from by ring]
  step fm
  -- Phase 3: R1 (1 step)
  rw [show 2 * n + 2 + 2 = (2 * n + 3) + 1 from by ring]
  step fm
  -- Phase 4: r2r1r1_chain (n+1 rounds)
  rw [show 2 * n + 3 = 1 + 2 * (n + 1) from by ring,
      show n * n + 4 * n + 4 = (n * n + 3 * n + 3) + (n + 1) from by ring]
  apply stepStar_trans (r2r1r1_chain (n + 1) 1 0 1 (n * n + 3 * n + 3))
  rw [show 0 + (n + 1) + 1 = n + 2 from by ring,
      show 1 + 2 * (n + 1) = 2 * n + 3 from by ring]
  -- Phase 5: R2 + R1 (2 steps)
  rw [show n * n + 3 * n + 3 = (n * n + 3 * n + 2) + 1 from by ring]
  step fm
  step fm
  -- Phase 6: r2_drain (n+2 steps)
  rw [show 2 * n + 3 + 1 = 2 * n + 4 from by ring,
      show n * n + 3 * n + 2 = (n * n + 2 * n) + (n + 2) from by ring]
  apply stepStar_trans (r2_drain (n + 2) 1 (2 * n + 4) (n * n + 2 * n))
  rw [show 1 + 2 * (n + 2) = 2 * n + 5 from by ring]
  -- Phase 7: r3_chain (2n+5 steps)
  have h := r3_chain (2 * n + 5) (2 * n + 4) (n * n + 2 * n)
  convert h using 2; ring_nf

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨0, 0, 0, 2, 5⟩) (by execute fm 9)
  apply progress_nonhalt_simple (fm := fm) (A := ℕ)
    (fun n ↦ ⟨0, 0, 0, 2 * n + 2, n * n + 4 * n + 5⟩) 0
  intro n; refine ⟨n + 1, ?_⟩
  have h := main_trans n
  convert h using 2; ring_nf

end Sz22_2003_unofficial_702
