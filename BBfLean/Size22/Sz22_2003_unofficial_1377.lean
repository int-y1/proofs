import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #1377: [63/10, 5/33, 2/3, 11/7, 105/2]

Vector representation:
```
-1  2 -1  1  0
 0 -1  1  0 -1
 1 -1  0  0  0
 0  0  0 -1  1
-1  1  1  1  0
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_1377

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a+1, b, c+1, d, e⟩ => some ⟨a, b+2, c, d+1, e⟩
  | ⟨a, b+1, c, d, e+1⟩ => some ⟨a, b, c+1, d, e⟩
  | ⟨a, b+1, c, d, e⟩ => some ⟨a+1, b, c, d, e⟩
  | ⟨a, b, c, d+1, e⟩ => some ⟨a, b, c, d, e+1⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b+1, c+1, d+1, e⟩
  | _ => none

-- R4 chain: transfer d to e (when b=0, c=0).
theorem d_to_e : ∀ k, ∀ d e, ⟨a, 0, 0, d + k, e⟩ [fm]⊢* ⟨a, 0, 0, d, e + k⟩ := by
  intro k; induction' k with k ih <;> intro d e
  · exists 0
  · rw [show d + (k + 1) = (d + k) + 1 from by ring]
    step fm
    apply stepStar_trans (ih d (e + 1)); ring_nf; finish

-- R1+R2 interleave: from (a+1, b, 1, d, e+a) to (0, b+a+2, 0, d+a+1, e).
theorem r1r2_interleave : ∀ a, ∀ b d e, ⟨a + 1, b, 1, d, e + a⟩ [fm]⊢* ⟨0, b + a + 2, 0, d + a + 1, e⟩ := by
  intro a; induction' a with a ih <;> intro b d e
  · step fm; ring_nf; finish
  · rw [show e + (a + 1) = (e + a) + 1 from by ring,
        show (a + 1) + 1 = (a + 1) + 1 from rfl]
    step fm; step fm
    apply stepStar_trans (ih (b + 1) (d + 1) e); ring_nf; finish

-- R2 drain: from (0, b+k, c, d, k) to (0, b, c+k, d, 0).
theorem r2_drain : ∀ k, ∀ b c d, ⟨0, b + k, c, d, k⟩ [fm]⊢* ⟨0, b, c + k, d, 0⟩ := by
  intro k; induction' k with k ih <;> intro b c d
  · exists 0
  · rw [show b + (k + 1) = (b + k) + 1 from by ring,
        show (k + 1) = k + 1 from rfl]
    step fm
    apply stepStar_trans (ih b (c + 1) d); ring_nf; finish

-- R3 drain: from (a, k, 0, d, 0) to (a+k, 0, 0, d, 0).
theorem r3_drain : ∀ k, ∀ a d, ⟨a, k, 0, d, 0⟩ [fm]⊢* ⟨a + k, 0, 0, d, 0⟩ := by
  intro k; induction' k with k ih <;> intro a d
  · exists 0
  · step fm
    apply stepStar_trans (ih (a + 1) d); ring_nf; finish

-- R1+R3 chain: from (1, b, k, d, 0) to (1, b+k, 0, d+k, 0).
theorem r1r3_chain : ∀ k, ∀ b d, ⟨1, b, k, d, 0⟩ [fm]⊢* ⟨1, b + k, 0, d + k, 0⟩ := by
  intro k; induction' k with k ih <;> intro b d
  · exists 0
  · rw [show (k + 1) = k + 1 from rfl]
    step fm; step fm
    apply stepStar_trans (ih (b + 1) (d + 1)); ring_nf; finish

-- Main transition: (n+2, 0, 0, 2n+2, 0) ⊢⁺ (n+3, 0, 0, 2n+4, 0).
theorem main_trans (n : ℕ) :
    ⟨n + 2, 0, 0, 2 * n + 2, 0⟩ [fm]⊢⁺ ⟨n + 3, 0, 0, 2 * n + 4, 0⟩ := by
  -- Phase 1: d_to_e
  rw [show 2 * n + 2 = 0 + (2 * n + 2) from by ring]
  apply stepStar_stepPlus_stepPlus (d_to_e (2 * n + 2) 0 0)
  rw [show 0 + (2 * n + 2) = 2 * n + 2 from by ring]
  -- Phase 2: R5
  rw [show n + 2 = (n + 1) + 1 from by ring]
  apply step_stepStar_stepPlus (by unfold fm; rfl)
  -- Phase 3: r1r2_interleave
  rw [show (2 * n + 1).succ = (n + 2) + n from by omega,
      show (0 : ℕ) + 1 = 1 from by ring]
  apply stepStar_trans (r1r2_interleave n 1 1 (n + 2))
  -- Phase 4: R2 drain
  rw [show 1 + n + 2 = 1 + (n + 2) from by ring,
      show 1 + n + 1 = n + 2 from by ring]
  apply stepStar_trans (r2_drain (n + 2) 1 0 (n + 2))
  -- Phase 5: R3 (one step, b=1)
  rw [show 0 + (n + 2) = n + 2 from by ring]
  step fm
  -- Phase 6: r1r3_chain
  apply stepStar_trans (r1r3_chain (n + 2) 0 (n + 2))
  -- Phase 7: r3_drain
  rw [show 0 + (n + 2) = n + 2 from by ring,
      show (n + 2) + (n + 2) = 2 * n + 4 from by ring]
  apply stepStar_trans (r3_drain (n + 2) 1 (2 * n + 4))
  rw [show 1 + (n + 2) = n + 3 from by ring]
  finish

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨2, 0, 0, 2, 0⟩)
  · execute fm 5
  apply progress_nonhalt_simple (fm := fm) (A := ℕ)
    (fun n ↦ ⟨n + 2, 0, 0, 2 * n + 2, 0⟩) 0
  intro n; exact ⟨n + 1, main_trans n⟩

end Sz22_2003_unofficial_1377
