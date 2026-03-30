import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #873: [4/15, 1/154, 147/2, 11/3, 50/11]

Vector representation:
```
 2 -1 -1  0  0
-1  0  0 -1 -1
-1  1  0  2  0
 0 -1  0  0  1
 1  0  2  0 -1
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_873

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a, b+1, c+1, d, e⟩ => some ⟨a+2, b, c, d, e⟩
  | ⟨a+1, b, c, d+1, e+1⟩ => some ⟨a, b, c, d, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b+1, c, d+2, e⟩
  | ⟨a, b+1, c, d, e⟩ => some ⟨a, b, c, d, e+1⟩
  | ⟨a, b, c, d, e+1⟩ => some ⟨a+1, b, c+2, d, e⟩
  | _ => none

-- R3 chain: (a+k, b, 0, d, 0) →* (a, b+k, 0, d+2*k, 0)
theorem a_to_b : ∀ k b d, ⟨a + k, b, 0, d, 0⟩ [fm]⊢* ⟨a, b + k, 0, d + 2 * k, 0⟩ := by
  intro k; induction' k with k ih <;> intro b d
  · exists 0
  · rw [show a + (k + 1) = (a + k) + 1 from by ring]
    step fm
    apply stepStar_trans (ih (b + 1) (d + 2))
    ring_nf; finish

-- R4 chain: (0, b+k, 0, d, e) →* (0, b, 0, d, e+k)
theorem b_to_e : ∀ k d e, ⟨0, b + k, 0, d, e⟩ [fm]⊢* ⟨0, b, 0, d, e + k⟩ := by
  intro k; induction' k with k ih <;> intro d e
  · exists 0
  · rw [show b + (k + 1) = (b + k) + 1 from by ring]
    step fm
    apply stepStar_trans (ih d (e + 1))
    ring_nf; finish

-- R5/R2 interleaved: (0, 0, c, d+k, 2*k+1) →* (1, 0, c+2*k+2, d, 0)
theorem r5r2_chain : ∀ k c d, ⟨0, 0, c, d + k, 2 * k + 1⟩ [fm]⊢* ⟨1, 0, c + 2 * k + 2, d, 0⟩ := by
  intro k; induction' k with k ih <;> intro c d
  · step fm; finish
  · rw [show d + (k + 1) = (d + k) + 1 from by ring,
        show 2 * (k + 1) + 1 = (2 * k + 1) + 1 + 1 from by ring]
    step fm
    step fm
    apply stepStar_trans (ih (c + 2) d)
    ring_nf; finish

-- R3/R1 interleaved: (a+1, 0, k, d, 0) →* (a+1+k, 0, 0, d+2*k, 0)
theorem r3r1_chain : ∀ k a d, ⟨a + 1, 0, k, d, 0⟩ [fm]⊢* ⟨a + 1 + k, 0, 0, d + 2 * k, 0⟩ := by
  intro k; induction' k with k ih <;> intro a d
  · exists 0
  · step fm
    step fm
    rw [show a + 2 = (a + 1) + 1 from by ring]
    apply stepStar_trans (ih (a + 1) (d + 2))
    ring_nf; finish

-- Main transition: (2n+1, 0, 0, D, 0) →⁺ (2n+3, 0, 0, D+7n+6, 0)
theorem main_trans (n D : ℕ) : ⟨2 * n + 1, 0, 0, D, 0⟩ [fm]⊢⁺ ⟨2 * n + 3, 0, 0, D + 7 * n + 6, 0⟩ := by
  -- Phase 1: R3 chain
  apply step_stepStar_stepPlus
  · show fm ⟨2 * n + 1, 0, 0, D, 0⟩ = some ⟨2 * n, 1, 0, D + 2, 0⟩
    simp [fm]
  apply stepStar_trans
  · show ⟨2 * n, 1, 0, D + 2, 0⟩ [fm]⊢* ⟨0, 2 * n + 1, 0, D + 4 * n + 2, 0⟩
    rw [show 2 * n = 0 + 2 * n from by ring]
    have := a_to_b (2 * n) (1) (D + 2) (a := 0)
    convert this using 1; ring_nf
  -- Phase 2: R4 chain
  apply stepStar_trans
  · show ⟨0, 2 * n + 1, 0, D + 4 * n + 2, 0⟩ [fm]⊢* ⟨0, 0, 0, D + 4 * n + 2, 2 * n + 1⟩
    rw [show 2 * n + 1 = 0 + (2 * n + 1) from by ring]
    have := b_to_e (2 * n + 1) (D + 4 * n + 2) 0 (b := 0)
    convert this using 1
  -- Phase 3: R5/R2 chain
  apply stepStar_trans
  · show ⟨0, 0, 0, D + 4 * n + 2, 2 * n + 1⟩ [fm]⊢* ⟨1, 0, 2 * n + 2, D + 3 * n + 2, 0⟩
    have := r5r2_chain n 0 (D + 3 * n + 2)
    convert this using 1; ring_nf
  -- Phase 4: R3/R1 chain
  show ⟨1, 0, 2 * n + 2, D + 3 * n + 2, 0⟩ [fm]⊢* ⟨2 * n + 3, 0, 0, D + 7 * n + 6, 0⟩
  rw [show (1 : ℕ) = 0 + 1 from by ring]
  have := r3r1_chain (2 * n + 2) 0 (D + 3 * n + 2)
  convert this using 1; ring_nf

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨3, 0, 0, 6, 0⟩)
  · execute fm 7
  apply progress_nonhalt_simple (fm := fm) (A := ℕ × ℕ)
    (fun ⟨n, D⟩ ↦ ⟨2 * n + 1, 0, 0, D, 0⟩) ⟨1, 6⟩
  intro ⟨n, D⟩
  exact ⟨⟨n + 1, D + 7 * n + 6⟩, main_trans n D⟩

end Sz22_2003_unofficial_873
