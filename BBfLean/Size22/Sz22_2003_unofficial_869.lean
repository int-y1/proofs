import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #869: [4/105, 55/6, 77/2, 3/11, 4/7]

Vector representation:
```
 2 -1 -1 -1  0
-1 -1  1  0  1
-1  0  0  1  1
 0  1  0  0 -1
 2  0  0 -1  0
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_869

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a, b+1, c+1, d+1, e⟩ => some ⟨a+2, b, c, d, e⟩
  | ⟨a+1, b+1, c, d, e⟩ => some ⟨a, b, c+1, d, e+1⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b, c, d+1, e+1⟩
  | ⟨a, b, c, d, e+1⟩ => some ⟨a, b+1, c, d, e⟩
  | ⟨a, b, c, d+1, e⟩ => some ⟨a+2, b, c, d, e⟩
  | _ => none

-- R4 repeated: move e to b.
theorem e_to_b : ∀ k, ⟨0, b, 0, d, e + k⟩ [fm]⊢* ⟨0, b + k, 0, d, e⟩ := by
  intro k; induction' k with k ih generalizing b e
  · exists 0
  · rw [show e + (k + 1) = (e + k) + 1 from by ring]
    step fm
    apply stepStar_trans (ih (b := b + 1))
    exists 0; show some _ = some _; congr 1; unfold Q; simp [Prod.ext_iff]; omega

-- R2+R1 interleaved chain.
theorem r2r1_chain : ∀ k, ⟨a + 1, b + 2 * k, 0, d + k, e⟩ [fm]⊢* ⟨a + k + 1, b, 0, d, e + k⟩ := by
  intro k; induction' k with k ih generalizing a b d e
  · exists 0
  · rw [show b + 2 * (k + 1) = (b + 2 * k) + 2 from by ring,
        show d + (k + 1) = (d + k) + 1 from by ring]
    step fm
    step fm
    apply stepStar_trans (ih (a := a + 1) (e := e + 1))
    exists 0; show some _ = some _; congr 1; unfold Q; simp [Prod.ext_iff]; omega

-- R3 repeated with c=1.
theorem r3_chain_c1 : ∀ k, ⟨a + k, 0, 1, d, e⟩ [fm]⊢* ⟨a, 0, 1, d + k, e + k⟩ := by
  intro k; induction' k with k ih generalizing a d e
  · exists 0
  · rw [show a + (k + 1) = (a + k) + 1 from by ring]
    step fm
    apply stepStar_trans (ih (d := d + 1) (e := e + 1))
    exists 0; show some _ = some _; congr 1; unfold Q; simp [Prod.ext_iff]; omega

-- R3 repeated with c=0.
theorem r3_chain : ∀ k, ⟨a + k, 0, 0, d, e⟩ [fm]⊢* ⟨a, 0, 0, d + k, e + k⟩ := by
  intro k; induction' k with k ih generalizing a d e
  · exists 0
  · rw [show a + (k + 1) = (a + k) + 1 from by ring]
    step fm
    apply stepStar_trans (ih (d := d + 1) (e := e + 1))
    exists 0; show some _ = some _; congr 1; unfold Q; simp [Prod.ext_iff]; omega

-- Main transition: (0, 0, 0, n+1, 2*n+1) ->+ (0, 0, 0, n+2, 2*n+3).
theorem main_trans (n : ℕ) : ⟨0, 0, 0, n + 1, 2 * n + 1⟩ [fm]⊢⁺ ⟨0, 0, 0, n + 2, 2 * n + 3⟩ := by
  -- Phase 1: e_to_b. (0, 0, 0, n+1, 2*n+1) ->* (0, 2*n+1, 0, n+1, 0).
  have h1 : ⟨0, 0, 0, n + 1, 2 * n + 1⟩ [fm]⊢* ⟨0, 2 * n + 1, 0, n + 1, 0⟩ := by
    rw [show (2 * n + 1 : ℕ) = 0 + (2 * n + 1) from by ring]
    apply stepStar_trans (e_to_b (2 * n + 1) (b := 0) (d := n + 1) (e := 0))
    finish
  -- Phase 2: R5. (0, 2*n+1, 0, n+1, 0) -> (2, 2*n+1, 0, n, 0).
  have h2 : (⟨0, 2 * n + 1, 0, n + 1, 0⟩ : Q) [fm]⊢ ⟨2, 2 * n + 1, 0, n, 0⟩ := by
    simp [fm]
  -- Phase 3: r2r1_chain, n rounds. (2, 2*n+1, 0, n, 0) ->* (n+2, 1, 0, 0, n).
  have h3 : ⟨2, 2 * n + 1, 0, n, 0⟩ [fm]⊢* ⟨n + 2, 1, 0, 0, n⟩ := by
    have := r2r1_chain n (a := 1) (b := 1) (d := 0) (e := 0)
    convert this using 2; ring_nf
  -- Phase 4: R2. (n+2, 1, 0, 0, n) -> (n+1, 0, 1, 0, n+1).
  have h4 : (⟨n + 2, 1, 0, 0, n⟩ : Q) [fm]⊢ ⟨n + 1, 0, 1, 0, n + 1⟩ := by
    rw [show n + 2 = (n + 1) + 1 from by ring]; simp [fm]
  -- Phase 5: R3 chain c=1, (n+1) rounds. (n+1, 0, 1, 0, n+1) ->* (0, 0, 1, n+1, 2*n+2).
  have h5 : ⟨n + 1, 0, 1, 0, n + 1⟩ [fm]⊢* ⟨0, 0, 1, n + 1, 2 * n + 2⟩ := by
    have := r3_chain_c1 (n + 1) (a := 0) (d := 0) (e := n + 1)
    rw [show 0 + (n + 1) = n + 1 from by ring,
        show n + 1 + (n + 1) = 2 * n + 2 from by ring] at this
    exact this
  -- Phase 6: R4. (0, 0, 1, n+1, 2*n+2) -> (0, 1, 1, n+1, 2*n+1).
  have h6 : (⟨0, 0, 1, n + 1, 2 * n + 2⟩ : Q) [fm]⊢ ⟨0, 1, 1, n + 1, 2 * n + 1⟩ := by
    rw [show 2 * n + 2 = (2 * n + 1) + 1 from by ring]; simp [fm]
  -- Phase 7: R1. (0, 1, 1, n+1, 2*n+1) -> (2, 0, 0, n, 2*n+1).
  have h7 : (⟨0, 1, 1, n + 1, 2 * n + 1⟩ : Q) [fm]⊢ ⟨2, 0, 0, n, 2 * n + 1⟩ := by
    rw [show n + 1 = n + 1 from rfl]; simp [fm]
  -- Phase 8: R3 x 2. (2, 0, 0, n, 2*n+1) ->* (0, 0, 0, n+2, 2*n+3).
  have h8 : ⟨2, 0, 0, n, 2 * n + 1⟩ [fm]⊢* ⟨0, 0, 0, n + 2, 2 * n + 3⟩ := by
    have := r3_chain 2 (a := 0) (d := n) (e := 2 * n + 1)
    rw [show 0 + 2 = 2 from by ring, show n + 2 = n + 2 from rfl,
        show 2 * n + 1 + 2 = 2 * n + 3 from by ring] at this
    exact this
  -- Compose all phases.
  exact stepStar_stepPlus_stepPlus h1
    (step_stepStar_stepPlus h2
      (stepStar_trans h3
        (stepStar_trans (step_stepStar h4)
          (stepStar_trans h5
            (stepStar_trans (step_stepStar h6)
              (stepStar_trans (step_stepStar h7) h8))))))

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨0, 0, 0, 1, 1⟩)
  · execute fm 1
  apply progress_nonhalt_simple (fm := fm) (A := ℕ)
    (fun n ↦ ⟨0, 0, 0, n + 1, 2 * n + 1⟩) 0
  intro n; exists n + 1; exact main_trans n

end Sz22_2003_unofficial_869
