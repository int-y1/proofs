import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #707: [35/6, 4/55, 121/2, 3/7, 42/11]

Vector representation:
```
-1 -1  1  1  0
 2  0 -1  0 -1
-1  0  0  0  2
 0  1  0 -1  0
 1  1  0  1 -1
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_707

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a+1, b+1, c, d, e⟩ => some ⟨a, b, c+1, d+1, e⟩
  | ⟨a, b, c+1, d, e+1⟩ => some ⟨a+2, b, c, d, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b, c, d, e+2⟩
  | ⟨a, b, c, d+1, e⟩ => some ⟨a, b+1, c, d, e⟩
  | ⟨a, b, c, d, e+1⟩ => some ⟨a+1, b+1, c, d+1, e⟩
  | _ => none

theorem r3_chain : ∀ k, ∀ a d e, ⟨a + k, 0, 0, d, e⟩ [fm]⊢* ⟨a, 0, 0, d, e + 2 * k⟩ := by
  intro k; induction' k with k ih <;> intro a d e
  · exists 0
  · rw [show a + (k + 1) = (a + k) + 1 from by ring]
    step fm
    apply stepStar_trans (ih a d (e + 2))
    ring_nf; finish

theorem r4_chain : ∀ k, ∀ b d e, ⟨0, b, 0, d + k, e⟩ [fm]⊢* ⟨0, b + k, 0, d, e⟩ := by
  intro k; induction' k with k ih <;> intro b d e
  · exists 0
  · rw [show d + (k + 1) = (d + k) + 1 from by ring]
    step fm
    apply stepStar_trans (ih (b + 1) d e)
    ring_nf; finish

theorem r2_chain : ∀ k, ∀ a d e, ⟨a, 0, k, d, e + k⟩ [fm]⊢* ⟨a + 2 * k, 0, 0, d, e⟩ := by
  intro k; induction' k with k ih <;> intro a d e
  · exists 0
  · rw [show e + (k + 1) = (e + k) + 1 from by ring]
    step fm
    apply stepStar_trans (ih (a + 2) d e)
    ring_nf; finish

theorem r2r1r1_chain : ∀ k, ∀ c d e, ⟨0, 2 * k, c + 1, d, e + k⟩ [fm]⊢* ⟨0, 0, c + k + 1, d + 2 * k, e⟩ := by
  intro k; induction' k with k ih <;> intro c d e
  · exists 0
  · rw [show 2 * (k + 1) = (2 * k + 1) + 1 from by ring,
        show e + (k + 1) = (e + k) + 1 from by ring]
    step fm
    rw [show 2 * k + 1 = (2 * k) + 1 from by ring]
    step fm; step fm
    apply stepStar_trans (ih (c + 1) (d + 2) e)
    ring_nf; finish

theorem phase_r3 (n : ℕ) :
    ⟨2 * n + 4, 0, 0, 2 * n + 4, n * (n + 1)⟩ [fm]⊢⁺
    ⟨0, 0, 0, 2 * n + 4, n * n + 5 * n + 8⟩ := by
  apply step_stepStar_stepPlus
  · show fm ⟨(2 * n + 3) + 1, 0, 0, 2 * n + 4, n * (n + 1)⟩ =
        some ⟨2 * n + 3, 0, 0, 2 * n + 4, n * (n + 1) + 2⟩
    simp [fm]
  have key := r3_chain (2 * n + 3) 0 (2 * n + 4) (n * (n + 1) + 2)
  rw [show 0 + (2 * n + 3) = 2 * n + 3 from by ring,
      show n * (n + 1) + 2 + 2 * (2 * n + 3) = n * n + 5 * n + 8 from by ring] at key
  exact key

theorem phase_rest (n : ℕ) :
    ⟨0, 0, 0, 2 * n + 4, n * n + 5 * n + 8⟩ [fm]⊢*
    ⟨2 * n + 6, 0, 0, 2 * n + 6, (n + 1) * (n + 2)⟩ := by
  -- Phase 2: R4 chain
  rw [show 2 * n + 4 = 0 + (2 * n + 4) from by ring]
  apply stepStar_trans (r4_chain (2 * n + 4) 0 0 (n * n + 5 * n + 8))
  rw [show 0 + (2 * n + 4) = 2 * n + 4 from by ring]
  -- State: (0, 2n+4, 0, 0, n^2+5n+8)
  -- Phase 3: R5 + R1
  rw [show n * n + 5 * n + 8 = (n * n + 5 * n + 7) + 1 from by ring]
  step fm
  rw [show 2 * n + 4 + 1 = (2 * n + 4) + 1 from by ring]
  step fm
  -- State: (0, 2n+4, 1, 2, n^2+5n+7)
  -- Phase 4: R2R1R1 chain
  rw [show n * n + 5 * n + 7 = (n * n + 4 * n + 5) + (n + 2) from by ring,
      show 2 * n + 4 = 2 * (n + 2) from by ring]
  apply stepStar_trans (r2r1r1_chain (n + 2) 0 2 (n * n + 4 * n + 5))
  -- State: (0, 0, n+3, 2n+6, n^2+4n+5)
  rw [show 0 + (n + 2) + 1 = n + 3 from by ring,
      show 2 + 2 * (n + 2) = 2 * n + 6 from by ring,
      show n * n + 4 * n + 5 = (n * n + 3 * n + 2) + (n + 3) from by ring]
  -- Phase 5: R2 chain
  apply stepStar_trans (r2_chain (n + 3) 0 (2 * n + 6) (n * n + 3 * n + 2))
  rw [show 0 + 2 * (n + 3) = 2 * n + 6 from by ring,
      show n * n + 3 * n + 2 = (n + 1) * (n + 2) from by ring]
  finish

theorem main_trans (n : ℕ) :
    ⟨2 * n + 4, 0, 0, 2 * n + 4, n * (n + 1)⟩ [fm]⊢⁺
    ⟨2 * n + 6, 0, 0, 2 * n + 6, (n + 1) * (n + 2)⟩ :=
  stepPlus_stepStar_stepPlus (phase_r3 n) (phase_rest n)

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨4, 0, 0, 4, 0⟩) (by execute fm 15)
  apply progress_nonhalt_simple (fm := fm) (A := ℕ)
    (fun n ↦ ⟨2 * n + 4, 0, 0, 2 * n + 4, n * (n + 1)⟩) 0
  intro n; exact ⟨n + 1, main_trans n⟩

end Sz22_2003_unofficial_707
