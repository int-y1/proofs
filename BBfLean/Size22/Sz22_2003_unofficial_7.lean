import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #7: [1/105, 3/22, 20/3, 49/2, 363/7]

Vector representation:
```
 0 -1 -1 -1  0
-1  1  0  0 -1
 2 -1  1  0  0
-1  0  0  2  0
 0  1  0 -1  2
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_7

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a, b+1, c+1, d+1, e⟩ => some ⟨a, b, c, d, e⟩
  | ⟨a+1, b, c, d, e+1⟩ => some ⟨a, b+1, c, d, e⟩
  | ⟨a, b+1, c, d, e⟩ => some ⟨a+2, b, c+1, d, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b, c, d+2, e⟩
  | ⟨a, b, c, d+1, e⟩ => some ⟨a, b+1, c, d, e+2⟩
  | _ => none

-- R4 chain: (a+k, 0, c, d, 0) →* (a, 0, c, d+2*k, 0)
theorem r4_chain : ∀ k, ∀ a d, ⟨a+k, 0, c, d, 0⟩ [fm]⊢* ⟨a, 0, c, d+2*k, 0⟩ := by
  intro k; induction' k with k ih <;> intro a d
  · exists 0
  rw [show a + (k + 1) = (a + k) + 1 from by ring]
  step fm
  apply stepStar_trans (ih _ _)
  ring_nf; finish

-- R5/R1 interleave: (0, 0, c+k, d+2*k, e) →* (0, 0, c, d, e+2*k)
theorem r5r1_chain : ∀ k, ∀ c d e, ⟨0, 0, c+k, d+2*k, e⟩ [fm]⊢* ⟨0, 0, c, d, e+2*k⟩ := by
  intro k; induction' k with k ih <;> intro c d e
  · exists 0
  rw [show c + (k + 1) = (c + k) + 1 from by ring,
      show d + 2 * (k + 1) = (d + 2 * k) + 2 from by ring]
  step fm; step fm
  apply stepStar_trans (ih _ _ _)
  ring_nf; finish

-- Bridge: (0, 0, 0, 2, e) →* (0, 1, 0, 0, e)
theorem bridge : ⟨0, 0, 0, 2, e⟩ [fm]⊢* ⟨0, 1, 0, 0, e⟩ := by
  execute fm 5

-- R3/R2/R2 chain: (0, b+1, b, 0, 2*k) →* (0, b+k+1, b+k, 0, 0)
theorem r3r2r2_chain : ∀ k, ∀ b, ⟨0, b+1, b, 0, 2*k⟩ [fm]⊢* ⟨0, b+k+1, b+k, 0, 0⟩ := by
  intro k; induction' k with k ih <;> intro b
  · exists 0
  rw [show 2 * (k + 1) = 2 * k + 2 from by ring]
  step fm; step fm; step fm
  rw [show b + 1 + 1 = (b + 1) + 1 from by ring]
  apply stepStar_trans (ih _)
  ring_nf; finish

-- R3 drain: (a, k, c, 0, 0) →* (a+2*k, 0, c+k, 0, 0)
theorem r3_drain : ∀ k, ∀ a c, ⟨a, k, c, 0, 0⟩ [fm]⊢* ⟨a+2*k, 0, c+k, 0, 0⟩ := by
  intro k; induction' k with k ih <;> intro a c
  · exists 0
  rw [show (k + 1) = k + 1 from rfl]
  step fm
  apply stepStar_trans (ih _ _)
  ring_nf; finish

-- Main transition: (2*(n+1), 0, 2*n+1, 0, 0) →⁺ (4*(n+1), 0, 4*n+3, 0, 0)
theorem main_trans (n : ℕ) : ⟨2*(n+1), 0, 2*n+1, 0, 0⟩ [fm]⊢⁺ ⟨4*(n+1), 0, 4*n+3, 0, 0⟩ := by
  -- Phase 1: R4 chain → (0, 0, 2*n+1, 4*(n+1), 0)
  have h1 : ⟨2*(n+1), 0, 2*n+1, 0, 0⟩ [fm]⊢* ⟨0, 0, 2*n+1, 4*(n+1), 0⟩ := by
    rw [show 2*(n+1) = 0 + 2*(n+1) from by ring,
        show (0 : ℕ) = 0 + 2*0 from by ring]
    apply stepStar_trans (r4_chain (2*(n+1)) 0 0)
    ring_nf; finish
  -- Phase 2: R5/R1 chain → (0, 0, 0, 2, 2*(2*n+1))
  have h2 : ⟨0, 0, 2*n+1, 4*(n+1), 0⟩ [fm]⊢* ⟨0, 0, 0, 2, 2*(2*n+1)⟩ := by
    rw [show 2*n+1 = 0 + (2*n+1) from by ring,
        show 4*(n+1) = 2 + 2*(2*n+1) from by ring,
        show (0 : ℕ) = 0 + 2*0 from by ring]
    apply stepStar_trans (r5r1_chain (2*n+1) 0 2 0)
    ring_nf; finish
  -- Phase 3: bridge → (0, 1, 0, 0, 2*(2*n+1))
  have h3 : ⟨0, 0, 0, 2, 2*(2*n+1)⟩ [fm]⊢* ⟨0, 1, 0, 0, 2*(2*n+1)⟩ := bridge
  -- Phase 4: R3/R2/R2 chain → (0, 2*n+2, 2*n+1, 0, 0)
  have h4 : ⟨0, 1, 0, 0, 2*(2*n+1)⟩ [fm]⊢* ⟨0, 2*n+2, 2*n+1, 0, 0⟩ := by
    rw [show (1 : ℕ) = 0 + 1 from by ring]
    apply stepStar_trans (r3r2r2_chain (2*n+1) 0)
    ring_nf; finish
  -- Phase 5: R3 drain → (4*(n+1), 0, 4*n+3, 0, 0)
  have h5 : ⟨0, 2*n+2, 2*n+1, 0, 0⟩ [fm]⊢* ⟨4*(n+1), 0, 4*n+3, 0, 0⟩ := by
    apply stepStar_trans (r3_drain (2*n+2) 0 (2*n+1))
    ring_nf; finish
  -- Compose: ⊢* + ⊢* + ⊢* + ⊢* + ⊢* = ⊢* but we need ⊢⁺
  -- Use stepStar_stepPlus with h1 ≠ target
  apply stepStar_stepPlus_stepPlus h1
  apply stepStar_stepPlus_stepPlus h2
  apply stepStar_stepPlus_stepPlus h3
  apply stepStar_stepPlus_stepPlus h4
  -- h5 is ⊢*, need ⊢⁺. Use stepStar_stepPlus since states differ.
  apply stepStar_stepPlus h5
  simp [Q]

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨2, 0, 1, 0, 0⟩) (by execute fm 7)
  apply progress_nonhalt_simple (fm := fm) (A := ℕ)
    (fun n ↦ ⟨2*(n+1), 0, 2*n+1, 0, 0⟩) 0
  intro n
  refine ⟨2*n+1, ?_⟩
  rw [show 2 * (2 * n + 1 + 1) = 4 * (n + 1) from by ring,
      show 2 * (2 * n + 1) + 1 = 4 * n + 3 from by ring]
  exact main_trans n

end Sz22_2003_unofficial_7
