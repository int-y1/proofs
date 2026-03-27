import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #6: [1/105, 20/3, 3/22, 49/2, 363/7]

Vector representation:
```
 0 -1 -1 -1  0
 2 -1  1  0  0
-1  1  0  0 -1
-1  0  0  2  0
 0  1  0 -1  2
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_6

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a, b+1, c+1, d+1, e⟩ => some ⟨a, b, c, d, e⟩
  | ⟨a, b+1, c, d, e⟩ => some ⟨a+2, b, c+1, d, e⟩
  | ⟨a+1, b, c, d, e+1⟩ => some ⟨a, b+1, c, d, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b, c, d+2, e⟩
  | ⟨a, b, c, d+1, e⟩ => some ⟨a, b+1, c, d, e+2⟩
  | _ => none

-- R3 chain: each step a -= 1, d += 2
theorem r3_chain : ∀ k : ℕ, ∀ a c d,
    ⟨a + k, 0, c, d, 0⟩ [fm]⊢* ⟨a, 0, c, d + 2 * k, 0⟩ := by
  intro k; induction' k with k ih <;> intro a c d
  · exists 0
  rw [show a + (k + 1) = (a + k) + 1 from by ring]
  step fm
  apply stepStar_trans (ih _ _ _)
  ring_nf; finish

-- R4/R0 interleave: each round c -= 1, d -= 2, e += 2
theorem r4r0_chain : ∀ k : ℕ, ∀ c d e,
    ⟨0, 0, c + k, d + 2 * k, e⟩ [fm]⊢* ⟨0, 0, c, d, e + 2 * k⟩ := by
  intro k; induction' k with k ih <;> intro c d e
  · exists 0
  rw [show c + (k + 1) = (c + k) + 1 from by ring,
      show d + 2 * (k + 1) = (d + 2 * k) + 1 + 1 from by ring]
  step fm; step fm
  apply stepStar_trans (ih _ _ _)
  ring_nf; finish

-- R2/R1 chain: each round a += 1, c += 1, e -= 1
theorem r2r1_chain : ∀ k : ℕ, ∀ a c e,
    ⟨a + 1, 0, c, 0, e + k⟩ [fm]⊢* ⟨a + k + 1, 0, c + k, 0, e⟩ := by
  intro k; induction' k with k ih <;> intro a c e
  · exists 0
  rw [show e + (k + 1) = (e + k) + 1 from by ring]
  step fm; step fm
  apply stepStar_trans (ih _ _ _)
  ring_nf; finish

-- Main transition: (2*n+2, 0, 2*n+1, 0, 0) →⁺ (4*n+4, 0, 4*n+3, 0, 0)
theorem main_trans : ∀ n : ℕ,
    ⟨2 * n + 2, 0, 2 * n + 1, 0, 0⟩ [fm]⊢⁺ ⟨4 * n + 4, 0, 4 * n + 3, 0, 0⟩ := by
  intro n
  -- Phase 1: R3 chain, 2*n+2 steps: → (0, 0, 2*n+1, 4*n+4, 0)
  apply stepStar_stepPlus_stepPlus
  · have h := r3_chain (2 * n + 2) 0 (2 * n + 1) 0
    simp only [Nat.zero_add] at h
    rw [show 2 * (2 * n + 2) = 4 * n + 4 from by ring] at h
    exact h
  -- Phase 2: R4/R0 chain, 2*n+1 rounds: → (0, 0, 0, 2, 4*n+2)
  apply stepStar_stepPlus_stepPlus
  · have h := r4r0_chain (2 * n + 1) 0 2 0
    simp only [Nat.zero_add] at h
    rw [show 2 * (2 * n + 1) = 4 * n + 2 from by ring] at h
    rw [show (2 : ℕ) + (4 * n + 2) = 4 * n + 4 from by ring] at h
    exact h
  -- Phase 3: 6 individual steps reaching (2, 0, 1, 0, 4*n+2)
  -- R4: (0, 0, 0, 2, 4*n+2) → (0, 1, 0, 1, 4*n+4)
  apply step_stepStar_stepPlus
  · show fm ⟨0, 0, 0, 1 + 1, 4 * n + 2⟩ = some ⟨0, 0 + 1, 0, 1, 4 * n + 2 + 2⟩; simp [fm]
  -- R1: (0, 1, 0, 1, 4*n+4) → (2, 0, 1, 1, 4*n+4)
  apply stepStar_trans
  · exact step_stepStar (show fm ⟨0, 0 + 1, 0, 1, 4 * n + 4⟩ =
      some ⟨0 + 2, 0, 0 + 1, 1, 4 * n + 4⟩ from by simp [fm])
  -- R2: (2, 0, 1, 1, 4*n+4) → (1, 1, 1, 1, 4*n+3)
  apply stepStar_trans
  · exact step_stepStar (show fm ⟨1 + 1, 0, 1, 1, (4 * n + 3) + 1⟩ =
      some ⟨1, 0 + 1, 1, 1, 4 * n + 3⟩ from by simp [fm])
  -- R0: (1, 1, 1, 1, 4*n+3) → (1, 0, 0, 0, 4*n+3)
  apply stepStar_trans
  · exact step_stepStar (show fm ⟨1, 0 + 1, 0 + 1, 0 + 1, 4 * n + 3⟩ =
      some ⟨1, 0, 0, 0, 4 * n + 3⟩ from by simp [fm])
  -- R2: (1, 0, 0, 0, 4*n+3) → (0, 1, 0, 0, 4*n+2)
  apply stepStar_trans
  · exact step_stepStar (show fm ⟨0 + 1, 0, 0, 0, (4 * n + 2) + 1⟩ =
      some ⟨0, 0 + 1, 0, 0, 4 * n + 2⟩ from by simp [fm])
  -- R1: (0, 1, 0, 0, 4*n+2) → (2, 0, 1, 0, 4*n+2)
  apply stepStar_trans
  · exact step_stepStar (show fm ⟨0, 0 + 1, 0, 0, 4 * n + 2⟩ =
      some ⟨0 + 2, 0, 0 + 1, 0, 4 * n + 2⟩ from by simp [fm])
  -- Phase 4: R2/R1 chain, 4*n+2 rounds: (2, 0, 1, 0, 4*n+2) →* (4*n+4, 0, 4*n+3, 0, 0)
  have h := r2r1_chain (4 * n + 2) 1 1 0
  simp only [Nat.zero_add] at h
  rw [show 1 + (4 * n + 2) + 1 = 4 * n + 4 from by ring,
      show 1 + (4 * n + 2) = 4 * n + 3 from by ring] at h
  exact h

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨2, 0, 1, 0, 0⟩) (by execute fm 7)
  apply progress_nonhalt_simple (fm := fm) (A := ℕ)
    (fun n ↦ ⟨2 * n + 2, 0, 2 * n + 1, 0, 0⟩) 0
  intro n; exists (2 * n + 1)
  have h := main_trans n
  rw [show 2 * (2 * n + 1) + 2 = 4 * n + 4 from by ring,
      show 2 * (2 * n + 1) + 1 = 4 * n + 3 from by ring]
  exact h

end Sz22_2003_unofficial_6
