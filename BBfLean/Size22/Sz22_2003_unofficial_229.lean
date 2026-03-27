import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #229: [11/105, 15/22, 4/3, 35/2, 33/5]

Vector representation:
```
 0 -1 -1 -1  1
-1  1  1  0 -1
 2 -1  0  0  0
-1  0  1  1  0
 0  1 -1  0  1
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_229

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a, b+1, c+1, d+1, e⟩ => some ⟨a, b, c, d, e+1⟩
  | ⟨a+1, b, c, d, e+1⟩ => some ⟨a, b+1, c+1, d, e⟩
  | ⟨a, b+1, c, d, e⟩ => some ⟨a+2, b, c, d, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b, c+1, d+1, e⟩
  | ⟨a, b, c+1, d, e⟩ => some ⟨a, b+1, c, d, e+1⟩
  | _ => none

-- Rule 4 chain: (a+k, 0, c, d, 0) →* (a, 0, c+k, d+k, 0)
theorem r4_chain : ∀ k, ∀ a c d, ⟨a+k, 0, c, d, 0⟩ [fm]⊢* ⟨a, 0, c+k, d+k, 0⟩ := by
  intro k; induction' k with k ih <;> intro a c d
  · exists 0
  rw [show a + (k + 1) = (a + k) + 1 from by ring]
  step fm
  apply stepStar_trans (ih a (c + 1) (d + 1))
  ring_nf; finish

-- Rules 5,1 chain: (0, 0, c+2*k, d+k, e) →* (0, 0, c, d, e+2*k)
theorem r51_chain : ∀ k, ∀ c d e, ⟨0, 0, c+2*k, d+k, e⟩ [fm]⊢* ⟨0, 0, c, d, e+2*k⟩ := by
  intro k; induction' k with k ih <;> intro c d e
  · exists 0
  rw [show c + 2 * (k + 1) = (c + 2 * k) + 2 from by ring,
      show d + (k + 1) = (d + k) + 1 from by ring]
  step fm; step fm
  apply stepStar_trans (ih c d (e + 2))
  ring_nf; finish

-- Rule 3 chain: (a, b+k, c, 0, 0) →* (a+2*k, b, c, 0, 0)
theorem r3_chain : ∀ k, ∀ a b c, ⟨a, b+k, c, 0, 0⟩ [fm]⊢* ⟨a+2*k, b, c, 0, 0⟩ := by
  intro k; induction' k with k ih <;> intro a b c
  · exists 0
  rw [show b + (k + 1) = (b + k) + 1 from by ring]
  step fm
  apply stepStar_trans (ih (a + 2) b c)
  ring_nf; finish

-- Buildup loop: (0, b+1, c, 0, 2*k) →* (0, b+k+1, c+2*k, 0, 0)
theorem buildup_loop : ∀ k, ∀ b c, ⟨0, b+1, c, 0, 2*k⟩ [fm]⊢* ⟨0, b+k+1, c+2*k, 0, 0⟩ := by
  intro k; induction' k with k ih <;> intro b c
  · exists 0
  rw [show 2 * (k + 1) = 2 * k + 2 from by ring]
  step fm; step fm; step fm
  apply stepStar_trans (ih (b + 1) (c + 2))
  ring_nf; finish

-- Main cycle: (N+1, 0, N, 0, 0) →⁺ (2*N+2, 0, 2*N+1, 0, 0)
theorem main_cycle (N : ℕ) : ⟨N+1, 0, N, 0, 0⟩ [fm]⊢⁺ ⟨2*N+2, 0, 2*N+1, 0, 0⟩ := by
  -- Phase 1: r4_chain N+1 times: (N+1, 0, N, 0, 0) →* (0, 0, 2*N+1, N+1, 0)
  apply stepStar_stepPlus_stepPlus (c₂ := ⟨0, 0, 2*N+1, N+1, 0⟩)
  · have h := r4_chain (N+1) 0 N 0
    simp only [Nat.zero_add] at h
    rw [show N + (N + 1) = 2 * N + 1 from by ring] at h
    exact h
  -- Phase 2: r51_chain N times: (0, 0, 2*N+1, N+1, 0) →* (0, 0, 1, 1, 2*N)
  apply stepStar_stepPlus_stepPlus (c₂ := ⟨0, 0, 1, 1, 2*N⟩)
  · have h := r51_chain N 1 1 0
    rw [show 1 + 2 * N = 2 * N + 1 from by ring, show 1 + N = N + 1 from by ring,
        show 0 + 2 * N = 2 * N from by ring] at h
    exact h
  -- Phase 3: rule 5: (0, 0, 1, 1, 2*N) → (0, 1, 0, 1, 2*N+1)
  apply stepStar_stepPlus_stepPlus (c₂ := ⟨0, 1, 0, 1, 2*N+1⟩)
  · step fm; finish
  -- Phase 4: rule 3: (0, 1, 0, 1, 2*N+1) → (2, 0, 0, 1, 2*N+1)
  apply stepStar_stepPlus_stepPlus (c₂ := ⟨2, 0, 0, 1, 2*N+1⟩)
  · step fm; finish
  -- Phase 5: rule 2: (2, 0, 0, 1, 2*N+1) → (1, 1, 1, 1, 2*N)
  apply stepStar_stepPlus_stepPlus (c₂ := ⟨1, 1, 1, 1, 2*N⟩)
  · step fm; finish
  -- Phase 6: rule 1: (1, 1, 1, 1, 2*N) → (1, 0, 0, 0, 2*N+1)
  apply stepStar_stepPlus_stepPlus (c₂ := ⟨1, 0, 0, 0, 2*N+1⟩)
  · step fm; finish
  -- Phase 7: rule 2: (1, 0, 0, 0, 2*N+1) → (0, 1, 1, 0, 2*N)
  apply stepStar_stepPlus_stepPlus (c₂ := ⟨0, 1, 1, 0, 2*N⟩)
  · step fm; finish
  -- Phase 8: buildup_loop N times: (0, 1, 1, 0, 2*N) →* (0, N+1, 2*N+1, 0, 0)
  apply stepStar_stepPlus_stepPlus (c₂ := ⟨0, N+1, 2*N+1, 0, 0⟩)
  · have h := buildup_loop N 0 1
    rw [show 0 + 1 = 1 from by ring, show 0 + N + 1 = N + 1 from by ring,
        show 1 + 2 * N = 2 * N + 1 from by ring] at h
    exact h
  -- Phase 9: r3_chain N+1 times: (0, N+1, 2*N+1, 0, 0) →* (2*N+2, 0, 2*N+1, 0, 0)
  have h := r3_chain (N+1) 0 0 (2*N+1)
  simp only [Nat.zero_add] at h
  rw [show 2 * (N + 1) = 2 * N + 2 from by ring] at h
  exact stepStar_stepPlus h (by simp [Q])

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨2, 0, 1, 0, 0⟩) (by execute fm 7)
  apply progress_nonhalt (fm := fm)
    (P := fun q ↦ ∃ N, q = ⟨N+1, 0, N, 0, 0⟩)
  · intro c ⟨N, hq⟩; subst hq
    exact ⟨⟨2*N+2, 0, 2*N+1, 0, 0⟩, ⟨2*N+1, by ring_nf⟩, main_cycle N⟩
  · exact ⟨1, rfl⟩

end Sz22_2003_unofficial_229
