import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz21_140_unofficial #65: [4/15, 33/14, 25/2, 7/11, 33/5]

Vector representation:
```
 2 -1 -1  0  0
-1  1  0 -1  1
-1  0  2  0  0
 0  0  0  1 -1
 0  1 -1  0  1
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz21_140_unofficial_65

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a, b+1, c+1, d, e⟩ => some ⟨a+2, b, c, d, e⟩
  | ⟨a+1, b, c, d+1, e⟩ => some ⟨a, b+1, c, d, e+1⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b, c+2, d, e⟩
  | ⟨a, b, c, d, e+1⟩ => some ⟨a, b, c, d+1, e⟩
  | ⟨a, b, c+1, d, e⟩ => some ⟨a, b+1, c, d, e+1⟩
  | _ => none

-- R3 repeated: a → c+2 (when b=0, d=0)
theorem a_to_c : ∀ k, ∀ a c e, ⟨a+k, 0, c, 0, e⟩ [fm]⊢* ⟨a, 0, c+2*k, 0, e⟩ := by
  intro k; induction' k with k h <;> intro a c e
  · exists 0
  rw [← Nat.add_assoc]
  step fm
  apply stepStar_trans (h _ _ _)
  ring_nf; finish

-- R4 repeated: e → d
theorem e_to_d : ∀ k, ∀ c d e, ⟨0, 0, c, d, e+k⟩ [fm]⊢* ⟨0, 0, c, d+k, e⟩ := by
  intro k; induction' k with k h <;> intro c d e
  · exists 0
  rw [← Nat.add_assoc]
  step fm
  apply stepStar_trans (h _ _ _)
  ring_nf; finish

-- R2+R1 chain: each round a→a+1, c→c-1, d→d-1, e→e+1
theorem r2r1_chain : ∀ k, ∀ A C E, ⟨A+1, 0, C+k, k, E⟩ [fm]⊢* ⟨A+k+1, 0, C, 0, E+k⟩ := by
  intro k; induction' k with k h <;> intro A C E
  · exists 0
  -- State: (A+1, 0, C+k+1, k+1, E)
  rw [show C + (k + 1) = (C + k) + 1 from by ring,
      show (k : ℕ) + 1 = k + 1 from rfl]
  -- R2: a+1 >= 1, d = k+1 >= 1
  step fm
  -- After R2: (A, 1, C+k+1, k, E+1)
  rw [show C + k + 1 = (C + k) + 1 from by ring]
  -- R1: b=1 >= 1, c = C+k+1 >= 1
  step fm
  -- After R1: (A+2, 0, C+k, k, E+1)
  rw [show A + 2 = (A + 1) + 1 from by ring]
  apply stepStar_trans (h _ _ _)
  ring_nf; finish

-- Main transition: (0, 0, c+n+3, n+1, 0) →⁺ (0, 0, c+2*n+6, n+2, 0)
theorem main_trans (c n : ℕ) : ⟨0, 0, c+n+3, n+1, 0⟩ [fm]⊢⁺ ⟨0, 0, c+2*n+6, n+2, 0⟩ := by
  -- Phase 1: R5 once: (0, 0, c+n+3, n+1, 0) → (0, 1, c+n+2, n+1, 1)
  rw [show c + n + 3 = (c + n + 2) + 1 from by ring]
  apply step_stepStar_stepPlus
  · show fm ⟨0, 0, (c + n + 2) + 1, n + 1, 0⟩ = some ⟨0, 1, c + n + 2, n + 1, 1⟩
    simp [fm]
  -- Phase 2: R1 once: (0, 1, c+n+2, n+1, 1) → (2, 0, c+n+1, n+1, 1)
  apply stepStar_trans
  · rw [show c + n + 2 = (c + n + 1) + 1 from by ring]
    have : fm ⟨0, 0 + 1, (c + n + 1) + 1, n + 1, 1⟩ = some ⟨2, 0, c + n + 1, n + 1, 1⟩ := by
      simp [fm]
    exact step_stepStar this
  -- Phase 3: R2+R1 chain with k = n+1 rounds
  -- (2, 0, c+n+1, n+1, 1) →* (n+3, 0, c, 0, n+2)
  apply stepStar_trans
  · have h := r2r1_chain (n + 1) 1 c 1
    rw [show (1 : ℕ) + 1 = 2 from rfl,
        show c + (n + 1) = c + n + 1 from by ring,
        show (1 : ℕ) + (n + 1) + 1 = n + 3 from by ring,
        show (1 : ℕ) + (n + 1) = n + 2 from by ring] at h
    exact h
  -- Phase 4: R3 repeated (n+3) times: (n+3, 0, c, 0, n+2) →* (0, 0, c+2*(n+3), 0, n+2)
  apply stepStar_trans
  · have h := a_to_c (n + 3) 0 c (n + 2)
    simp only [Nat.zero_add] at h
    exact h
  -- Phase 5: R4 repeated (n+2) times: (0, 0, c+2*(n+3), 0, n+2) →* (0, 0, c+2*(n+3), n+2, 0)
  have h := e_to_d (n + 2) (c + 2 * (n + 3)) 0 0
  simp only [Nat.zero_add] at h
  refine stepStar_trans h ?_
  ring_nf; finish

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨0, 0, 4, 1, 0⟩) (by execute fm 6)
  apply progress_nonhalt_simple (fm := fm) (A := ℕ × ℕ)
    (fun ⟨c, n⟩ ↦ ⟨0, 0, c+n+3, n+1, 0⟩) ⟨1, 0⟩
  intro ⟨c, n⟩
  refine ⟨⟨c+n+2, n+1⟩, ?_⟩
  show ⟨0, 0, c+n+3, n+1, 0⟩ [fm]⊢⁺ ⟨0, 0, c+n+2+(n+1)+3, (n+1)+1, 0⟩
  rw [show c + n + 2 + (n + 1) + 3 = c + 2 * n + 6 from by ring,
      show (n + 1) + 1 = n + 2 from by ring]
  exact main_trans c n
