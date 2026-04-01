import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #1270: [5/6, 99/35, 49/3, 4/11, 15/2]

Vector representation:
```
-1 -1  1  0  0
 0  2 -1 -1  1
 0 -1  0  2  0
 2  0  0  0 -1
-1  1  1  0  0
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_1270

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a+1, b+1, c, d, e⟩ => some ⟨a, b, c+1, d, e⟩
  | ⟨a, b, c+1, d+1, e⟩ => some ⟨a, b+2, c, d, e+1⟩
  | ⟨a, b+1, c, d, e⟩ => some ⟨a, b, c, d+2, e⟩
  | ⟨a, b, c, d, e+1⟩ => some ⟨a+2, b, c, d, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b+1, c+1, d, e⟩
  | _ => none

-- R4: drain e into a
theorem e_drain : ∀ k a d e, ⟨a, (0 : ℕ), (0 : ℕ), d, e + k⟩ [fm]⊢* ⟨a + 2 * k, (0 : ℕ), (0 : ℕ), d, e⟩ := by
  intro k; induction' k with k ih <;> intro a d e
  · simp; exists 0
  · rw [show e + (k + 1) = (e + k) + 1 from by ring]
    step fm
    apply stepStar_trans (ih (a + 2) d e); ring_nf; finish

-- R3: drain b into d
theorem b_drain : ∀ k b d e, ⟨(0 : ℕ), b + k, (0 : ℕ), d, e⟩ [fm]⊢* ⟨(0 : ℕ), b, (0 : ℕ), d + 2 * k, e⟩ := by
  intro k; induction' k with k ih <;> intro b d e
  · simp; exists 0
  · rw [show b + (k + 1) = (b + k) + 1 from by ring]
    step fm
    apply stepStar_trans (ih b (d + 2) e); ring_nf; finish

-- R2 chain: drain c (and d) into b and e
theorem r2_chain : ∀ k, ∀ b c d e, ⟨(0 : ℕ), b, c + k, d + k, e⟩ [fm]⊢* ⟨(0 : ℕ), b + 2 * k, c, d, e + k⟩ := by
  intro k; induction' k with k ih <;> intro b c d e
  · simp; exists 0
  · rw [show c + (k + 1) = (c + k) + 1 from by ring,
        show d + (k + 1) = (d + k) + 1 from by ring]
    step fm
    apply stepStar_trans (ih (b + 2) c d (e + 1)); ring_nf; finish

-- R2,R1,R1 interleaved chain
theorem r2r1r1_chain : ∀ k, ∀ a c d e, ⟨a + 2 * k, (0 : ℕ), c + 1, d + k, e⟩ [fm]⊢* ⟨a, (0 : ℕ), c + k + 1, d, e + k⟩ := by
  intro k; induction' k with k ih <;> intro a c d e
  · simp; exists 0
  · rw [show a + 2 * (k + 1) = (a + 2) + 2 * k from by ring,
        show d + (k + 1) = (d + 1) + k from by ring]
    apply stepStar_trans (ih (a + 2) c (d + 1) e)
    rw [show c + k + 1 = (c + k) + 1 from by ring,
        show (d + 1) = d + 1 from rfl]
    step fm; step fm; step fm
    rw [show c + k + 2 = c + (k + 1) + 1 from by ring]
    finish

-- Full transition from (2*(n+1), 0, 0, D + 2*n + 2, 0)
-- to (4*(n+1), 0, 0, D + 4*n + 8, 0)
theorem main_transition (n D : ℕ) :
    ⟨2 * n + 2, (0 : ℕ), (0 : ℕ), D + 2 * n + 2, (0 : ℕ)⟩ [fm]⊢⁺
    ⟨4 * n + 4, (0 : ℕ), (0 : ℕ), D + 4 * n + 8, (0 : ℕ)⟩ := by
  -- Phase 1: R5 then R1
  rw [show 2 * n + 2 = (2 * n + 1) + 1 from by ring]
  step fm
  rw [show 2 * n + 1 = (2 * n) + 1 from by ring]
  step fm
  -- State: (2*n, 0, 2, D + 2*n + 2, 0)
  -- Phase 2: R2,R1,R1 chain (n rounds)
  rw [show D + 2 * n + 2 = (D + n + 2) + n from by ring,
      show 2 * n = 0 + 2 * n from by ring,
      show (2 : ℕ) = 1 + 1 from by ring]
  apply stepStar_trans (r2r1r1_chain n 0 1 (D + n + 2) 0)
  rw [show 1 + n + 1 = n + 2 from by ring,
      show (0 : ℕ) + n = n from by ring]
  -- State: (0, 0, n+2, D + n + 2, n)
  -- Phase 3: R2 chain (n+2 rounds)
  rw [show n + 2 = 0 + (n + 2) from by ring,
      show D + n + 2 = D + (n + 2) from by ring]
  apply stepStar_trans (r2_chain (n + 2) 0 0 D n)
  rw [show (0 : ℕ) + 2 * (n + 2) = 2 * n + 4 from by ring,
      show n + (n + 2) = 2 * n + 2 from by ring]
  -- State: (0, 2*n+4, 0, D, 2*n+2)
  -- Phase 4: R3 chain
  rw [show 2 * n + 4 = 0 + (2 * n + 4) from by ring]
  apply stepStar_trans (b_drain (2 * n + 4) 0 D (2 * n + 2))
  -- State: (0, 0, 0, D + 2*(2*n+4), 2*n+2)
  -- Phase 5: R4 chain
  rw [show 2 * n + 2 = 0 + (2 * n + 2) from by ring]
  apply stepStar_trans (e_drain (2 * n + 2) 0 (D + 2 * (2 * n + 4)) 0)
  rw [show 0 + 2 * (2 * n + 2) = 4 * n + 4 from by ring,
      show D + 2 * (2 * n + 4) = D + 4 * n + 8 from by ring]
  finish

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨2, 0, 0, 5, 0⟩) (by execute fm 6)
  apply progress_nonhalt (fm := fm)
    (P := fun q ↦ ∃ a D, q = ⟨2 * a + 2, 0, 0, D + 2 * a + 2, 0⟩)
  · intro c ⟨a, D, hq⟩; subst hq
    exact ⟨_, ⟨2 * a + 1, D + 4, by ring_nf⟩, main_transition a D⟩
  · exact ⟨0, 3, rfl⟩

end Sz22_2003_unofficial_1270
