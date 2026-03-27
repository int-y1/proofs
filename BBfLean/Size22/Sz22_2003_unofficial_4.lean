import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #4: [1/105, 18/5, 25/22, 7/2, 605/7]

Vector representation:
```
 0 -1 -1 -1  0
 1  2 -1  0  0
-1  0  2  0 -1
-1  0  0  1  0
 0  0  1 -1  2
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_4

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a, b+1, c+1, d+1, e⟩ => some ⟨a, b, c, d, e⟩
  | ⟨a, b, c+1, d, e⟩ => some ⟨a+1, b+2, c, d, e⟩
  | ⟨a+1, b, c, d, e+1⟩ => some ⟨a, b, c+2, d, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b, c, d+1, e⟩
  | ⟨a, b, c, d+1, e⟩ => some ⟨a, b, c+1, d, e+2⟩
  | _ => none

-- R3 drain: (a+k, b, 0, d, 0) ->* (a, b, 0, d+k, 0)
theorem r3_drain : ∀ k, ∀ a b d, ⟨a+k, b, 0, d, 0⟩ [fm]⊢* ⟨a, b, 0, d+k, 0⟩ := by
  intro k; induction' k with k ih <;> intro a b d
  · exists 0
  rw [show a + (k + 1) = (a + k) + 1 from by ring]
  step fm
  apply stepStar_trans (ih a b (d + 1))
  ring_nf; finish

-- R4+R0 interleave: (0, b+k, 0, d+2*k, e) ->* (0, b, 0, d, e+2*k)
theorem r4r0_drain : ∀ k, ∀ b d e, ⟨0, b+k, 0, d+2*k, e⟩ [fm]⊢* ⟨0, b, 0, d, e+2*k⟩ := by
  intro k; induction' k with k ih <;> intro b d e
  · exists 0
  rw [show d + 2 * (k + 1) = (d + 2 * k) + 2 from by ring,
      show b + (k + 1) = (b + k) + 1 from by ring]
  step fm
  step fm
  apply stepStar_trans (ih b d (e + 2))
  ring_nf; finish

-- Growth: (a+1, b, 0, 0, k) ->* (a+1+k, b+4*k, 0, 0, 0)
theorem growth : ∀ k, ∀ a b, ⟨a+1, b, 0, 0, k⟩ [fm]⊢* ⟨a+1+k, b+4*k, 0, 0, 0⟩ := by
  intro k; induction' k with k ih <;> intro a b
  · exists 0
  rw [show (k + 1) = k + 1 from rfl]
  step fm
  step fm
  step fm
  apply stepStar_trans (ih (a + 1) (b + 4))
  ring_nf; finish

-- Main transition: parameterized by n and r where b = n + r
-- From (2*n+1, n+r, 0, 0, 0) ->+ (2*n+3, n+r+7*n+10, 0, 0, 0)
theorem main_trans (n r : ℕ) :
    ⟨2*n+1, n+r, 0, 0, 0⟩ [fm]⊢⁺ ⟨2*n+3, n+r+7*n+10, 0, 0, 0⟩ := by
  -- Phase 1: R3 drain (2n+1 times)
  apply stepStar_stepPlus_stepPlus (c₂ := ⟨0, n+r, 0, 2*n+1, 0⟩)
  · have h := r3_drain (2*n+1) 0 (n+r) 0
    simp only [Nat.zero_add] at h; exact h
  -- Phase 2: R4+R0 drain (n rounds)
  -- (0, n+r, 0, 2*n+1, 0) ->* (0, r, 0, 1, 2*n)
  apply stepStar_stepPlus_stepPlus (c₂ := ⟨0, r, 0, 1, 2*n⟩)
  · have h := r4r0_drain n r 1 0
    simp only [Nat.zero_add] at h
    rw [show r + n = n + r from by ring,
        show 1 + 2 * n = 2 * n + 1 from by ring] at h; exact h
  -- Phase 2b: R4 once: (0, r, 0, 1, 2*n) -> (0, r, 1, 0, 2*n+2)
  -- Phase 2c: R1: (0, r, 1, 0, 2*n+2) -> (1, r+2, 0, 0, 2*n+2)
  apply step_stepStar_stepPlus
  · show fm ⟨0, r, 0, 1, 2*n⟩ = some ⟨0, r, 1, 0, 2*n+2⟩; simp [fm]
  step fm
  -- Phase 3: Growth (2*n+2 rounds)
  -- (1, r+2, 0, 0, 2*n+2) ->* (1+2*n+2, r+2+4*(2*n+2), 0, 0, 0)
  -- = (2*n+3, r+8*n+10, 0, 0, 0)
  have h := growth (2*n+2) 0 (r+2)
  simp only [Nat.zero_add] at h
  rw [show 1 + (2 * n + 2) = 2 * n + 3 from by ring,
      show (r + 2) + 4 * (2 * n + 2) = r + 8 * n + 10 from by ring] at h
  rw [show n + r + 7 * n + 10 = r + 8 * n + 10 from by ring]
  exact h

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨3, 10, 0, 0, 0⟩) (by execute fm 9)
  apply progress_nonhalt_simple (fm := fm) (A := ℕ × ℕ)
    (fun ⟨n, r⟩ ↦ ⟨2*n+1, n+r, 0, 0, 0⟩) ⟨1, 9⟩
  intro ⟨n, r⟩
  exists ⟨n+1, r+7*n+9⟩
  show ⟨2*n+1, n+r, 0, 0, 0⟩ [fm]⊢⁺ ⟨2*(n+1)+1, (n+1)+(r+7*n+9), 0, 0, 0⟩
  rw [show 2*(n+1)+1 = 2*n+3 from by ring,
      show (n+1)+(r+7*n+9) = n+r+7*n+10 from by ring]
  exact main_trans n r

end Sz22_2003_unofficial_4
