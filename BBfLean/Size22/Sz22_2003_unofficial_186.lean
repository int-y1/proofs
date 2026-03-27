import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #186: [1/6, 175/3, 3/55, 2/5, 11/14, 3/2]

Vector representation:
```
-1 -1  0  0  0
 0 -1  2  1  0
 0  1 -1  0 -1
 1  0 -1  0  0
-1  0  0 -1  1
-1  1  0  0  0
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_186

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a+1, b+1, c, d, e⟩ => some ⟨a, b, c, d, e⟩
  | ⟨a, b+1, c, d, e⟩ => some ⟨a, b, c+2, d+1, e⟩
  | ⟨a, b, c+1, d, e+1⟩ => some ⟨a, b+1, c, d, e⟩
  | ⟨a, b, c+1, d, e⟩ => some ⟨a+1, b, c, d, e⟩
  | ⟨a+1, b, c, d+1, e⟩ => some ⟨a, b, c, d, e+1⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b+1, c, d, e⟩
  | _ => none

-- Rule 5 applied k times: (a+k, 0, 0, d+k, e) ->* (a, 0, 0, d, e+k)
theorem drain_ad : ∀ k, ∀ a d e, ⟨a + k, 0, 0, d + k, e⟩ [fm]⊢* ⟨a, 0, 0, d, e + k⟩ := by
  intro k; induction' k with k ih <;> intro a d e
  · exists 0
  rw [show a + (k + 1) = (a + k) + 1 from by ring,
      show d + (k + 1) = (d + k) + 1 from by ring]
  step fm
  apply stepStar_trans (ih a d (e + 1)); ring_nf; finish

-- Rule 4 applied k times: (a, 0, k, d, 0) ->* (a+k, 0, 0, d, 0)
theorem drain_c : ∀ k, ∀ a d, ⟨a, 0, k, d, 0⟩ [fm]⊢* ⟨a + k, 0, 0, d, 0⟩ := by
  intro k; induction' k with k ih <;> intro a d
  · exists 0
  rw [show k + 1 = k + 1 from rfl]
  step fm
  apply stepStar_trans (ih (a + 1) d); ring_nf; finish

-- Interleaved R3, R2 pairs: (0, 0, c+1, d, k) ->* (0, 0, c+k+1, d+k, 0)
theorem interleave : ∀ k, ∀ c d, ⟨0, 0, c + 1, d, k⟩ [fm]⊢* ⟨(0 : ℕ), 0, c + k + 1, d + k, 0⟩ := by
  intro k; induction' k with k ih <;> intro c d
  · exists 0
  rw [show c + (k + 1) + 1 = (c + 1) + k + 1 from by ring,
      show d + (k + 1) = (d + 1) + k from by ring]
  step fm; step fm
  apply stepStar_trans (ih (c + 1) (d + 1)); ring_nf; finish

-- Main transition: (n+2, 0, 0, n+1, 0) ->+ (n+3, 0, 0, n+2, 0)
theorem main_trans : ∀ n, ⟨n + 2, 0, 0, n + 1, 0⟩ [fm]⊢⁺ ⟨n + 3, 0, 0, n + 2, 0⟩ := by
  intro n
  -- Phase 1: R5 first step (gives stepPlus), then drain remaining
  -- (n+2, 0, 0, n+1, 0) = ((n+1)+1, 0, 0, n+1, 0)
  -- R5: -> (n+1, 0, 0, n, 1) -- but wait, n+1 = n + 1 so d+1 pattern...
  -- Actually (n+2, 0, 0, n+1, 0) with a=n+2>=1, d=n+1>=1: R5 fires
  -- -> (n+1, 0, 0, n, 1)
  apply step_stepStar_stepPlus
    (c₂ := ⟨n + 1, 0, 0, n, 1⟩)
  · show fm ⟨(n + 1) + 1, 0, 0, n + 1, 0⟩ = some ⟨n + 1, 0, 0, n, 1⟩
    simp [fm]
  -- Drain remaining n: (n+1, 0, 0, n, 1) ->* (1, 0, 0, 0, n+1)
  apply stepStar_trans (c₂ := ⟨1, 0, 0, 0, n + 1⟩)
  · have h := drain_ad n 1 0 1; simp only [Nat.zero_add] at h
    rw [show 1 + n = n + 1 from by ring] at h; exact h
  -- Phase 2: R6 then R2: (1, 0, 0, 0, n+1) -> (0, 1, 0, 0, n+1) -> (0, 0, 2, 1, n+1)
  apply stepStar_trans (c₂ := ⟨0, 0, 2, 1, n + 1⟩)
  · step fm; step fm; finish
  -- Phase 3: interleave (n+1) pairs: (0, 0, 2, 1, n+1) ->* (0, 0, n+3, n+2, 0)
  apply stepStar_trans (c₂ := ⟨0, 0, n + 3, n + 2, 0⟩)
  · have h := interleave (n + 1) 1 1
    rw [show 1 + (n + 1) + 1 = n + 3 from by ring,
        show 1 + (n + 1) = n + 2 from by ring] at h; exact h
  -- Phase 4: drain c to a: (0, 0, n+3, n+2, 0) ->* (n+3, 0, 0, n+2, 0)
  have h := drain_c (n + 3) 0 (n + 2)
  rw [show (0 : ℕ) + (n + 3) = n + 3 from by ring] at h; exact h

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨2, 0, 0, 1, 0⟩) (by execute fm 4)
  apply progress_nonhalt (fm := fm)
    (P := fun q ↦ ∃ n, q = ⟨n + 2, 0, 0, n + 1, 0⟩)
  · intro q ⟨n, hq⟩
    subst hq
    exact ⟨⟨n + 3, 0, 0, n + 2, 0⟩, ⟨n + 1, rfl⟩, main_trans n⟩
  · exact ⟨0, rfl⟩

end Sz22_2003_unofficial_186
