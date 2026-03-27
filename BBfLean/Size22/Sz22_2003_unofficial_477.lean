import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #477: [28/15, 3/22, 1/3, 25/2, 11/7, 3/5]

Vector representation:
```
 2 -1 -1  1  0
-1  1  0  0 -1
 0 -1  0  0  0
-1  0  2  0  0
 0  0  0 -1  1
 0  1 -1  0  0
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_477

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a, b+1, c+1, d, e⟩ => some ⟨a+2, b, c, d+1, e⟩
  | ⟨a+1, b, c, d, e+1⟩ => some ⟨a, b+1, c, d, e⟩
  | ⟨a, b+1, c, d, e⟩ => some ⟨a, b, c, d, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b, c+2, d, e⟩
  | ⟨a, b, c, d+1, e⟩ => some ⟨a, b, c, d, e+1⟩
  | ⟨a, b, c+1, d, e⟩ => some ⟨a, b+1, c, d, e⟩
  | _ => none

-- R4 repeated: (a+k, 0, c, d, 0) ->* (a, 0, c+2*k, d, 0)
theorem a_to_c : ∀ k a c d, ⟨a+k, 0, c, d, 0⟩ [fm]⊢* ⟨a, 0, c+2*k, d, 0⟩ := by
  intro k; induction' k with k h <;> intro a c d
  · exists 0
  rw [← Nat.add_assoc]
  step fm
  apply stepStar_trans (h _ _ _)
  ring_nf; finish

-- R5 repeated: (0, 0, c, d+k, e) ->* (0, 0, c, d, e+k)
theorem d_to_e : ∀ k c d e, ⟨0, 0, c, d+k, e⟩ [fm]⊢* ⟨0, 0, c, d, e+k⟩ := by
  intro k; induction' k with k h <;> intro c d e
  · exists 0
  rw [← Nat.add_assoc]
  step fm
  apply stepStar_trans (h _ _ _)
  ring_nf; finish

-- R2+R1 chain: (a+1, 0, c+k, d, e+k) ->* (a+k+1, 0, c, d+k, e)
theorem r2r1_chain : ∀ k a c d e, ⟨a+1, 0, c+k, d, e+k⟩ [fm]⊢* ⟨a+k+1, 0, c, d+k, e⟩ := by
  intro k; induction' k with k h <;> intro a c d e
  · exists 0
  rw [show c + (k + 1) = (c + 1) + k from by ring,
      show e + (k + 1) = (e + k) + 1 from by ring]
  step fm
  rw [show (c + 1) + k = (c + k) + 1 from by ring]
  step fm
  apply stepStar_trans (h _ _ _ _)
  ring_nf; finish

-- Main transition: (n+2, 0, c, n+1, 0) ⊢⁺ (n+3, 0, c+n+1, n+2, 0)
theorem main_trans (n c : ℕ) :
    ⟨n+2, 0, c, n+1, 0⟩ [fm]⊢⁺ ⟨n+3, 0, c+n+1, n+2, 0⟩ := by
  -- First R4 step gives ⊢⁺
  apply step_stepStar_stepPlus (c₂ := ⟨n+1, 0, c+2, n+1, 0⟩)
  · show fm ⟨n + 2, 0, c, n + 1, 0⟩ = some ⟨n + 1, 0, c + 2, n + 1, 0⟩
    simp [fm]
  -- Remaining R4 steps
  apply stepStar_trans (c₂ := ⟨0, 0, c + 2 * n + 4, n + 1, 0⟩)
  · have h := a_to_c (n+1) 0 (c+2) (n+1)
    simp only [Nat.zero_add, show c + 2 + 2 * (n + 1) = c + 2 * n + 4 from by ring] at h
    exact h
  -- R5 chain
  apply stepStar_trans (c₂ := ⟨0, 0, c + 2 * n + 4, 0, n + 1⟩)
  · have h := d_to_e (n+1) (c + 2 * n + 4) 0 0
    simp only [Nat.zero_add] at h; exact h
  -- R6 step
  rw [show c + 2 * n + 4 = (c + 2 * n + 3) + 1 from by ring]
  step fm
  -- R1 step
  rw [show c + 2 * n + 3 = (c + 2 * n + 2) + 1 from by ring]
  step fm
  -- R2+R1 chain (n+1 pairs)
  apply stepStar_trans (c₂ := ⟨n+3, 0, c+n+1, n+2, 0⟩)
  · have h := r2r1_chain (n+1) 1 (c+n+1) 1 0
    simp only [show 1 + (n + 1) = n + 2 from by ring,
               show (c + n + 1) + (n + 1) = c + 2 * n + 2 from by ring,
               show 0 + (n + 1) = n + 1 from by ring] at h
    exact h
  finish

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨2, 0, 0, 1, 0⟩) (by execute fm 3)
  apply progress_nonhalt_simple (fm := fm) (A := ℕ × ℕ)
    (fun ⟨n, c⟩ ↦ ⟨n+2, 0, c, n+1, 0⟩) ⟨0, 0⟩
  intro ⟨n, c⟩
  exact ⟨⟨n+1, c+n+1⟩, main_trans n c⟩

end Sz22_2003_unofficial_477
