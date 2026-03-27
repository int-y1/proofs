import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #528: [28/15, 39/22, 35/2, 11/13, 22/7]

Vector representation:
```
 2 -1 -1  1  0  0
-1  1  0  0 -1  1
-1  0  1  1  0  0
 0  0  0  0  1 -1
 1  0  0 -1  1  0
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_528

def Q := ℕ × ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a, b+1, c+1, d, e, f⟩ => some ⟨a+2, b, c, d+1, e, f⟩
  | ⟨a+1, b, c, d, e+1, f⟩ => some ⟨a, b+1, c, d, e, f+1⟩
  | ⟨a+1, b, c, d, e, f⟩ => some ⟨a, b, c+1, d+1, e, f⟩
  | ⟨a, b, c, d, e, f+1⟩ => some ⟨a, b, c, d, e+1, f⟩
  | ⟨a, b, c, d+1, e, f⟩ => some ⟨a+1, b, c, d, e+1, f⟩
  | _ => none

-- R3 repeated: drain a, build c and d
theorem a_to_cd : ∀ k c d, ⟨k, 0, c, d, 0, f⟩ [fm]⊢* ⟨0, 0, c+k, d+k, 0, f⟩ := by
  intro k; induction' k with k ih <;> intro c d
  · exists 0
  rw [show c + (k + 1) = (c + 1) + k from by ring]
  rw [show d + (k + 1) = (d + 1) + k from by ring]
  step fm; exact ih _ _

-- R4 repeated: drain f to e
theorem f_to_e : ∀ k e, ⟨0, 0, c, d, e, k⟩ [fm]⊢* ⟨0, 0, c, d, e+k, 0⟩ := by
  intro k; induction' k with k ih <;> intro e
  · exists 0
  rw [show e + (k + 1) = (e + 1) + k from by ring]
  step fm; exact ih _

-- R2+R1 interleaved chain
theorem r2r1_chain : ∀ k a d f, ⟨a+1, 0, k, d, k, f⟩ [fm]⊢* ⟨a+1+k, 0, 0, d+k, 0, f+k⟩ := by
  intro k; induction' k with k ih <;> intro a d f
  · exists 0
  rw [show a + 1 + (k + 1) = (a + 1 + 1) + k from by ring]
  rw [show d + (k + 1) = (d + 1) + k from by ring]
  rw [show f + (k + 1) = (f + 1) + k from by ring]
  step fm; step fm; exact ih _ _ _

-- Main transition
theorem main_trans (n : ℕ) : ⟨n+2, 0, 0, (n+1)*(n+1), 0, n+1⟩ [fm]⊢⁺
    ⟨n+3, 0, 0, (n+2)*(n+2), 0, n+2⟩ := by
  -- R3 step (gives ⊢⁺)
  step fm
  -- R3*(n+1) more
  have h1 := a_to_cd (f := n+1) (n+1) 1 ((n+1)*(n+1)+1)
  rw [show 1 + (n+1) = n + 2 from by ring] at h1
  rw [show (n+1)*(n+1) + 1 + (n+1) = (n+1)*(n+1) + (n+2) from by ring] at h1
  apply stepStar_trans h1
  -- R4*(n+1)
  have h2 := f_to_e (c := n+2) (d := (n+1)*(n+1)+(n+2)) (n+1) 0
  rw [show 0 + (n+1) = n + 1 from by ring] at h2
  apply stepStar_trans h2
  -- R5
  rw [show (n+1)*(n+1) + (n+2) = (n*n+2*n+1+n+1) + 1 from by ring]
  step fm
  -- R2R1*(n+2)
  have h4 := r2r1_chain (n+2) 0 (n*n+2*n+1+n+1) 0
  rw [show 0 + 1 + (n+2) = n + 3 from by ring] at h4
  rw [show (n*n+2*n+1+n+1) + (n+2) = (n+2)*(n+2) from by ring] at h4
  rw [show 0 + (n+2) = n + 2 from by ring] at h4
  exact stepStar_trans h4 (by finish)

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨3, 0, 0, 4, 0, 2⟩) (by execute fm 12)
  apply progress_nonhalt_simple (fm := fm) (A := ℕ)
    (fun n ↦ ⟨n+3, 0, 0, (n+2)*(n+2), 0, n+2⟩) 0
  intro n; exists n+1; exact main_trans (n+1)

end Sz22_2003_unofficial_528
