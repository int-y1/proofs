import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #567: [35/3, 12/55, 1/5, 121/2, 1/77, 5/11]

Vector representation:
```
 0 -1  1  1  0
 2  1 -1  0 -1
 0  0 -1  0  0
-1  0  0  0  2
 0  0  0 -1 -1
 0  0  1  0 -1
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_567

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a, b+1, c, d, e⟩ => some ⟨a, b, c+1, d+1, e⟩
  | ⟨a, b, c+1, d, e+1⟩ => some ⟨a+2, b+1, c, d, e⟩
  | ⟨a, b, c+1, d, e⟩ => some ⟨a, b, c, d, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b, c, d, e+2⟩
  | ⟨a, b, c, d+1, e+1⟩ => some ⟨a, b, c, d, e⟩
  | ⟨a, b, c, d, e+1⟩ => some ⟨a, b, c+1, d, e⟩
  | _ => none

-- R2+R1 interleaved chain: consumes e, builds a and d
theorem r2r1_chain : ∀ k, ∀ a d e, ⟨a, 0, 1, d, e+k⟩ [fm]⊢* ⟨a+2*k, 0, 1, d+k, e⟩ := by
  intro k; induction' k with k h <;> intro a d e
  · exists 0
  rw [show e + (k + 1) = (e + k) + 1 from by ring]
  step fm; step fm
  apply stepStar_trans (h _ _ _)
  ring_nf; finish

-- R4 repeated: converts a to e
theorem a_to_e : ∀ k, ∀ a d e, ⟨a+k, 0, 0, d, e⟩ [fm]⊢* ⟨a, 0, 0, d, e+2*k⟩ := by
  intro k; induction' k with k h <;> intro a d e
  · exists 0
  rw [show a + (k + 1) = (a + k) + 1 from by ring]
  step fm
  apply stepStar_trans (h _ _ _)
  ring_nf; finish

-- R5 repeated: annihilates d and e together
theorem de_annihilate : ∀ k, ∀ d e, ⟨0, 0, 0, d+k, e+k⟩ [fm]⊢* ⟨0, 0, 0, d, e⟩ := by
  intro k; induction' k with k h <;> intro d e
  · exists 0
  rw [show d + (k + 1) = (d + k) + 1 from by ring,
      show e + (k + 1) = (e + k) + 1 from by ring]
  step fm
  apply stepStar_trans (h _ _)
  ring_nf; finish

-- Full transition: (0, 0, 0, 0, n+2) ->⁺ (0, 0, 0, 0, 3*n+3)
theorem main_trans : ⟨0, 0, 0, 0, n+2⟩ [fm]⊢⁺ ⟨0, 0, 0, 0, 3*n+3⟩ := by
  -- R6, R2, R1: (0,0,0,0,n+2) -> (2,0,1,1,n)
  step fm; step fm; step fm
  -- R2+R1 chain: (2,0,1,1,n) ->* (2+2n,0,1,1+n,0)
  rw [show n = 0 + n from by ring]
  apply stepStar_trans (r2r1_chain n 2 1 0)
  simp only [Nat.zero_add]
  -- R3: (2+2n,0,1,1+n,0) -> (2+2n,0,0,1+n,0)
  step fm
  -- R4 chain: (2+2n,0,0,1+n,0) ->* (0,0,0,1+n,4+4n)
  rw [show 2 + 2 * n = 0 + (2 + 2 * n) from by ring]
  apply stepStar_trans (a_to_e (2 + 2 * n) 0 (1 + n) 0)
  simp only [Nat.zero_add]
  -- R5 chain: (0,0,0,1+n,2*(2+2n)) ->* (0,0,0,0,3n+3)
  rw [show 1 + n = 0 + (1 + n) from by ring,
      show 2 * (2 + 2 * n) = (3 * n + 3) + (1 + n) from by ring]
  apply stepStar_trans (de_annihilate (1 + n) 0 (3 * n + 3))
  ring_nf; finish

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨0, 0, 0, 0, 2⟩) (by execute fm 1)
  apply progress_nonhalt_simple (fm := fm) (A := ℕ)
    (fun n ↦ ⟨0, 0, 0, 0, n + 2⟩) 0
  intro n; exact ⟨3 * n + 1, main_trans⟩

end Sz22_2003_unofficial_567
