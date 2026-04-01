import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #1309: [63/10, 121/2, 4/77, 5/3, 35/11]

Vector representation:
```
-1  2 -1  1  0
-1  0  0  0  2
 2  0  0 -1 -1
 0 -1  1  0  0
 0  0  1  1 -1
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_1309

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a+1, b, c+1, d, e⟩ => some ⟨a, b+2, c, d+1, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b, c, d, e+2⟩
  | ⟨a, b, c, d+1, e+1⟩ => some ⟨a+2, b, c, d, e⟩
  | ⟨a, b+1, c, d, e⟩ => some ⟨a, b, c+1, d, e⟩
  | ⟨a, b, c, d, e+1⟩ => some ⟨a, b, c+1, d+1, e⟩
  | _ => none

-- R4 repeated: drain b into c.
theorem b_to_c : ∀ k, ∀ b c, ⟨0, k + b, c, 0, e⟩ [fm]⊢* ⟨0, b, c + k, 0, e⟩ := by
  intro k; induction' k with k ih <;> intro b c
  · ring_nf; finish
  · rw [show k + 1 + b = (k + (b + 1)) from by ring]
    step fm
    apply stepStar_trans (ih b (c + 1))
    ring_nf; finish

-- R1,R1,R3 chain: each round consumes 2 from c, adds 4 to b, adds 1 to d, subtracts 1 from e.
theorem r1r1r3_chain : ∀ k, ∀ b c d e, ⟨2, b, c + 2 * k, d, e + k⟩ [fm]⊢* ⟨2, b + 4 * k, c, d + k, e⟩ := by
  intro k; induction' k with k ih <;> intro b c d e
  · ring_nf; finish
  · rw [show c + 2 * (k + 1) = (c + 2) + 2 * k from by ring,
        show e + (k + 1) = (e + 1) + k from by ring]
    apply stepStar_trans (ih b (c + 2) d (e + 1))
    step fm  -- R1
    step fm  -- R1
    step fm  -- R3
    ring_nf; finish

-- R3,R2,R2 drain: each round consumes 1 from d, adds 3 to e.
theorem r3r2r2_drain : ∀ k, ∀ b d e, ⟨0, b, 0, k + d, e + 1⟩ [fm]⊢* ⟨0, b, 0, d, e + 1 + 3 * k⟩ := by
  intro k; induction' k with k ih <;> intro b d e
  · ring_nf; finish
  · rw [show k + 1 + d = (k + d) + 1 from by ring]
    step fm  -- R3: (2, b, 0, k+d, e)
    step fm  -- R2: (1, b, 0, k+d, e+2)
    step fm  -- R2: (0, b, 0, k+d, e+4)
    rw [show e + 4 = (e + 3) + 1 from by ring]
    apply stepStar_trans (ih b d (e + 3))
    ring_nf; finish

-- Transition for even c (c = 2*m):
-- (0,0,2m,0,2m+n+2) ⊢⁺ (0,0,4m+2,0,4m+n+5)
theorem trans_even (m n : ℕ) : ⟨0, 0, 2 * m, 0, 2 * m + n + 2⟩ [fm]⊢⁺ ⟨0, 0, 4 * m + 2, 0, 4 * m + n + 5⟩ := by
  -- R5
  step fm
  -- R3
  step fm
  -- Now goal is ⊢* from (2, 0, 2*m+1, 0, 2*m+n)
  -- Chain with k=m: (2, 0, 1+2*m, 0, (n+m)+m)
  rw [show 2 * m + 1 = 1 + 2 * m from by ring,
      show 2 * m + n = (n + m) + m from by ring]
  apply stepStar_trans (r1r1r3_chain m 0 1 0 (n + m))
  rw [show 0 + 4 * m = 4 * m from by ring, show 0 + m = m from by ring]
  -- R1 (tail c=1): (2, 4m, 1, m, n+m)
  step fm  -- R1: (1, 4m+2, 0, m+1, n+m)
  -- R2: (0, 4m+2, 0, m+1, n+m+2)
  step fm
  -- R3,R2,R2 drain with d = m+1
  rw [show m + 1 = (m + 1) + 0 from by ring,
      show n + m + 2 = (n + m + 1) + 1 from by ring]
  apply stepStar_trans (r3r2r2_drain (m + 1) (4 * m + 2) 0 (n + m + 1))
  -- b_to_c: (0, 4m+2, 0, 0, n+m+1+1+3*(m+1))
  rw [show n + m + 1 + 1 + 3 * (m + 1) = 4 * m + n + 5 from by ring,
      show 4 * m + 2 = (4 * m + 2) + 0 from by ring]
  apply stepStar_trans (b_to_c (4 * m + 2) 0 0 (e := 4 * m + n + 5))
  ring_nf; finish

-- Transition for odd c (c = 2*m+1):
-- (0,0,2m+1,0,2m+n+3) ⊢⁺ (0,0,4m+4,0,4m+n+7)
theorem trans_odd (m n : ℕ) : ⟨0, 0, 2 * m + 1, 0, 2 * m + n + 3⟩ [fm]⊢⁺ ⟨0, 0, 4 * m + 4, 0, 4 * m + n + 7⟩ := by
  -- R5
  step fm
  -- R3
  step fm
  -- Chain with k=m+1: (2, 0, 0+2*(m+1), 0, (m+n)+(m+1))
  rw [show 2 * m + 2 = 0 + 2 * (m + 1) from by ring,
      show 2 * m + n + 1 = (m + n) + (m + 1) from by ring]
  apply stepStar_trans (r1r1r3_chain (m + 1) 0 0 0 (m + n))
  rw [show 0 + 4 * (m + 1) = 4 * m + 4 from by ring, show 0 + (m + 1) = m + 1 from by ring]
  -- R2 (tail c=0): (2, 4m+4, 0, m+1, m+n)
  step fm  -- R2: (1, 4m+4, 0, m+1, m+n+2)
  -- R2: (0, 4m+4, 0, m+1, m+n+4)
  step fm
  -- R3,R2,R2 drain with d = m+1
  rw [show m + 1 = (m + 1) + 0 from by ring,
      show m + n + 4 = (m + n + 3) + 1 from by ring]
  apply stepStar_trans (r3r2r2_drain (m + 1) (4 * m + 4) 0 (m + n + 3))
  -- b_to_c
  rw [show m + n + 3 + 1 + 3 * (m + 1) = 4 * m + n + 7 from by ring,
      show 4 * m + 4 = (4 * m + 4) + 0 from by ring]
  apply stepStar_trans (b_to_c (4 * m + 4) 0 0 (e := 4 * m + n + 7))
  ring_nf; finish

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨0, 0, 0, 0, 2⟩) (by execute fm 1)
  apply progress_nonhalt_simple (fm := fm) (A := ℕ × ℕ)
    (fun ⟨c, n⟩ ↦ ⟨0, 0, c, 0, c + n + 2⟩) ⟨0, 0⟩
  intro ⟨c, n⟩
  rcases Nat.even_or_odd c with ⟨m, hm⟩ | ⟨m, hm⟩
  · rw [show m + m = 2 * m from by ring] at hm; subst hm
    refine ⟨⟨4 * m + 2, n + 1⟩, ?_⟩
    show ⟨0, 0, 2 * m, 0, 2 * m + n + 2⟩ [fm]⊢⁺ ⟨0, 0, 4 * m + 2, 0, 4 * m + 2 + (n + 1) + 2⟩
    rw [show 4 * m + 2 + (n + 1) + 2 = 4 * m + n + 5 from by ring]
    exact trans_even m n
  · subst hm
    refine ⟨⟨4 * m + 4, n + 1⟩, ?_⟩
    show ⟨0, 0, 2 * m + 1, 0, 2 * m + 1 + n + 2⟩ [fm]⊢⁺ ⟨0, 0, 4 * m + 4, 0, 4 * m + 4 + (n + 1) + 2⟩
    rw [show 2 * m + 1 + n + 2 = 2 * m + n + 3 from by ring,
        show 4 * m + 4 + (n + 1) + 2 = 4 * m + n + 7 from by ring]
    exact trans_odd m n

end Sz22_2003_unofficial_1309
