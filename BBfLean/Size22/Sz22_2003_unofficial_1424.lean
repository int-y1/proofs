import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #1424: [7/15, 2/3, 99/14, 5/11, 1617/2]

Vector representation:
```
 0 -1 -1  1  0
 1 -1  0  0  0
-1  2  0 -1  1
 0  0  1  0 -1
-1  1  0  2  1
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_1424

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a, b+1, c+1, d, e⟩ => some ⟨a, b, c, d+1, e⟩
  | ⟨a, b+1, c, d, e⟩ => some ⟨a+1, b, c, d, e⟩
  | ⟨a+1, b, c, d+1, e⟩ => some ⟨a, b+2, c, d, e+1⟩
  | ⟨a, b, c, d, e+1⟩ => some ⟨a, b, c+1, d, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b+1, c, d+2, e+1⟩
  | _ => none

-- R4: transfer e to c (with b=0, d=0).
theorem e_to_c : ∀ k c, ⟨a, 0, c, 0, e + k⟩ [fm]⊢* ⟨a, 0, c + k, 0, e⟩ := by
  intro k; induction' k with k ih
  · intro c; exists 0
  · intro c; rw [Nat.add_succ]
    step fm
    apply stepStar_trans (ih (c + 1)); ring_nf; finish

-- R3,R2,R2 chain: drain d, build a and e (with b=0, c=0).
theorem r3r2r2_chain : ∀ k a d e, ⟨a + 1, 0, 0, d + k, e⟩ [fm]⊢* ⟨a + k + 1, 0, 0, d, e + k⟩ := by
  intro k; induction' k with k ih
  · intro a d e; exists 0
  · intro a d e
    rw [show d + (k + 1) = (d + k) + 1 from by ring]
    step fm; step fm; step fm
    apply stepStar_trans (ih (a + 1) d (e + 1)); ring_nf; finish

-- R3,R1,R1 chain: each round a-=1, c-=2, d+=1, e+=1.
-- From (a+k+1, 0, c+2*k, d+1, e) to (a+1, 0, c, d+k+1, e+k).
theorem r3r1r1_chain : ∀ k, ∀ a c d e, ⟨a + k + 1, 0, c + 2 * k, d + 1, e⟩ [fm]⊢* ⟨a + 1, 0, c, d + k + 1, e + k⟩ := by
  intro k; induction' k with k ih <;> intro a c d e
  · exists 0
  · rw [show a + (k + 1) + 1 = (a + k + 1) + 1 from by ring,
        show c + 2 * (k + 1) = (c + 2 * k) + 2 from by ring]
    step fm; step fm; step fm
    apply stepStar_trans (ih a c (d + 1) (e + 1)); ring_nf; finish

-- Even case: n=2m, C(2m) = (4m+3, 0, 6m+3, 0, 0) ⊢⁺ C(2m+1) = (4m+5, 0, 6m+6, 0, 0)
theorem main_even (m : ℕ) :
    ⟨4 * m + 3, 0, 6 * m + 3, 0, 0⟩ [fm]⊢⁺ ⟨4 * m + 5, 0, 6 * m + 6, 0, 0⟩ := by
  -- R5: (4m+3, 0, 6m+3, 0, 0) -> (4m+2, 1, 6m+3, 2, 1)
  rw [show 4 * m + 3 = (4 * m + 2) + 1 from by ring]
  step fm
  -- R1: (4m+2, 1, 6m+3, 2, 1) -> (4m+2, 0, 6m+2, 3, 1)
  rw [show 6 * m + 3 = (6 * m + 2) + 1 from by ring]
  step fm
  -- r3r1r1_chain with k = 3*m+1
  rw [show (4 * m + 2 : ℕ) = m + (3 * m + 1) + 1 from by ring,
      show (6 * m + 2 : ℕ) = 0 + 2 * (3 * m + 1) from by ring,
      show (3 : ℕ) = 2 + 1 from by ring]
  apply stepStar_trans (r3r1r1_chain (3 * m + 1) m 0 2 1)
  -- State: (m+1, 0, 0, 3m+4, 3m+2)
  rw [show (2 + (3 * m + 1) + 1 : ℕ) = 0 + (3 * m + 4) from by ring]
  apply stepStar_trans (r3r2r2_chain (3 * m + 4) m 0 (1 + (3 * m + 1)))
  -- State: (m+1+3m+4, 0, 0, 0, (3m+2)+(3m+4)) = (4m+5, 0, 0, 0, 6m+6)
  rw [show (1 + (3 * m + 1) + (3 * m + 4) : ℕ) = 0 + (6 * m + 6) from by ring,
      show m + (3 * m + 4) + 1 = 4 * m + 5 from by ring]
  apply stepStar_trans (e_to_c (a := 4 * m + 5) (e := 0) (6 * m + 6) 0)
  ring_nf; finish

-- Odd case: n=2m+1, C(2m+1) = (4m+5, 0, 6m+6, 0, 0) ⊢⁺ C(2m+2) = (4m+7, 0, 6m+9, 0, 0)
theorem main_odd (m : ℕ) :
    ⟨4 * m + 5, 0, 6 * m + 6, 0, 0⟩ [fm]⊢⁺ ⟨4 * m + 7, 0, 6 * m + 9, 0, 0⟩ := by
  -- R5: (4m+5, 0, 6m+6, 0, 0) -> (4m+4, 1, 6m+6, 2, 1)
  rw [show 4 * m + 5 = (4 * m + 4) + 1 from by ring]
  step fm
  -- R1: (4m+4, 1, 6m+6, 2, 1) -> (4m+4, 0, 6m+5, 3, 1)
  rw [show 6 * m + 6 = (6 * m + 5) + 1 from by ring]
  step fm
  -- r3r1r1_chain with k = 3*m+2
  rw [show (4 * m + 4 : ℕ) = (m + 1) + (3 * m + 2) + 1 from by ring,
      show (6 * m + 5 : ℕ) = 1 + 2 * (3 * m + 2) from by ring,
      show (3 : ℕ) = 2 + 1 from by ring]
  apply stepStar_trans (r3r1r1_chain (3 * m + 2) (m + 1) 1 2 1)
  -- State: (m+2, 0, 1, 3m+5, 3m+3)
  -- Partial round: R3, R1, R2
  rw [show (2 + (3 * m + 2) + 1 : ℕ) = (3 * m + 4) + 1 from by ring,
      show (1 + (3 * m + 2) : ℕ) = 3 * m + 3 from by ring]
  step fm; step fm; step fm
  -- State: (m+1+1, 0, 0, 3*m+4+1, 3*m+3+1)
  rw [show (3 * m + 4 + 1 : ℕ) = 0 + (3 * m + 5) from by ring,
      show (m + 1 + 1 : ℕ) = (m + 1) + 1 from by ring]
  apply stepStar_trans (r3r2r2_chain (3 * m + 5) (m + 1) 0 (3 * m + 3 + 1))
  rw [show (3 * m + 3 + 1 + (3 * m + 5) : ℕ) = 0 + (6 * m + 9) from by ring,
      show (m + 1 + (3 * m + 5) + 1 : ℕ) = 4 * m + 7 from by ring]
  apply stepStar_trans (e_to_c (a := 4 * m + 7) (e := 0) (6 * m + 9) 0)
  ring_nf; finish

-- Combined transition: C(n) ⊢⁺ C(n+1)
theorem main_trans (n : ℕ) :
    ⟨2 * n + 3, 0, 3 * n + 3, 0, 0⟩ [fm]⊢⁺ ⟨2 * n + 5, 0, 3 * n + 6, 0, 0⟩ := by
  rcases Nat.even_or_odd n with ⟨m, hm⟩ | ⟨m, hm⟩
  · rw [show m + m = 2 * m from by ring] at hm; subst hm
    rw [show 2 * (2 * m) + 3 = 4 * m + 3 from by ring,
        show 3 * (2 * m) + 3 = 6 * m + 3 from by ring,
        show 2 * (2 * m) + 5 = 4 * m + 5 from by ring,
        show 3 * (2 * m) + 6 = 6 * m + 6 from by ring]
    exact main_even m
  · subst hm
    rw [show 2 * (2 * m + 1) + 3 = 4 * m + 5 from by ring,
        show 3 * (2 * m + 1) + 3 = 6 * m + 6 from by ring,
        show 2 * (2 * m + 1) + 5 = 4 * m + 7 from by ring,
        show 3 * (2 * m + 1) + 6 = 6 * m + 9 from by ring]
    exact main_odd m

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨3, 0, 3, 0, 0⟩)
  · execute fm 11
  apply progress_nonhalt_simple (fm := fm) (A := ℕ)
    (fun n ↦ ⟨2 * n + 3, 0, 3 * n + 3, 0, 0⟩) 0
  intro n; exact ⟨n + 1, main_trans n⟩

end Sz22_2003_unofficial_1424
