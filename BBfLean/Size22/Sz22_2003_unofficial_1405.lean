import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #1405: [7/15, 1089/14, 4/3, 5/11, 21/2]

Vector representation:
```
 0 -1 -1  1  0
-1  2  0 -1  2
 2 -1  0  0  0
 0  0  1  0 -1
-1  1  0  1  0
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_1405

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a, b+1, c+1, d, e⟩ => some ⟨a, b, c, d+1, e⟩
  | ⟨a+1, b, c, d+1, e⟩ => some ⟨a, b+2, c, d, e+2⟩
  | ⟨a, b+1, c, d, e⟩ => some ⟨a+2, b, c, d, e⟩
  | ⟨a, b, c, d, e+1⟩ => some ⟨a, b, c+1, d, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b+1, c, d+1, e⟩
  | _ => none

-- R4: transfer e to c
theorem e_to_c : ∀ k a c e, (⟨a, 0, c, 0, e + k⟩ : Q) [fm]⊢* ⟨a, 0, c + k, 0, e⟩ := by
  intro k; induction k with
  | zero => intro a c e; exists 0
  | succ k ih =>
    intro a c e
    rw [show e + (k + 1) = (e + k) + 1 from by ring]
    step fm
    apply stepStar_trans (ih a (c + 1) e)
    ring_nf; finish

-- R3: transfer b to a (doubling)
theorem r3_chain : ∀ k a b e, (⟨a, b + k, 0, 0, e⟩ : Q) [fm]⊢* ⟨a + 2 * k, b, 0, 0, e⟩ := by
  intro k; induction k with
  | zero => intro a b e; exists 0
  | succ k ih =>
    intro a b e
    rw [show b + (k + 1) = (b + k) + 1 from by ring]
    step fm
    apply stepStar_trans (ih (a + 2) b e)
    ring_nf; finish

-- R2: drain a and d to b and e (c must be 0 so R1 doesn't fire)
theorem r2_chain : ∀ k a b d e, (⟨a + k, b, 0, d + k, e⟩ : Q) [fm]⊢* ⟨a, b + 2 * k, 0, d, e + 2 * k⟩ := by
  intro k; induction k with
  | zero => intro a b d e; exists 0
  | succ k ih =>
    intro a b d e
    rw [show a + (k + 1) = (a + k) + 1 from by ring,
        show d + (k + 1) = (d + k) + 1 from by ring]
    step fm
    apply stepStar_trans (ih a (b + 2) d (e + 2))
    ring_nf; finish

-- R1R1R2 loop: each round does R1,R1,R2 consuming 2 from c and 1 from a
theorem r1r1r2_loop : ∀ k a d e, (⟨a + k, 2, 2 * k + 1, d, e⟩ : Q) [fm]⊢* ⟨a, 2, 1, d + k, e + 2 * k⟩ := by
  intro k; induction k with
  | zero => intro a d e; exists 0
  | succ k ih =>
    intro a d e
    rw [show a + (k + 1) = (a + k) + 1 from by ring,
        show 2 * (k + 1) + 1 = (2 * k + 1) + 2 from by ring]
    rw [show (2 * k + 1) + 2 = (2 * k + 2) + 1 from by ring]
    step fm -- R1
    rw [show 2 * k + 2 = (2 * k + 1) + 1 from by ring]
    step fm -- R1
    rw [show (a + k) + 1 = a + k + 1 from by ring,
        show d + 2 = (d + 1) + 1 from by ring]
    step fm -- R2
    apply stepStar_trans (ih a (d + 1) (e + 2))
    ring_nf; finish

-- Main transition for E >= 1
theorem main_trans_succ (D E : ℕ) :
    (⟨2 * E + D + 4, 0, 0, 0, 2 * E + 2⟩ : Q) [fm]⊢⁺ ⟨4 * E + D + 10, 0, 0, 0, 4 * E + 6⟩ := by
  -- R4 chain: e_to_c with k = 2*E+2
  apply stepStar_stepPlus_stepPlus
  · rw [show (0 : ℕ) = 0 + 0 from by ring,
        show 2 * E + 2 = 0 + (2 * E + 2) from by ring]
    exact e_to_c (2 * E + 2) (2 * E + D + 4) 0 0
  -- Now at (2*E+D+4, 0, 2*E+2, 0, 0)
  -- R5: (2*E+D+3, 1, 2*E+2, 1, 0)
  rw [show 0 + (2 * E + 2) = (2 * E + 1) + 1 from by ring,
      show 2 * E + D + 4 = (2 * E + D + 3) + 1 from by ring]
  step fm
  -- R1: (2*E+D+3, 0, 2*E+1, 2, 0)
  step fm
  -- R2: (2*E+D+2, 2, 2*E+1, 1, 2)
  rw [show 2 * E + D + 3 = (2 * E + D + 2) + 1 from by ring,
      show (2 : ℕ) = 1 + 1 from by ring]
  step fm
  -- R1R1R2 loop: E rounds with k=E, a=D+E+2
  rw [show 2 * E + D + 2 = (D + E + 2) + E from by ring]
  apply stepStar_trans (r1r1r2_loop E (D + E + 2) 1 2)
  -- Now at (D+E+2, 2, 1, E+1, 2*E+2)
  -- R1: (D+E+2, 1, 0, E+2, 2*E+2)
  rw [show 1 + E = E + 1 from by ring, show 2 + 2 * E = 2 * E + 2 from by ring]
  step fm
  -- R2 chain + R3 chain combined
  have hr2 := r2_chain (E + 2) D 1 0 (2 * E + 2)
  simp only [Nat.zero_add] at hr2
  rw [show 1 + 2 * (E + 2) = 2 * E + 5 from by ring,
      show 2 * E + 2 + 2 * (E + 2) = 4 * E + 6 from by ring] at hr2
  have hr3 := r3_chain (2 * E + 5) D 0 (4 * E + 6)
  rw [show D + 2 * (2 * E + 5) = 4 * E + D + 10 from by ring,
      show 0 + (2 * E + 5) = 2 * E + 5 from by ring] at hr3
  rw [show E + 1 + 1 = E + 2 from by ring,
      show D + E + 2 = D + (E + 2) from by ring]
  exact stepStar_trans hr2 hr3

-- Main transition for E = 0: from (D+2, 0, 0, 0, 0) to (D+6, 0, 0, 0, 2)
theorem main_trans_zero (D : ℕ) :
    (⟨D + 2, 0, 0, 0, 0⟩ : Q) [fm]⊢⁺ ⟨D + 6, 0, 0, 0, 2⟩ := by
  -- R5: (D+1, 1, 0, 1, 0)
  rw [show D + 2 = (D + 1) + 1 from by ring]
  step fm
  -- R2: (D, 3, 0, 0, 2)
  step fm
  -- R3 x3: (D+6, 0, 0, 0, 2)
  rw [show (3 : ℕ) = 0 + 3 from by ring]
  apply stepStar_trans (r3_chain 3 D 0 2)
  rw [show D + 2 * 3 = D + 6 from by ring]
  finish

-- Combined main transition
theorem main_trans (D E : ℕ) :
    (⟨2 * E + D + 2, 0, 0, 0, 2 * E⟩ : Q) [fm]⊢⁺ ⟨4 * E + D + 6, 0, 0, 0, 4 * E + 2⟩ := by
  rcases E with _ | E
  · -- E = 0
    rw [show 2 * 0 + D + 2 = D + 2 from by ring,
        show 4 * 0 + D + 6 = D + 6 from by ring,
        show 4 * 0 + 2 = 2 from by ring,
        show 2 * 0 = 0 from by ring]
    exact main_trans_zero D
  · -- E = E + 1
    rw [show 2 * (E + 1) + D + 2 = 2 * E + D + 4 from by ring,
        show 2 * (E + 1) = 2 * E + 2 from by ring,
        show 4 * (E + 1) + D + 6 = 4 * E + D + 10 from by ring,
        show 4 * (E + 1) + 2 = 4 * E + 6 from by ring]
    exact main_trans_succ D E

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨5, 0, 0, 0, 2⟩) (by execute fm 5)
  apply progress_nonhalt_simple (fm := fm) (A := ℕ × ℕ)
    (fun ⟨D, E⟩ ↦ ⟨2 * E + D + 2, 0, 0, 0, 2 * E⟩) ⟨1, 1⟩
  intro ⟨D, E⟩
  exact ⟨⟨D + 2, 2 * E + 1⟩, by
    show (⟨2 * E + D + 2, 0, 0, 0, 2 * E⟩ : Q) [fm]⊢⁺ ⟨2 * (2 * E + 1) + (D + 2) + 2, 0, 0, 0, 2 * (2 * E + 1)⟩
    rw [show 2 * (2 * E + 1) + (D + 2) + 2 = 4 * E + D + 6 from by ring,
        show 2 * (2 * E + 1) = 4 * E + 2 from by ring]
    exact main_trans D E⟩

end Sz22_2003_unofficial_1405
