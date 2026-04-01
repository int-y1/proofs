import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #1440: [7/15, 242/3, 3/77, 5/11, 63/2]

Vector representation:
```
 0 -1 -1  1  0
 1 -1  0  0  2
 0  1  0 -1 -1
 0  0  1  0 -1
-1  2  0  1  0
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_1440

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a, b+1, c+1, d, e⟩ => some ⟨a, b, c, d+1, e⟩
  | ⟨a, b+1, c, d, e⟩ => some ⟨a+1, b, c, d, e+2⟩
  | ⟨a, b, c, d+1, e+1⟩ => some ⟨a, b+1, c, d, e⟩
  | ⟨a, b, c, d, e+1⟩ => some ⟨a, b, c+1, d, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b+2, c, d+1, e⟩
  | _ => none

-- R4 chain: transfer e to c (when b=0, d=0)
theorem e_to_c : ∀ k c e, (⟨a, 0, c, 0, e + k⟩ : Q) [fm]⊢* ⟨a, 0, c + k, 0, e⟩ := by
  intro k; induction k with
  | zero => intro c e; exists 0
  | succ k ih =>
    intro c e
    rw [show e + (k + 1) = e + k + 1 from by ring]
    step fm
    apply stepStar_trans (ih (c + 1) e)
    ring_nf; finish

-- R5+R1+R1 chain: each round uses 1 a and 2 c, produces 3 d
theorem r5r1r1_chain : ∀ k a c d,
    (⟨a + k, 0, c + 2 * k, d, 0⟩ : Q) [fm]⊢* ⟨a, 0, c, d + 3 * k, 0⟩ := by
  intro k; induction k with
  | zero => intro a c d; ring_nf; finish
  | succ k ih =>
    intro a c d
    rw [show a + (k + 1) = (a + k) + 1 from by ring,
        show c + 2 * (k + 1) = (c + 2 * k) + 2 from by ring]
    step fm; step fm; step fm
    apply stepStar_trans (ih a c (d + 3))
    ring_nf; finish

-- Phase 3 even: when c=0, fire R5+R2+R2
theorem phase3_even : ∀ a d,
    (⟨a + 1, 0, 0, d, 0⟩ : Q) [fm]⊢* ⟨a + 2, 0, 0, d + 1, 4⟩ := by
  intro a d
  step fm; step fm; step fm
  ring_nf; finish

-- Phase 3 odd: when c=1, fire R5+R1+R2
theorem phase3_odd : ∀ a d,
    (⟨a + 1, 0, 1, d, 0⟩ : Q) [fm]⊢* ⟨a + 1, 0, 0, d + 2, 2⟩ := by
  intro a d
  step fm; step fm; step fm
  ring_nf; finish

-- R3+R2 micro-step
theorem r3r2_step (a d e : ℕ) :
    (⟨a, 0, 0, d + 1, e + 1⟩ : Q) [fm]⊢⁺ ⟨a + 1, 0, 0, d, e + 2⟩ := by
  step fm; step fm; finish

-- R3+R2 chain
theorem r3r2_chain : ∀ k a d e,
    (⟨a, 0, 0, d + k, e + 1⟩ : Q) [fm]⊢* ⟨a + k, 0, 0, d, e + k + 1⟩ := by
  intro k; induction k with
  | zero => intro a d e; exists 0
  | succ k ih =>
    intro a d e
    rw [show d + (k + 1) = (d + k) + 1 from by ring]
    step fm; step fm
    apply stepStar_trans (ih (a + 1) d (e + 1))
    ring_nf; finish

-- Phases 1+2+3 for even e=2m
theorem phases123_even (a m : ℕ) :
    (⟨a + m + 1, 0, 0, 0, 2 * m⟩ : Q) [fm]⊢* ⟨a + 2, 0, 0, 3 * m + 1, 4⟩ := by
  -- Phase 1: R4 chain
  rw [show (2 * m : ℕ) = 0 + 2 * m from by ring]
  apply stepStar_trans (e_to_c (2 * m) 0 0 (a := a + m + 1))
  rw [show 0 + 2 * m = 2 * m from by ring]
  -- Phase 2: R5/R1/R1 chain
  rw [show a + m + 1 = (a + 1) + m from by ring,
      show 2 * m = 0 + 2 * m from by ring]
  apply stepStar_trans (r5r1r1_chain m (a + 1) 0 0)
  rw [show 0 + 3 * m = 3 * m from by ring]
  -- Phase 3: R5+R2+R2
  exact phase3_even a (3 * m)

-- Phases 1+2+3 for odd e=2m+1
theorem phases123_odd (a m : ℕ) :
    (⟨a + m + 1, 0, 0, 0, 2 * m + 1⟩ : Q) [fm]⊢* ⟨a + 1, 0, 0, 3 * m + 2, 2⟩ := by
  -- Phase 1: R4 chain
  rw [show (2 * m + 1 : ℕ) = 0 + (2 * m + 1) from by ring]
  apply stepStar_trans (e_to_c (2 * m + 1) 0 0 (a := a + m + 1))
  rw [show 0 + (2 * m + 1) = 2 * m + 1 from by ring]
  -- Phase 2: R5/R1/R1 chain
  rw [show a + m + 1 = (a + 1) + m from by ring,
      show 2 * m + 1 = 1 + 2 * m from by ring]
  apply stepStar_trans (r5r1r1_chain m (a + 1) 1 0)
  rw [show 0 + 3 * m = 3 * m from by ring]
  -- Phase 3: R5+R1+R2
  exact phase3_odd a (3 * m)

-- Even transition: (a+m+1, 0, 0, 0, 2m) ⊢⁺ (a+3m+3, 0, 0, 0, 3m+5)
theorem main_even (a m : ℕ) :
    (⟨a + m + 1, 0, 0, 0, 2 * m⟩ : Q) [fm]⊢⁺ ⟨a + 3 * m + 3, 0, 0, 0, 3 * m + 5⟩ := by
  apply stepStar_stepPlus_stepPlus (phases123_even a m)
  -- State: (a+2, 0, 0, 3m+1, 4). First R3+R2 step.
  rw [show 3 * m + 1 = 0 + (3 * m) + 1 from by ring,
      show (4 : ℕ) = 3 + 1 from by ring]
  apply stepPlus_stepStar_stepPlus (r3r2_step (a + 2) (0 + 3 * m) 3)
  -- State: (a+3, 0, 0, 3m, 5). Remaining 3m pairs.
  rw [show 0 + 3 * m = 3 * m from by ring,
      show a + 2 + 1 = a + 3 from by ring,
      show 3 + 2 = 4 + 1 from by ring,
      show 3 * m = 0 + 3 * m from by ring]
  apply stepStar_trans (r3r2_chain (3 * m) (a + 3) 0 4)
  ring_nf; finish

-- Odd transition: (a+m+1, 0, 0, 0, 2m+1) ⊢⁺ (a+3m+3, 0, 0, 0, 3m+4)
theorem main_odd (a m : ℕ) :
    (⟨a + m + 1, 0, 0, 0, 2 * m + 1⟩ : Q) [fm]⊢⁺ ⟨a + 3 * m + 3, 0, 0, 0, 3 * m + 4⟩ := by
  apply stepStar_stepPlus_stepPlus (phases123_odd a m)
  -- State: (a+1, 0, 0, 3m+2, 2). First R3+R2 step.
  rw [show 3 * m + 2 = 0 + (3 * m + 1) + 1 from by ring,
      show (2 : ℕ) = 1 + 1 from by ring]
  apply stepPlus_stepStar_stepPlus (r3r2_step (a + 1) (0 + 3 * m + 1) 1)
  -- State: (a+2, 0, 0, 3m+1, 3). Remaining 3m+1 pairs.
  rw [show 0 + 3 * m + 1 = 3 * m + 1 from by ring,
      show a + 1 + 1 = a + 2 from by ring,
      show 1 + 2 = 2 + 1 from by ring,
      show 3 * m + 1 = 0 + (3 * m + 1) from by ring]
  apply stepStar_trans (r3r2_chain (3 * m + 1) (a + 2) 0 2)
  ring_nf; finish

theorem nonhalt : ¬halts fm c₀ := by
  apply progress_nonhalt (fm := fm)
    (P := fun q ↦ ∃ a e, q = ⟨a, 0, 0, 0, e⟩ ∧ 2 * a ≥ e + 1)
  · intro q ⟨a, e, hq, hae⟩; subst hq
    rcases Nat.even_or_odd e with ⟨m, hm⟩ | ⟨m, hm⟩
    · -- e = 2m (even)
      rw [show m + m = 2 * m from by ring] at hm; subst hm
      obtain ⟨a', rfl⟩ : ∃ a', a = a' + m + 1 := ⟨a - m - 1, by omega⟩
      exact ⟨⟨a' + 3 * m + 3, 0, 0, 0, 3 * m + 5⟩,
        ⟨a' + 3 * m + 3, 3 * m + 5, rfl, by omega⟩,
        main_even a' m⟩
    · -- e = 2m+1 (odd)
      subst hm
      obtain ⟨a', rfl⟩ : ∃ a', a = a' + m + 1 := ⟨a - m - 1, by omega⟩
      exact ⟨⟨a' + 3 * m + 3, 0, 0, 0, 3 * m + 4⟩,
        ⟨a' + 3 * m + 3, 3 * m + 4, rfl, by omega⟩,
        main_odd a' m⟩
  · exact ⟨1, 0, rfl, by omega⟩

end Sz22_2003_unofficial_1440
