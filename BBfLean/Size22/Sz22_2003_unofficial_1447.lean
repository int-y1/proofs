import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #1447: [7/15, 242/3, 9/77, 5/121, 21/2]

Vector representation:
```
 0 -1 -1  1  0
 1 -1  0  0  2
 0  2  0 -1 -1
 0  0  1  0 -2
-1  1  0  1  0
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_1447

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a, b+1, c+1, d, e⟩ => some ⟨a, b, c, d+1, e⟩
  | ⟨a, b+1, c, d, e⟩ => some ⟨a+1, b, c, d, e+2⟩
  | ⟨a, b, c, d+1, e+1⟩ => some ⟨a, b+2, c, d, e⟩
  | ⟨a, b, c, d, e+2⟩ => some ⟨a, b, c+1, d, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b+1, c, d+1, e⟩
  | _ => none

-- R3+R2+R2 chain: each round consumes 1 from d, adds 2 to a, adds 3 to e.
theorem r3r2r2_chain : ∀ k, ∀ a d e, (⟨a, 0, 0, d + k, e + 1⟩ : Q) [fm]⊢*
    ⟨a + 2 * k, 0, 0, d, e + 3 * k + 1⟩ := by
  intro k; induction k with
  | zero => intro a d e; ring_nf; finish
  | succ k ih =>
    intro a d e
    rw [show d + (k + 1) = (d + k) + 1 from by ring]
    step fm; step fm; step fm
    apply stepStar_trans (ih (a + 2) d (e + 3)); ring_nf; finish

-- R4 chain: transfer e to c in pairs.
theorem e_to_c : ∀ k, ∀ c e, (⟨a, 0, c, 0, e + 2 * k⟩ : Q) [fm]⊢*
    ⟨a, 0, c + k, 0, e⟩ := by
  intro k; induction k with
  | zero => intro c e; ring_nf; finish
  | succ k ih =>
    intro c e
    rw [show e + 2 * (k + 1) = e + 2 * k + 2 from by ring]
    step fm
    apply stepStar_trans (ih (c + 1) e); ring_nf; finish

-- R5+R1 drain chain: each pair consumes 1 from a and c, adds 2 to d.
theorem r5r1_drain : ∀ k, ∀ a c d, (⟨a + k, 0, c + k, d, 0⟩ : Q) [fm]⊢*
    ⟨a, 0, c, d + 2 * k, 0⟩ := by
  intro k; induction k with
  | zero => intro a c d; ring_nf; finish
  | succ k ih =>
    intro a c d
    rw [show a + (k + 1) = (a + k) + 1 from by ring,
        show c + (k + 1) = (c + k) + 1 from by ring]
    step fm; step fm
    apply stepStar_trans (ih a c (d + 2)); ring_nf; finish

-- Even case: d = 2m, m ≥ 1.
-- (a+1, 0, 0, 2m, 0) ⊢⁺ (a + m + 3, 0, 0, 6m + 1, 0)
theorem main_even (a m : ℕ) (hm : m ≥ 1) :
    (⟨a + 1, 0, 0, 2 * m, 0⟩ : Q) [fm]⊢⁺ ⟨a + m + 3, 0, 0, 6 * m + 1, 0⟩ := by
  -- Phase 1: R5+R2 (2 steps). Rewrite d so step fm can see it.
  rw [show 2 * m = (2 * m - 1) + 1 from by omega]
  step fm; step fm
  -- State: (a+1, 0, 0, 2m+1, 2)
  rw [show 2 * m - 1 + 1 + 1 = 0 + (2 * m + 1) from by omega,
      show (2 : ℕ) = 0 + 1 + 1 from by ring]
  -- Phase 2: R3+R2+R2 chain (2m+1 rounds)
  apply stepStar_trans (r3r2r2_chain (2 * m + 1) (a + 1) 0 (0 + 1))
  -- Phase 3: R4 chain (3m+2 pairs), leaving e=1
  rw [show a + 1 + 2 * (2 * m + 1) = a + 4 * m + 3 from by ring,
      show 0 + 1 + 3 * (2 * m + 1) + 1 = 1 + 2 * (3 * m + 2) from by ring]
  apply stepStar_trans (e_to_c (3 * m + 2) 0 1 (a := a + 4 * m + 3))
  -- State: (a+4m+3, 0, 3m+2, 0, 1)
  rw [show a + 4 * m + 3 = (a + m + 3) + (3 * m - 1) + 1 from by omega,
      show 3 * m + 2 = (3 * m - 1) + 2 + 1 from by omega]
  -- Phase 4a: 5 setup steps (R5, R1, R3, R1, R1)
  step fm; step fm; step fm; step fm; step fm
  -- State: (a+4m+2, 0, 3m-1, 3, 0)
  apply stepStar_trans (r5r1_drain (3 * m - 1) (a + m + 3) 0 3)
  rw [show 3 + 2 * (3 * m - 1) = 6 * m + 1 from by omega]
  finish

-- Odd case: d = 2m + 1.
-- (a+1, 0, 0, 2m+1, 0) ⊢⁺ (a + m + 1, 0, 0, 6m + 8, 0)
theorem main_odd (a m : ℕ) :
    (⟨a + 1, 0, 0, 2 * m + 1, 0⟩ : Q) [fm]⊢⁺ ⟨a + m + 1, 0, 0, 6 * m + 8, 0⟩ := by
  -- Phase 1: R5+R2 (2 steps)
  step fm; step fm
  -- State: (a+1, 0, 0, 2m+2, 2)
  rw [show 2 * m + 2 = 0 + (2 * m + 2) from by ring,
      show (2 : ℕ) = 0 + 1 + 1 from by ring]
  -- Phase 2: R3+R2+R2 chain (2m+2 rounds)
  apply stepStar_trans (r3r2r2_chain (2 * m + 2) (a + 1) 0 (0 + 1))
  -- Phase 3: R4 chain (3m+4 pairs), leaving e=0
  rw [show a + 1 + 2 * (2 * m + 2) = a + 4 * m + 5 from by ring,
      show 0 + 1 + 3 * (2 * m + 2) + 1 = 0 + 2 * (3 * m + 4) from by ring]
  apply stepStar_trans (e_to_c (3 * m + 4) 0 0 (a := a + 4 * m + 5))
  -- State: (a+4m+5, 0, 3m+4, 0, 0)
  rw [show a + 4 * m + 5 = (a + m + 1) + (3 * m + 3) + 1 from by ring,
      show 3 * m + 4 = (3 * m + 3) + 1 from by ring]
  -- Phase 4b: R5+R1 then drain
  step fm; step fm
  apply stepStar_trans (r5r1_drain (3 * m + 3) (a + m + 1) 0 2)
  rw [show 2 + 2 * (3 * m + 3) = 6 * m + 8 from by ring]
  finish

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨3, 0, 0, 8, 0⟩) (by execute fm 30)
  apply progress_nonhalt (fm := fm)
    (P := fun q ↦ ∃ a d, q = ⟨a + 1, 0, 0, d, 0⟩ ∧ d ≥ 1)
  · intro q ⟨a, d, hq, hd⟩; subst hq
    rcases Nat.even_or_odd d with ⟨k, hk⟩ | ⟨k, hk⟩
    · rw [show k + k = 2 * k from by ring] at hk; subst hk
      have hk1 : k ≥ 1 := by omega
      exact ⟨⟨a + k + 3, 0, 0, 6 * k + 1, 0⟩,
        ⟨a + k + 2, 6 * k + 1, by ring_nf, by omega⟩,
        main_even a k hk1⟩
    · subst hk
      exact ⟨⟨a + k + 1, 0, 0, 6 * k + 8, 0⟩,
        ⟨a + k, 6 * k + 8, by ring_nf, by omega⟩,
        main_odd a k⟩
  · exact ⟨2, 8, by ring_nf, by omega⟩

end Sz22_2003_unofficial_1447
