import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #1443: [7/15, 242/3, 9/77, 5/11, 539/2]

Vector representation:
```
 0 -1 -1  1  0
 1 -1  0  0  2
 0  2  0 -1 -1
 0  0  1  0 -1
-1  0  0  2  1
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_1443

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a, b+1, c+1, d, e⟩ => some ⟨a, b, c, d+1, e⟩
  | ⟨a, b+1, c, d, e⟩ => some ⟨a+1, b, c, d, e+2⟩
  | ⟨a, b, c, d+1, e+1⟩ => some ⟨a, b+2, c, d, e⟩
  | ⟨a, b, c, d, e+1⟩ => some ⟨a, b, c+1, d, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b, c, d+2, e+1⟩
  | _ => none

-- R4 chain: transfer e to c (when b=0, d=0)
theorem e_to_c : ∀ k, ∀ a c e, (⟨a, 0, c, 0, k + e⟩ : Q) [fm]⊢* ⟨a, 0, c + k, 0, e⟩ := by
  intro k; induction k with
  | zero => intro a c e; ring_nf; finish
  | succ k ih =>
    intro a c e
    rw [show k + 1 + e = k + (e + 1) from by ring]
    step fm
    apply stepStar_trans (ih a (c + 1) e); ring_nf; finish

-- Drain chain: (R5, R3, R1, R1) repeated, consuming a and c, producing d
theorem drain : ∀ k, ∀ a c d, (⟨a + k, 0, c + 2 * k, d, 0⟩ : Q) [fm]⊢* ⟨a, 0, c, d + 3 * k, 0⟩ := by
  intro k; induction k with
  | zero => intro a c d; ring_nf; finish
  | succ k ih =>
    intro a c d
    rw [show a + (k + 1) = (a + k) + 1 from by ring,
        show c + 2 * (k + 1) = (c + 2 * k) + 2 from by ring]
    step fm; step fm; step fm; step fm
    apply stepStar_trans (ih a c (d + 3)); ring_nf; finish

-- R3/R2/R2 chain: when b=0, c=0, d >= 1, e >= 1
theorem r3r2r2 : ∀ k, ∀ a d e, (⟨a, 0, 0, d + k, e + 1⟩ : Q) [fm]⊢* ⟨a + 2 * k, 0, 0, d, e + 3 * k + 1⟩ := by
  intro k; induction k with
  | zero => intro a d e; ring_nf; finish
  | succ k ih =>
    intro a d e
    rw [show d + (k + 1) = (d + k) + 1 from by ring]
    step fm; step fm; step fm
    apply stepStar_trans (ih (a + 2) d (e + 3)); ring_nf; finish

-- Transition for odd case: (a+1, 0, 1, d, 0) -> (a+1, 0, 0, d+2, 2)
theorem trans_odd : (⟨a + 1, 0, 1, d, 0⟩ : Q) [fm]⊢* ⟨a + 1, 0, 0, d + 2, 2⟩ := by
  step fm; step fm; step fm; step fm; ring_nf; finish

-- Main odd transition: from (a, 0, 0, 0, 2*m+1) with a >= m+1
theorem main_odd (a m : ℕ) (ha : a ≥ m + 1) :
    (⟨a, 0, 0, 0, 2 * m + 1⟩ : Q) [fm]⊢⁺ ⟨a + 5 * m + 4, 0, 0, 0, 9 * m + 8⟩ := by
  -- Phase 1: e_to_c
  have h1 : (⟨a, 0, 0, 0, 2 * m + 1⟩ : Q) [fm]⊢⁺ ⟨a, 0, 2 * m + 1, 0, 0⟩ := by
    rw [show 2 * m + 1 = (2 * m + 1) + 0 from by ring]
    step fm
    apply stepStar_trans (e_to_c (2 * m) 1 (a := a) (e := 0))
    ring_nf; finish
  -- Phase 2: drain m rounds
  have h2 : (⟨a, 0, 2 * m + 1, 0, 0⟩ : Q) [fm]⊢* ⟨a - m, 0, 1, 3 * m, 0⟩ := by
    have := drain m (a - m) 1 0
    rw [show 0 + 3 * m = 3 * m from by ring,
        show a - m + m = a from by omega,
        show 1 + 2 * m = 2 * m + 1 from by ring] at this
    exact this
  -- Phase 3: transition odd
  have h3 : (⟨a - m, 0, 1, 3 * m, 0⟩ : Q) [fm]⊢* ⟨a - m, 0, 0, 3 * m + 2, 2⟩ := by
    rw [show a - m = (a - m - 1) + 1 from by omega]
    exact trans_odd (a := a - m - 1) (d := 3 * m)
  -- Phase 4: r3r2r2 chain
  have h4 : (⟨a - m, 0, 0, 3 * m + 2, 2⟩ : Q) [fm]⊢* ⟨a + 5 * m + 4, 0, 0, 0, 9 * m + 8⟩ := by
    rw [show 3 * m + 2 = 0 + (3 * m + 2) from by ring,
        show (2 : ℕ) = 1 + 1 from rfl]
    apply stepStar_trans (r3r2r2 (3 * m + 2) (a - m) 0 1)
    rw [show a - m + 2 * (3 * m + 2) = a + 5 * m + 4 from by omega,
        show 1 + 3 * (3 * m + 2) + 1 = 9 * m + 8 from by ring]
    finish
  exact stepPlus_stepStar_stepPlus h1 (stepStar_trans h2 (stepStar_trans h3 h4))

-- Main even transition: from (a, 0, 0, 0, 2*(m+1)) with a >= m+2
theorem main_even (a m : ℕ) (ha : a ≥ m + 2) :
    (⟨a, 0, 0, 0, 2 * (m + 1)⟩ : Q) [fm]⊢⁺ ⟨a + 5 * m + 8, 0, 0, 0, 9 * m + 16⟩ := by
  -- Phase 1: e_to_c
  have h1 : (⟨a, 0, 0, 0, 2 * (m + 1)⟩ : Q) [fm]⊢⁺ ⟨a, 0, 2 * (m + 1), 0, 0⟩ := by
    rw [show 2 * (m + 1) = (2 * (m + 1)) + 0 from by ring]
    step fm
    apply stepStar_trans (e_to_c (2 * m + 1) 1 (a := a) (e := 0))
    ring_nf; finish
  -- Phase 2: drain (m+1) rounds
  have h2 : (⟨a, 0, 2 * (m + 1), 0, 0⟩ : Q) [fm]⊢* ⟨a - (m + 1), 0, 0, 3 * (m + 1), 0⟩ := by
    have := drain (m + 1) (a - (m + 1)) 0 0
    rw [show 0 + 3 * (m + 1) = 3 * (m + 1) from by ring,
        show a - (m + 1) + (m + 1) = a from by omega,
        show 0 + 2 * (m + 1) = 2 * (m + 1) from by ring] at this
    exact this
  -- Phase 3: R5 step
  have h3 : (⟨a - (m + 1), 0, 0, 3 * (m + 1), 0⟩ : Q) [fm]⊢* ⟨a - (m + 2), 0, 0, 3 * m + 5, 1⟩ := by
    rw [show a - (m + 1) = (a - (m + 2)) + 1 from by omega,
        show 3 * (m + 1) = 3 * m + 3 from by ring]
    step fm; ring_nf; finish
  -- Phase 4: r3r2r2 chain
  have h4 : (⟨a - (m + 2), 0, 0, 3 * m + 5, 1⟩ : Q) [fm]⊢* ⟨a + 5 * m + 8, 0, 0, 0, 9 * m + 16⟩ := by
    rw [show 3 * m + 5 = 0 + (3 * m + 5) from by ring,
        show (1 : ℕ) = 0 + 1 from rfl]
    apply stepStar_trans (r3r2r2 (3 * m + 5) (a - (m + 2)) 0 0)
    rw [show a - (m + 2) + 2 * (3 * m + 5) = a + 5 * m + 8 from by omega,
        show 0 + 3 * (3 * m + 5) + 1 = 9 * m + 16 from by ring]
    finish
  exact stepPlus_stepStar_stepPlus h1 (stepStar_trans h2 (stepStar_trans h3 h4))

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨4, 0, 0, 0, 7⟩) (by execute fm 7)
  apply progress_nonhalt (fm := fm)
    (P := fun q ↦ ∃ a e, q = ⟨a, 0, 0, 0, e⟩ ∧ e ≥ 1 ∧ 2 * a ≥ e + 1)
  · intro q ⟨a, e, hq, he, ha⟩; subst hq
    rcases Nat.even_or_odd e with ⟨k, hk⟩ | ⟨k, hk⟩
    · -- e even: e = 2k, k >= 1 since e >= 1 and e even means e >= 2
      rw [show k + k = 2 * k from by ring] at hk; subst hk
      have hk1 : k ≥ 1 := by omega
      rw [show 2 * k = 2 * ((k - 1) + 1) from by omega]
      refine ⟨⟨a + 5 * (k - 1) + 8, 0, 0, 0, 9 * (k - 1) + 16⟩,
        ⟨a + 5 * (k - 1) + 8, 9 * (k - 1) + 16, rfl, by omega, by omega⟩,
        main_even a (k - 1) (by omega)⟩
    · -- e odd: e = 2k + 1
      subst hk
      refine ⟨⟨a + 5 * k + 4, 0, 0, 0, 9 * k + 8⟩,
        ⟨a + 5 * k + 4, 9 * k + 8, rfl, by omega, by omega⟩,
        main_odd a k (by omega)⟩
  · exact ⟨4, 7, rfl, by omega, by omega⟩

end Sz22_2003_unofficial_1443
