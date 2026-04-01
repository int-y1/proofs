import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #1549: [7/30, 55/3, 27/35, 2/11, 35/2]

Vector representation:
```
-1 -1 -1  1  0
 0 -1  1  0  1
 0  3 -1 -1  0
 1  0  0  0 -1
-1  0  1  1  0
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_1549

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a+1, b+1, c+1, d, e⟩ => some ⟨a, b, c, d+1, e⟩
  | ⟨a, b+1, c, d, e⟩ => some ⟨a, b, c+1, d, e+1⟩
  | ⟨a, b, c+1, d+1, e⟩ => some ⟨a, b+3, c, d, e⟩
  | ⟨a, b, c, d, e+1⟩ => some ⟨a+1, b, c, d, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b, c+1, d+1, e⟩
  | _ => none

-- R4 chain: transfer e to a.
theorem e_to_a : ∀ k a c, ⟨a, 0, c, 0, e + k⟩ [fm]⊢* ⟨a + k, 0, c, 0, e⟩ := by
  intro k; induction' k with k ih
  · intro a c; exists 0
  · intro a c; rw [show e + (k + 1) = (e + k) + 1 from by ring]
    step fm; apply stepStar_trans (ih (a + 1) c); ring_nf; finish

-- R1x3 + R3 repeated k times.
theorem inner_loop : ∀ k, ∀ a d, ⟨a + 3 * k + 1, 3, c + 4 * k + 1, d, 0⟩ [fm]⊢*
    ⟨a + 1, 3, c + 1, d + 2 * k, 0⟩ := by
  intro k; induction' k with k ih
  · intro a d; simp; exists 0
  · intro a d
    rw [show a + 3 * (k + 1) + 1 = (a + 3 * k + 1) + 1 + 1 + 1 from by ring,
        show (3 : ℕ) = 2 + 1 from rfl,
        show c + 4 * (k + 1) + 1 = (c + 4 * k + 1) + 1 + 1 + 1 + 1 from by ring]
    step fm; step fm; step fm
    rw [show (c + 4 * k + 1) + 1 = (c + 4 * k + 1 + 1) from by ring,
        show d + 1 + 1 + 1 = (d + 2) + 1 from by ring]
    step fm
    apply stepStar_trans (ih a (d + 2)); ring_nf; finish

-- Micro drain: R3,R2,R1,R2 repeated k times.
theorem micro_drain : ∀ k, ∀ d e, ⟨k, 0, 1, d + 1, e⟩ [fm]⊢*
    ⟨0, 0, 1, d + 1, e + 2 * k⟩ := by
  intro k; induction' k with k ih
  · intro d e; simp; exists 0
  · intro d e
    rw [show k + 1 = k + 1 from rfl,
        show (1 : ℕ) = 0 + 1 from rfl,
        show d + 1 = d + 1 from rfl]
    step fm; step fm; step fm; step fm
    apply stepStar_trans (ih d (e + 2)); ring_nf; finish

-- R3 + R2x3 chain repeated k+1 times.
theorem r3r2_chain : ∀ k, ∀ c e, ⟨0, 0, c + 1, k + 1, e⟩ [fm]⊢*
    ⟨0, 0, c + 2 * k + 3, 0, e + 3 * k + 3⟩ := by
  intro k; induction' k with k ih
  · intro c e; step fm; step fm; step fm; step fm; ring_nf; finish
  · intro c e
    rw [show (k + 1) + 1 = (k + 1) + 1 from rfl]
    step fm; step fm; step fm; step fm
    rw [show c + 1 + 1 + 1 = (c + 2) + 1 from by ring]
    apply stepStar_trans (ih (c + 2) (e + 3)); ring_nf; finish

-- Even transition: C = 12m+9, cleanup has c_end = 1.
theorem trans_even (m F : ℕ) :
    ⟨0, 0, 12 * m + 9, 0, 9 * m + F + 15⟩ [fm]⊢⁺
    ⟨0, 0, 12 * m + 15, 0, 18 * m + 2 * F + 33⟩ := by
  rw [show (9 * m + F + 15 : ℕ) = 0 + (9 * m + F + 15) from by ring]
  apply stepStar_stepPlus_stepPlus (e_to_a (9 * m + F + 15) 0 (12 * m + 9) (e := 0))
  rw [show 0 + (9 * m + F + 15) = 9 * m + F + 15 from by ring]
  rw [show 9 * m + F + 15 = (9 * m + F + 14) + 1 from by ring,
      show 12 * m + 9 = (12 * m + 8) + 0 + 1 from by ring]
  step fm
  rw [show (12 * m + 8) + 0 + 1 + 1 = (12 * m + 8) + 1 + 1 from by ring]
  step fm
  rw [show 9 * m + F + 14 = (F + 7) + 3 * (3 * m + 2) + 1 from by ring,
      show 12 * m + 8 + 1 = 0 + 4 * (3 * m + 2) + 1 from by ring]
  apply stepStar_trans (inner_loop (3 * m + 2) (F + 7) 0 (c := 0))
  rw [show 0 + 2 * (3 * m + 2) = 6 * m + 4 from by ring,
      show F + 7 + 1 = F + 8 from by ring,
      show (0 : ℕ) + 1 = 1 from by ring]
  rw [show F + 8 = (F + 7) + 1 from by ring,
      show (3 : ℕ) = 2 + 1 from rfl,
      show (1 : ℕ) = 0 + 1 from rfl]
  step fm
  rw [show (2 : ℕ) = 1 + 1 from rfl]
  step fm
  rw [show F + 7 = (F + 6) + 1 from by ring,
      show (1 : ℕ) = 0 + 1 from rfl,
      show (1 : ℕ) = 0 + 1 from rfl]
  step fm
  rw [show (1 : ℕ) = 0 + 1 from rfl]
  step fm
  rw [show F + 6 + 1 = (F + 6) + 1 from by ring]
  step fm
  rw [show 6 * m + 7 = (6 * m + 6) + 1 from by ring]
  apply stepStar_trans (micro_drain (F + 6) (6 * m + 6) 0)
  rw [show 0 + 2 * (F + 6) = 2 * F + 12 from by ring]
  rw [show (6 * m + 6) + 1 = (6 * m + 6) + 1 from rfl,
      show (1 : ℕ) = 0 + 1 from rfl]
  apply stepStar_trans (r3r2_chain (6 * m + 6) 0 (2 * F + 12))
  ring_nf; finish

-- Odd transition: C = 12m+15, cleanup has c_end = 3.
theorem trans_odd (m F : ℕ) :
    ⟨0, 0, 12 * m + 15, 0, 9 * m + F + 15⟩ [fm]⊢⁺
    ⟨0, 0, 12 * m + 21, 0, 18 * m + 2 * F + 32⟩ := by
  rw [show (9 * m + F + 15 : ℕ) = 0 + (9 * m + F + 15) from by ring]
  apply stepStar_stepPlus_stepPlus (e_to_a (9 * m + F + 15) 0 (12 * m + 15) (e := 0))
  rw [show 0 + (9 * m + F + 15) = 9 * m + F + 15 from by ring]
  rw [show 9 * m + F + 15 = (9 * m + F + 14) + 1 from by ring,
      show 12 * m + 15 = (12 * m + 14) + 0 + 1 from by ring]
  step fm
  rw [show (12 * m + 14) + 0 + 1 + 1 = (12 * m + 14) + 1 + 1 from by ring]
  step fm
  rw [show 9 * m + F + 14 = (F + 4) + 3 * (3 * m + 3) + 1 from by ring,
      show (12 * m + 14) + 1 = 2 + 4 * (3 * m + 3) + 1 from by ring]
  apply stepStar_trans (inner_loop (3 * m + 3) (F + 4) 0 (c := 2))
  rw [show 0 + 2 * (3 * m + 3) = 6 * m + 6 from by ring,
      show F + 4 + 1 = F + 5 from by ring,
      show (2 : ℕ) + 1 = 3 from by ring]
  rw [show F + 5 = (F + 4) + 1 from by ring]
  step fm
  rw [show F + 4 = (F + 3) + 1 from by ring]
  step fm
  rw [show F + 3 = (F + 2) + 1 from by ring]
  step fm
  rw [show F + 2 = (F + 1) + 1 from by ring]
  step fm
  rw [show 6 * m + 10 = (6 * m + 9) + 1 from by ring]
  apply stepStar_trans (micro_drain (F + 1) (6 * m + 9) 0)
  rw [show 0 + 2 * (F + 1) = 2 * F + 2 from by ring]
  rw [show (6 * m + 9) + 1 = (6 * m + 9) + 1 from rfl,
      show (1 : ℕ) = 0 + 1 from rfl]
  apply stepStar_trans (r3r2_chain (6 * m + 9) 0 (2 * F + 2))
  ring_nf; finish

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨0, 0, 12 * 0 + 9, 0, 9 * 0 + 0 + 15⟩)
  · execute fm 57
  apply progress_nonhalt (fm := fm)
    (P := fun q ↦
      (∃ m F, q = ⟨0, 0, 12 * m + 9, 0, 9 * m + F + 15⟩) ∨
      (∃ m F, q = ⟨0, 0, 12 * m + 15, 0, 9 * m + F + 15⟩))
  · intro q hq
    rcases hq with ⟨m, F, rfl⟩ | ⟨m, F, rfl⟩
    · refine ⟨⟨0, 0, 12 * m + 15, 0, 18 * m + 2 * F + 33⟩,
        Or.inr ⟨m, 9 * m + 2 * F + 18, by ring_nf⟩, ?_⟩
      exact trans_even m F
    · refine ⟨⟨0, 0, 12 * m + 21, 0, 18 * m + 2 * F + 32⟩,
        Or.inl ⟨m + 1, 9 * m + 2 * F + 8, by ring_nf⟩, ?_⟩
      exact trans_odd m F
  · exact Or.inl ⟨0, 0, by ring_nf⟩

end Sz22_2003_unofficial_1549
