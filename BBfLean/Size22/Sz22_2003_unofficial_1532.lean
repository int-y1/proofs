import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #1532: [7/30, 22/3, 27/35, 5/11, 35/2]

Vector representation:
```
-1 -1 -1  1  0
 1 -1  0  0  1
 0  3 -1 -1  0
 0  0  1  0 -1
-1  0  1  1  0
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_1532

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a+1, b+1, c+1, d, e⟩ => some ⟨a, b, c, d+1, e⟩
  | ⟨a, b+1, c, d, e⟩ => some ⟨a+1, b, c, d, e+1⟩
  | ⟨a, b, c+1, d+1, e⟩ => some ⟨a, b+3, c, d, e⟩
  | ⟨a, b, c, d, e+1⟩ => some ⟨a, b, c+1, d, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b, c+1, d+1, e⟩
  | _ => none

-- One round of inner loop: R3 then 3×R1.
-- (a+3, 0, c+4, d+1, 0) -> (a, 0, c, d+3, 0)
theorem inner_step (a c d : ℕ) :
    ⟨a + 3, 0, c + 4, d + 1, 0⟩ [fm]⊢* ⟨a, 0, c, d + 3, 0⟩ := by
  rw [show c + 4 = (c + 3) + 1 from by ring,
      show a + 3 = (a + 2) + 1 from by ring]
  step fm
  rw [show (3 : ℕ) = 2 + 1 from rfl,
      show c + 3 = (c + 2) + 1 from by ring]
  step fm
  rw [show c + 2 = (c + 1) + 1 from by ring]
  step fm
  rw [show c + 1 = c + 1 from rfl]
  step fm
  ring_nf; finish

-- Inner loop: repeated inner_step, k times.
theorem inner_loop : ∀ k, ∀ c_rem a d,
    ⟨a + 3 * k, 0, c_rem + 4 * k, d + 1, 0⟩ [fm]⊢*
    ⟨a, 0, c_rem, d + 2 * k + 1, 0⟩ := by
  intro k; induction' k with k ih <;> intro c_rem a d
  · exists 0
  · rw [show a + 3 * (k + 1) = (a + 3 * k) + 3 from by ring,
        show c_rem + 4 * (k + 1) = (c_rem + 4 * k) + 4 from by ring]
    apply stepStar_trans (inner_step (a + 3 * k) (c_rem + 4 * k) d)
    rw [show d + 3 = (d + 2) + 1 from by ring]
    apply stepStar_trans (ih c_rem a (d + 2))
    ring_nf; finish

-- One round of d-drain: R3, 3×R2, R4.
-- (a, 0, 1, d+2, e) -> (a+3, 0, 1, d+1, e+2)
theorem drain_step (a d e : ℕ) :
    ⟨a, 0, 1, d + 2, e⟩ [fm]⊢* ⟨a + 3, 0, 1, d + 1, e + 2⟩ := by
  rw [show d + 2 = (d + 1) + 1 from by ring,
      show (1 : ℕ) = 0 + 1 from rfl]
  step fm
  rw [show (3 : ℕ) = 2 + 1 from rfl]
  step fm
  step fm
  step fm
  rw [show (e + 2) + 1 = (e + 2) + 1 from rfl]
  step fm
  ring_nf; finish

-- Last round of d-drain: R3, 3×R2.
-- (a, 0, 1, 1, e) -> (a+3, 0, 0, 0, e+3)
theorem drain_last (a e : ℕ) :
    ⟨a, 0, 1, 1, e⟩ [fm]⊢* ⟨a + 3, 0, 0, 0, e + 3⟩ := by
  rw [show (1 : ℕ) = 0 + 1 from rfl]
  step fm
  rw [show (3 : ℕ) = 2 + 1 from rfl]
  step fm
  step fm
  step fm
  ring_nf; finish

-- Full d-drain: (a, 0, 1, k+1, e) -> (a + 3*(k+1), 0, 0, 0, e + 2*k + 3).
theorem d_drain : ∀ k, ∀ a e,
    ⟨a, 0, 1, k + 1, e⟩ [fm]⊢*
    ⟨a + 3 * (k + 1), 0, 0, 0, e + 2 * k + 3⟩ := by
  intro k; induction' k with k ih <;> intro a e
  · apply drain_last
  · rw [show (k + 1) + 1 = k + 2 from by ring]
    apply stepStar_trans (drain_step a k e)
    apply stepStar_trans (ih (a + 3) (e + 2))
    ring_nf; finish

-- E-to-C transfer via R4.
theorem e_to_c : ∀ k, ∀ a c e,
    ⟨a, 0, c, 0, e + k⟩ [fm]⊢*
    ⟨a, 0, c + k, 0, e⟩ := by
  intro k; induction' k with k ih <;> intro a c e
  · exists 0
  · rw [show e + (k + 1) = (e + k) + 1 from by ring]
    step fm
    apply stepStar_trans (ih a (c + 1) e)
    ring_nf; finish

-- Remainder phase for Sub2: R3, R1, 2×R2, R4.
-- (a+1, 0, 2, d+1, 0) -> (a+2, 0, 1, d+1, 1)
theorem remainder (a d : ℕ) :
    ⟨a + 1, 0, 2, d + 1, 0⟩ [fm]⊢*
    ⟨a + 2, 0, 1, d + 1, 1⟩ := by
  rw [show (2 : ℕ) = 1 + 1 from rfl,
      show d + 1 = d + 1 from rfl,
      show (1 : ℕ) = 0 + 1 from rfl]
  step fm
  step fm
  step fm
  step fm
  step fm
  ring_nf; finish

-- Sub-transition 1.
theorem sub1 (F n : ℕ) :
    ⟨F + 9 * n + 15, 0, 12 * n + 15, 0, 0⟩ [fm]⊢⁺
    ⟨F + 18 * n + 31, 0, 12 * n + 21, 0, 0⟩ := by
  -- R5
  rw [show F + 9 * n + 15 = (F + 9 * n + 14) + 1 from by ring]
  step fm
  -- inner_loop: k = 3n+4, c_rem = 0, a_base = F+2
  rw [show F + 9 * n + 14 = (F + 2) + 3 * (3 * n + 4) from by ring,
      show 12 * n + 16 = 0 + 4 * (3 * n + 4) from by ring,
      show (1 : ℕ) = 0 + 1 from rfl]
  apply stepStar_trans (inner_loop (3 * n + 4) 0 (F + 2) 0)
  -- State: (F+2, 0, 0, 6n+9, 0)
  -- R5
  rw [show 0 + 2 * (3 * n + 4) + 1 = 6 * n + 9 from by ring,
      show F + 2 = (F + 1) + 1 from by ring]
  apply stepStar_trans
  · apply step_stepStar
    show fm ⟨(F + 1) + 1, 0, 0, 6 * n + 9, 0⟩ = some ⟨F + 1, 0, 1, (6 * n + 9) + 1, 0⟩
    simp [fm]
  -- d_drain: k = 6n+9
  apply stepStar_trans (d_drain (6 * n + 9) (F + 1) 0)
  -- e_to_c
  rw [show F + 1 + 3 * (6 * n + 9 + 1) = F + 18 * n + 31 from by ring,
      show 0 + 2 * (6 * n + 9) + 3 = 0 + (12 * n + 21) from by ring]
  apply stepStar_trans (e_to_c (12 * n + 21) (F + 18 * n + 31) 0 0)
  ring_nf; finish

-- Sub-transition 2.
theorem sub2 (F n : ℕ) :
    ⟨F + 18 * n + 31, 0, 12 * n + 21, 0, 0⟩ [fm]⊢⁺
    ⟨F + 27 * n + 49, 0, 12 * n + 24, 0, 0⟩ := by
  -- R5
  rw [show F + 18 * n + 31 = (F + 18 * n + 30) + 1 from by ring]
  step fm
  -- inner_loop: k = 3n+5, c_rem = 2, a_base = F+9n+15
  rw [show F + 18 * n + 30 = (F + 9 * n + 15) + 3 * (3 * n + 5) from by ring,
      show 12 * n + 22 = 2 + 4 * (3 * n + 5) from by ring,
      show (1 : ℕ) = 0 + 1 from rfl]
  apply stepStar_trans (inner_loop (3 * n + 5) 2 (F + 9 * n + 15) 0)
  -- State: (F+9n+15, 0, 2, 6n+11, 0)
  -- remainder
  rw [show 0 + 2 * (3 * n + 5) + 1 = 6 * n + 11 from by ring,
      show F + 9 * n + 15 = (F + 9 * n + 14) + 1 from by ring,
      show 6 * n + 11 = (6 * n + 10) + 1 from by ring]
  apply stepStar_trans (remainder (F + 9 * n + 14) (6 * n + 10))
  -- d_drain: k = 6n+10
  rw [show (F + 9 * n + 14) + 2 = F + 9 * n + 16 from by ring]
  apply stepStar_trans (d_drain (6 * n + 10) (F + 9 * n + 16) 1)
  -- e_to_c
  rw [show F + 9 * n + 16 + 3 * (6 * n + 10 + 1) = F + 27 * n + 49 from by ring,
      show 1 + 2 * (6 * n + 10) + 3 = 0 + (12 * n + 24) from by ring]
  apply stepStar_trans (e_to_c (12 * n + 24) (F + 27 * n + 49) 0 0)
  ring_nf; finish

-- Sub-transition 3.
theorem sub3 (F n : ℕ) :
    ⟨F + 27 * n + 49, 0, 12 * n + 24, 0, 0⟩ [fm]⊢⁺
    ⟨F + 36 * n + 69, 0, 12 * n + 27, 0, 0⟩ := by
  -- R5
  rw [show F + 27 * n + 49 = (F + 27 * n + 48) + 1 from by ring]
  step fm
  -- inner_loop: k = 3n+6, c_rem = 1, a_base = F+18n+30
  rw [show F + 27 * n + 48 = (F + 18 * n + 30) + 3 * (3 * n + 6) from by ring,
      show 12 * n + 25 = 1 + 4 * (3 * n + 6) from by ring,
      show (1 : ℕ) = 0 + 1 from rfl]
  apply stepStar_trans (inner_loop (3 * n + 6) 1 (F + 18 * n + 30) 0)
  -- State: (F+18n+30, 0, 1, 6n+13, 0)
  -- d_drain: k = 6n+12
  rw [show 0 + 2 * (3 * n + 6) + 1 = 6 * n + 13 from by ring,
      show 6 * n + 13 = (6 * n + 12) + 1 from by ring]
  apply stepStar_trans (d_drain (6 * n + 12) (F + 18 * n + 30) 0)
  -- e_to_c
  rw [show F + 18 * n + 30 + 3 * (6 * n + 12 + 1) = F + 36 * n + 69 from by ring,
      show 0 + 2 * (6 * n + 12) + 3 = 0 + (12 * n + 27) from by ring]
  apply stepStar_trans (e_to_c (12 * n + 27) (F + 36 * n + 69) 0 0)
  ring_nf; finish

-- Main macro-transition.
theorem main_trans (F n : ℕ) :
    ⟨F + 9 * n + 15, 0, 12 * n + 15, 0, 0⟩ [fm]⊢⁺
    ⟨F + 36 * n + 69, 0, 12 * n + 27, 0, 0⟩ :=
  stepPlus_trans (stepPlus_trans (sub1 F n) (sub2 F n)) (sub3 F n)

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨34, 0, 15, 0, 0⟩)
  · execute fm 178
  apply progress_nonhalt_simple (fm := fm) (A := ℕ × ℕ)
    (fun p ↦ ⟨p.1 + 9 * p.2 + 15, 0, 12 * p.2 + 15, 0, 0⟩) ⟨19, 0⟩
  intro ⟨F, n⟩
  refine ⟨⟨F + 27 * n + 45, n + 1⟩, ?_⟩
  show ⟨F + 9 * n + 15, 0, 12 * n + 15, 0, 0⟩ [fm]⊢⁺
    ⟨(F + 27 * n + 45) + 9 * (n + 1) + 15, 0, 12 * (n + 1) + 15, 0, 0⟩
  rw [show (F + 27 * n + 45) + 9 * (n + 1) + 15 = F + 36 * n + 69 from by ring,
      show 12 * (n + 1) + 15 = 12 * n + 27 from by ring]
  exact main_trans F n

end Sz22_2003_unofficial_1532
