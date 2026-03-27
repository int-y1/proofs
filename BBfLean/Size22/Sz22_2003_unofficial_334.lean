import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #334: [18/35, 75/2, 1/375, 7/3, 5/7]

Vector representation:
```
 1  2 -1 -1
-1  1  2  0
 0 -1 -3  0
 0 -1  0  1
 0  0  1 -1
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_334

def Q := ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a, b, c+1, d+1⟩ => some ⟨a+1, b+2, c, d⟩
  | ⟨a+1, b, c, d⟩ => some ⟨a, b+1, c+2, d⟩
  | ⟨a, b+1, c+3, d⟩ => some ⟨a, b, c, d⟩
  | ⟨a, b+1, c, d⟩ => some ⟨a, b, c, d+1⟩
  | ⟨a, b, c, d+1⟩ => some ⟨a, b, c+1, d⟩
  | _ => none

theorem climb_step (k d : ℕ) :
    ⟨k + 1, 5 * k + 2, 0, d + 2⟩ [fm]⊢* (⟨k + 2, 5 * k + 7, 0, d⟩ : Q) := by
  step fm; step fm; step fm; ring_nf; finish

theorem climb_even : ∀ n k,
    ⟨k + 1, 5 * k + 2, 0, 2 * n⟩ [fm]⊢* (⟨k + n + 1, 5 * (k + n) + 2, 0, 0⟩ : Q) := by
  intro n; induction n with
  | zero => intro k; ring_nf; exists 0
  | succ n ih =>
    intro k
    rw [show 2 * (n + 1) = 2 * n + 2 from by ring]
    apply stepStar_trans (climb_step k (2 * n))
    rw [show 5 * k + 7 = 5 * (k + 1) + 2 from by ring]
    apply stepStar_trans (ih (k + 1)); ring_nf; finish

theorem climb_odd : ∀ n k,
    ⟨k + 1, 5 * k + 2, 0, 2 * n + 1⟩ [fm]⊢* (⟨k + n + 1, 5 * (k + n) + 2, 0, 1⟩ : Q) := by
  intro n; induction n with
  | zero => intro k; ring_nf; exists 0
  | succ n ih =>
    intro k
    rw [show 2 * (n + 1) + 1 = (2 * n + 1) + 2 from by ring]
    apply stepStar_trans (climb_step k (2 * n + 1))
    rw [show 5 * k + 7 = 5 * (k + 1) + 2 from by ring]
    apply stepStar_trans (ih (k + 1)); ring_nf; finish

-- r2_wind_gen: a+1 steps, adds a+1 to b and 2*(a+1) to c
theorem r2_wind_gen : ∀ a b c,
    ⟨a + 1, b, c, 0⟩ [fm]⊢* (⟨0, b + a + 1, c + 2 * a + 2, 0⟩ : Q) := by
  intro a; induction a with
  | zero => intro b c; step fm; ring_nf; finish
  | succ a ih =>
    intro b c; step fm
    apply stepStar_trans (ih (b + 1) (c + 2))
    ring_nf; finish

-- r3 drain with remainder: j steps
theorem r3_drain_rem : ∀ j b c,
    ⟨0, b + j, 3 * j + c, 0⟩ [fm]⊢* (⟨0, b, c, 0⟩ : Q) := by
  intro j; induction j with
  | zero => intro b c; simp; exists 0
  | succ j ih =>
    intro b c
    rw [show b + (j + 1) = (b + j) + 1 from by ring,
        show 3 * (j + 1) + c = (3 * j + c) + 3 from by ring]
    step fm
    apply stepStar_trans (ih b c); ring_nf; finish

-- tail_c1: 7 steps, (0, b+1, 1, 0) to (0, b+4, 0, 0)
theorem tail_c1 (b : ℕ) :
    ⟨0, b + 1, 1, 0⟩ [fm]⊢* (⟨0, b + 4, 0, 0⟩ : Q) := by
  step fm; step fm; step fm; step fm; step fm; step fm; step fm; ring_nf; finish

-- tail_c2: 4 steps, (0, b+1, 2, 0) to (0, b+2, 0, 0)
theorem tail_c2 (b : ℕ) :
    ⟨0, b + 1, 2, 0⟩ [fm]⊢* (⟨0, b + 2, 0, 0⟩ : Q) := by
  step fm; step fm; step fm; step fm; ring_nf; finish

-- r4 drain: k+1 steps
theorem r4_drain : ∀ k d,
    ⟨0, k + 1, 0, d⟩ [fm]⊢* (⟨0, 0, 0, d + k + 1⟩ : Q) := by
  intro k; induction k with
  | zero => intro d; step fm; ring_nf; finish
  | succ k ih =>
    intro d; step fm
    apply stepStar_trans (ih (d + 1)); ring_nf; finish

-- Startup: 2 steps
theorem startup (d : ℕ) :
    ⟨0, 0, 0, d + 2⟩ [fm]⊢⁺ (⟨1, 2, 0, d⟩ : Q) := by
  execute fm 2

-- Even climb + r2 wind: (1, 2, 0, 2n) ⊢* (0, 6n+3, 2n+2, 0)
theorem even_climb_wind (n : ℕ) :
    ⟨1, 2, 0, 2 * n⟩ [fm]⊢* (⟨0, 6 * n + 3, 2 * n + 2, 0⟩ : Q) := by
  apply stepStar_trans (climb_even n 0)
  rw [show 0 + n + 1 = n + 1 from by ring,
      show 5 * (0 + n) + 2 = 5 * n + 2 from by ring]
  apply stepStar_trans (r2_wind_gen n (5 * n + 2) 0)
  ring_nf; finish

-- Odd climb + 2 steps + r2 wind: (1, 2, 0, 2n+1) ⊢* (0, 6n+6, 2n+3, 0)
-- Path: climb to (n+1, 5n+2, 0, 1), r2 to (n, 5n+3, 2, 1),
--       r1 to (n+1, 5n+5, 1, 0), then r2_wind_gen with c=1.
theorem odd_climb_wind (n : ℕ) :
    ⟨1, 2, 0, 2 * n + 1⟩ [fm]⊢* (⟨0, 6 * n + 6, 2 * n + 3, 0⟩ : Q) := by
  apply stepStar_trans (climb_odd n 0)
  rw [show 0 + n + 1 = n + 1 from by ring,
      show 5 * (0 + n) + 2 = 5 * n + 2 from by ring]
  -- State: (n+1, 5n+2, 0, 1). r2 then r1.
  step fm; step fm
  -- State: (n+1, 5n+5, 1, 0).
  rw [show 5 * n + 2 + 1 + 2 = 5 * n + 5 from by ring]
  apply stepStar_trans (r2_wind_gen n (5 * n + 5) 1)
  ring_nf; finish

-- Case D = 6j+2: target = 16j+4
theorem trans_6j2 (j : ℕ) :
    ⟨0, 0, 0, 6 * j + 2⟩ [fm]⊢⁺ (⟨0, 0, 0, 16 * j + 4⟩ : Q) := by
  rw [show 6 * j + 2 = 2 * (3 * j) + 2 from by ring]
  apply stepPlus_stepStar_stepPlus (startup (2 * (3 * j)))
  apply stepStar_trans (even_climb_wind (3 * j))
  -- State: (0, 18j+3, 6j+2, 0)
  rw [show 6 * (3 * j) + 3 = (16 * j + 3) + 2 * j from by ring,
      show 2 * (3 * j) + 2 = 3 * (2 * j) + 2 from by ring]
  apply stepStar_trans (r3_drain_rem (2 * j) (16 * j + 3) 2)
  apply stepStar_trans (tail_c2 (16 * j + 2))
  rw [show 16 * j + 2 + 2 = 16 * j + 4 from by ring]
  apply stepStar_trans (r4_drain (16 * j + 3) 0); ring_nf; finish

-- Case D = 6j+4: target = 16j+11
theorem trans_6j4 (j : ℕ) :
    ⟨0, 0, 0, 6 * j + 4⟩ [fm]⊢⁺ (⟨0, 0, 0, 16 * j + 11⟩ : Q) := by
  rw [show 6 * j + 4 = 2 * (3 * j + 1) + 2 from by ring]
  apply stepPlus_stepStar_stepPlus (startup (2 * (3 * j + 1)))
  apply stepStar_trans (even_climb_wind (3 * j + 1))
  rw [show 6 * (3 * j + 1) + 3 = (16 * j + 8) + (2 * j + 1) from by ring,
      show 2 * (3 * j + 1) + 2 = 3 * (2 * j + 1) + 1 from by ring]
  apply stepStar_trans (r3_drain_rem (2 * j + 1) (16 * j + 8) 1)
  apply stepStar_trans (tail_c1 (16 * j + 7))
  rw [show 16 * j + 7 + 4 = 16 * j + 11 from by ring]
  apply stepStar_trans (r4_drain (16 * j + 10) 0); ring_nf; finish

-- Case D = 6j+6: target = 16j+13
theorem trans_6j6 (j : ℕ) :
    ⟨0, 0, 0, 6 * j + 6⟩ [fm]⊢⁺ (⟨0, 0, 0, 16 * j + 13⟩ : Q) := by
  rw [show 6 * j + 6 = 2 * (3 * j + 2) + 2 from by ring]
  apply stepPlus_stepStar_stepPlus (startup (2 * (3 * j + 2)))
  apply stepStar_trans (even_climb_wind (3 * j + 2))
  rw [show 6 * (3 * j + 2) + 3 = (16 * j + 13) + (2 * j + 2) from by ring,
      show 2 * (3 * j + 2) + 2 = 3 * (2 * j + 2) + 0 from by ring]
  apply stepStar_trans (r3_drain_rem (2 * j + 2) (16 * j + 13) 0)
  apply stepStar_trans (r4_drain (16 * j + 12) 0); ring_nf; finish

-- Case D = 6j+3: target = 16j+5
theorem trans_6j3 (j : ℕ) :
    ⟨0, 0, 0, 6 * j + 3⟩ [fm]⊢⁺ (⟨0, 0, 0, 16 * j + 5⟩ : Q) := by
  rw [show 6 * j + 3 = (2 * (3 * j) + 1) + 2 from by ring]
  apply stepPlus_stepStar_stepPlus (startup (2 * (3 * j) + 1))
  apply stepStar_trans (odd_climb_wind (3 * j))
  -- State: (0, 18j+6, 6j+3, 0)
  rw [show 6 * (3 * j) + 6 = (16 * j + 5) + (2 * j + 1) from by ring,
      show 2 * (3 * j) + 3 = 3 * (2 * j + 1) + 0 from by ring]
  apply stepStar_trans (r3_drain_rem (2 * j + 1) (16 * j + 5) 0)
  apply stepStar_trans (r4_drain (16 * j + 4) 0); ring_nf; finish

-- Case D = 6j+5: target = 16j+12
theorem trans_6j5 (j : ℕ) :
    ⟨0, 0, 0, 6 * j + 5⟩ [fm]⊢⁺ (⟨0, 0, 0, 16 * j + 12⟩ : Q) := by
  rw [show 6 * j + 5 = (2 * (3 * j + 1) + 1) + 2 from by ring]
  apply stepPlus_stepStar_stepPlus (startup (2 * (3 * j + 1) + 1))
  apply stepStar_trans (odd_climb_wind (3 * j + 1))
  -- State: (0, 18j+12, 6j+5, 0)
  rw [show 6 * (3 * j + 1) + 6 = (16 * j + 11) + (2 * j + 1) from by ring,
      show 2 * (3 * j + 1) + 3 = 3 * (2 * j + 1) + 2 from by ring]
  apply stepStar_trans (r3_drain_rem (2 * j + 1) (16 * j + 11) 2)
  apply stepStar_trans (tail_c2 (16 * j + 10))
  rw [show 16 * j + 10 + 2 = 16 * j + 12 from by ring]
  apply stepStar_trans (r4_drain (16 * j + 11) 0); ring_nf; finish

-- Case D = 6j+7: target = 16j+19
theorem trans_6j7 (j : ℕ) :
    ⟨0, 0, 0, 6 * j + 7⟩ [fm]⊢⁺ (⟨0, 0, 0, 16 * j + 19⟩ : Q) := by
  rw [show 6 * j + 7 = (2 * (3 * j + 2) + 1) + 2 from by ring]
  apply stepPlus_stepStar_stepPlus (startup (2 * (3 * j + 2) + 1))
  apply stepStar_trans (odd_climb_wind (3 * j + 2))
  -- State: (0, 18j+18, 6j+7, 0)
  rw [show 6 * (3 * j + 2) + 6 = (16 * j + 16) + (2 * j + 2) from by ring,
      show 2 * (3 * j + 2) + 3 = 3 * (2 * j + 2) + 1 from by ring]
  apply stepStar_trans (r3_drain_rem (2 * j + 2) (16 * j + 16) 1)
  apply stepStar_trans (tail_c1 (16 * j + 15))
  rw [show 16 * j + 15 + 4 = 16 * j + 19 from by ring]
  apply stepStar_trans (r4_drain (16 * j + 18) 0); ring_nf; finish

theorem init_phase : c₀ [fm]⊢* (⟨0, 0, 0, 2⟩ : Q) := by
  execute fm 7

-- Helper to dispatch all 6 mod-6 cases
private theorem progress (d : ℕ) :
    ∃ d', ⟨0, 0, 0, d + 2⟩ [fm]⊢⁺ (⟨0, 0, 0, d' + 2⟩ : Q) := by
  have : d % 6 = 0 ∨ d % 6 = 1 ∨ d % 6 = 2 ∨ d % 6 = 3 ∨ d % 6 = 4 ∨ d % 6 = 5 := by omega
  rcases this with h | h | h | h | h | h
  · exact ⟨16 * (d / 6) + 2,
      by rw [show d + 2 = 6 * (d / 6) + 2 from by omega]; exact trans_6j2 _⟩
  · exact ⟨16 * (d / 6) + 3,
      by rw [show d + 2 = 6 * (d / 6) + 3 from by omega]; exact trans_6j3 _⟩
  · exact ⟨16 * (d / 6) + 9,
      by rw [show d + 2 = 6 * (d / 6) + 4 from by omega]; exact trans_6j4 _⟩
  · exact ⟨16 * (d / 6) + 10,
      by rw [show d + 2 = 6 * (d / 6) + 5 from by omega]; exact trans_6j5 _⟩
  · exact ⟨16 * (d / 6) + 11,
      by rw [show d + 2 = 6 * (d / 6) + 6 from by omega]; exact trans_6j6 _⟩
  · exact ⟨16 * (d / 6) + 17,
      by rw [show d + 2 = 6 * (d / 6) + 7 from by omega]; exact trans_6j7 _⟩

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts init_phase
  exact progress_nonhalt_simple (fun d : ℕ ↦ (⟨0, 0, 0, d + 2⟩ : Q)) 0
    (fun d ↦ progress d)

end Sz22_2003_unofficial_334
