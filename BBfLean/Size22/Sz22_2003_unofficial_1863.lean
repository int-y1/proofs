import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #1863: [9/35, 242/5, 5/33, 7/11, 275/2]

Vector representation:
```
 0  2 -1 -1  0
 1  0 -1  0  2
 0 -1  1  0 -1
 0  0  0  1 -1
-1  0  2  0  1
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_1863

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a, b, c+1, d+1, e⟩ => some ⟨a, b+2, c, d, e⟩
  | ⟨a, b, c+1, d, e⟩ => some ⟨a+1, b, c, d, e+2⟩
  | ⟨a, b+1, c, d, e+1⟩ => some ⟨a, b, c+1, d, e⟩
  | ⟨a, b, c, d, e+1⟩ => some ⟨a, b, c, d+1, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b, c+2, d, e+1⟩
  | _ => none

theorem r4_chain : ∀ k d, ⟨a, 0, 0, d, k⟩ [fm]⊢* ⟨a, 0, 0, d + k, 0⟩ := by
  intro k; induction k with
  | zero => intro d; exists 0
  | succ k ih =>
    intro d; step fm
    show ⟨a, 0, 0, d + 1, k⟩ [fm]⊢* _
    rw [show d + (k + 1) = (d + 1) + k from by ring]
    exact ih (d + 1)

-- (K, n+1, 0, 0, E+1) →* (K+n+1, 0, 0, 0, E+n+2)
-- Each round of R3+R2: a += 1, b -= 1, e += 1.
-- n+1 rounds total. Result: a = K+n+1, b = 0, e = E+1+n+1 = E+n+2.
theorem r3r2_chain : ∀ n K E, ⟨K, n + 1, 0, 0, E + 1⟩ [fm]⊢* ⟨K + n + 1, 0, 0, 0, E + n + 2⟩ := by
  intro n; induction n with
  | zero =>
    intro K E; step fm; step fm; finish
  | succ n ih =>
    intro K E; step fm; step fm
    show ⟨K + 1, n + 1, 0, 0, E + 2⟩ [fm]⊢* _
    rw [show E + 2 = (E + 1) + 1 from by ring]
    apply stepStar_trans (ih (K + 1) (E + 1))
    ring_nf; finish

theorem main_loop_step : ⟨A + 1, B, 0, D + 3, 0⟩ [fm]⊢* ⟨A, B + 5, 0, D, 0⟩ := by
  step fm; step fm; step fm; step fm; step fm; finish

theorem main_loop : ∀ k A B D, ⟨A + k, B, 0, D + 3 * k, 0⟩ [fm]⊢* ⟨A, B + 5 * k, 0, D, 0⟩ := by
  intro k; induction k with
  | zero => intro A B D; exists 0
  | succ k ih =>
    intro A B D
    rw [show A + (k + 1) = (A + 1) + k from by ring,
        show D + 3 * (k + 1) = (D + 3) + 3 * k from by ring]
    apply stepStar_trans (ih (A + 1) B (D + 3))
    show ⟨A + 1, B + 5 * k, 0, D + 3, 0⟩ [fm]⊢* _
    rw [show B + 5 * (k + 1) = (B + 5 * k) + 5 from by ring]
    exact main_loop_step

theorem terminal_d0 : ⟨A + 1, B, 0, 0, 0⟩ [fm]⊢⁺ ⟨A + 2, B, 0, 0, 5⟩ := by
  step fm; step fm; step fm; finish

theorem terminal_d1 : ⟨A + 1, B, 0, 1, 0⟩ [fm]⊢⁺ ⟨A + 1, B + 2, 0, 0, 3⟩ := by
  step fm; step fm; step fm; finish

theorem terminal_d2 : ⟨A + 1, B, 0, 2, 0⟩ [fm]⊢⁺ ⟨A, B + 4, 0, 0, 1⟩ := by
  step fm; step fm; step fm; finish

-- R3/R2 chain + R4: result has d = E+n+2
theorem r3r2_r4 (K n E : ℕ) : ⟨K, n + 1, 0, 0, E + 1⟩ [fm]⊢* ⟨K + n + 1, 0, 0, E + n + 2, 0⟩ := by
  apply stepStar_trans (r3r2_chain n K E)
  show ⟨K + n + 1, 0, 0, 0, E + n + 2⟩ [fm]⊢* _
  have := r4_chain (E + n + 2) 0 (a := K + n + 1)
  simp at this; exact this

-- Macro d=3*(m+1):
-- After main loop m+1 times: (F+1, 5m+5, 0, 0, 0).
-- terminal_d0: (F+2, 5m+5, 0, 0, 5).
-- r3r2_r4 with K=F+2, n+1=5m+5 (n=5m+4), E+1=5 (E=4):
-- Result: (F+2+5m+4+1, 0, 0, 4+5m+4+2, 0) = (F+5m+7, 0, 0, 5m+10, 0). ✓
theorem macro_d0 : ⟨F + m + 2, 0, 0, 3 * m + 3, 0⟩ [fm]⊢⁺ ⟨F + 5 * m + 7, 0, 0, 5 * m + 10, 0⟩ := by
  rw [show F + m + 2 = (F + 1) + (m + 1) from by ring,
      show 3 * m + 3 = 0 + 3 * (m + 1) from by ring]
  apply stepStar_stepPlus_stepPlus (main_loop (m + 1) (F + 1) 0 0)
  rw [show 0 + 5 * (m + 1) = 5 * m + 5 from by ring]
  apply stepPlus_stepStar_stepPlus (terminal_d0 (A := F) (B := 5 * m + 5))
  show ⟨F + 2, 5 * m + 5, 0, 0, 5⟩ [fm]⊢* _
  rw [show (5 * m + 5 : ℕ) = (5 * m + 4) + 1 from by ring,
      show (5 : ℕ) = 4 + 1 from by ring]
  apply stepStar_trans (r3r2_r4 (F + 2) (5 * m + 4) 4)
  rw [show F + 2 + (5 * m + 4) + 1 = F + 5 * m + 7 from by ring,
      show 4 + (5 * m + 4) + 2 = 5 * m + 10 from by ring]
  finish

-- Macro d=1:
-- terminal_d1: (F+1, 2, 0, 0, 3).
-- r3r2_r4 with K=F+1, n+1=2 (n=1), E+1=3 (E=2):
-- Result: (F+1+1+1, 0, 0, 2+1+2, 0) = (F+3, 0, 0, 5, 0). ✓
theorem macro_d1_base : ⟨F + 1, 0, 0, 1, 0⟩ [fm]⊢⁺ ⟨F + 3, 0, 0, 5, 0⟩ := by
  apply stepPlus_stepStar_stepPlus (terminal_d1 (A := F) (B := 0))
  show ⟨F + 1, 2, 0, 0, 3⟩ [fm]⊢* _
  rw [show (2 : ℕ) = 1 + 1 from by ring, show (3 : ℕ) = 2 + 1 from by ring]
  apply stepStar_trans (r3r2_r4 (F + 1) 1 2)
  rw [show F + 1 + 1 + 1 = F + 3 from by ring, show 2 + 1 + 2 = 5 from by ring]
  finish

-- Macro d=3*m+4:
-- After main loop: (F+1, 5m+5, 0, 1, 0).
-- terminal_d1: (F+1, 5m+7, 0, 0, 3).
-- r3r2_r4 with K=F+1, n+1=5m+7 (n=5m+6), E+1=3 (E=2):
-- Result: (F+1+5m+6+1, 0, 0, 2+5m+6+2, 0) = (F+5m+8, 0, 0, 5m+10, 0). ✓
theorem macro_d1 : ⟨F + m + 2, 0, 0, 3 * m + 4, 0⟩ [fm]⊢⁺ ⟨F + 5 * m + 8, 0, 0, 5 * m + 10, 0⟩ := by
  rw [show F + m + 2 = (F + 1) + (m + 1) from by ring,
      show 3 * m + 4 = 1 + 3 * (m + 1) from by ring]
  apply stepStar_stepPlus_stepPlus (main_loop (m + 1) (F + 1) 0 1)
  rw [show 0 + 5 * (m + 1) = 5 * m + 5 from by ring]
  apply stepPlus_stepStar_stepPlus (terminal_d1 (A := F) (B := 5 * m + 5))
  show ⟨F + 1, 5 * m + 5 + 2, 0, 0, 3⟩ [fm]⊢* _
  rw [show 5 * m + 5 + 2 = (5 * m + 6) + 1 from by ring,
      show (3 : ℕ) = 2 + 1 from by ring]
  apply stepStar_trans (r3r2_r4 (F + 1) (5 * m + 6) 2)
  rw [show F + 1 + (5 * m + 6) + 1 = F + 5 * m + 8 from by ring,
      show 2 + (5 * m + 6) + 2 = 5 * m + 10 from by ring]
  finish

-- Macro d=2:
-- terminal_d2: (F, 4, 0, 0, 1).
-- r3r2_r4 with K=F, n+1=4 (n=3), E+1=1 (E=0):
-- Result: (F+3+1, 0, 0, 0+3+2, 0) = (F+4, 0, 0, 5, 0). ✓
theorem macro_d2_base : ⟨F + 1, 0, 0, 2, 0⟩ [fm]⊢⁺ ⟨F + 4, 0, 0, 5, 0⟩ := by
  apply stepPlus_stepStar_stepPlus (terminal_d2 (A := F) (B := 0))
  show ⟨F, 4, 0, 0, 1⟩ [fm]⊢* _
  rw [show (4 : ℕ) = 3 + 1 from by ring, show (1 : ℕ) = 0 + 1 from by ring]
  apply stepStar_trans (r3r2_r4 F 3 0)
  rw [show F + 3 + 1 = F + 4 from by ring, show 0 + 3 + 2 = 5 from by ring]
  finish

-- Macro d=3*m+5:
-- After main loop: (F+1, 5m+5, 0, 2, 0).
-- terminal_d2: (F, 5m+9, 0, 0, 1).
-- r3r2_r4 with K=F, n+1=5m+9 (n=5m+8), E+1=1 (E=0):
-- Result: (F+5m+8+1, 0, 0, 0+5m+8+2, 0) = (F+5m+9, 0, 0, 5m+10, 0). ✓
theorem macro_d2 : ⟨F + m + 2, 0, 0, 3 * m + 5, 0⟩ [fm]⊢⁺ ⟨F + 5 * m + 9, 0, 0, 5 * m + 10, 0⟩ := by
  rw [show F + m + 2 = (F + 1) + (m + 1) from by ring,
      show 3 * m + 5 = 2 + 3 * (m + 1) from by ring]
  apply stepStar_stepPlus_stepPlus (main_loop (m + 1) (F + 1) 0 2)
  rw [show 0 + 5 * (m + 1) = 5 * m + 5 from by ring]
  apply stepPlus_stepStar_stepPlus (terminal_d2 (A := F) (B := 5 * m + 5))
  show ⟨F, 5 * m + 5 + 4, 0, 0, 1⟩ [fm]⊢* _
  rw [show 5 * m + 5 + 4 = (5 * m + 8) + 1 from by ring,
      show (1 : ℕ) = 0 + 1 from by ring]
  apply stepStar_trans (r3r2_r4 F (5 * m + 8) 0)
  rw [show F + (5 * m + 8) + 1 = F + 5 * m + 9 from by ring,
      show 0 + (5 * m + 8) + 2 = 5 * m + 10 from by ring]
  finish

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨2, 0, 0, 5, 0⟩) (by execute fm 8)
  apply progress_nonhalt (fm := fm)
    (P := fun q ↦ ∃ a d, q = ⟨a, 0, 0, d, 0⟩ ∧ d ≥ 1 ∧ 3 * a ≥ d + 1)
  · intro c ⟨a, d, hq, hd, ha⟩; subst hq
    rcases (show d % 3 = 0 ∨ d % 3 = 1 ∨ d % 3 = 2 from by omega) with h0 | h1 | h2
    · -- d % 3 = 0
      obtain ⟨m, hm⟩ : ∃ m, d = 3 * (m + 1) := by
        refine ⟨d / 3 - 1, ?_⟩; omega
      obtain ⟨F, rfl⟩ : ∃ F, a = F + m + 2 := ⟨a - m - 2, by omega⟩
      rw [show 3 * (m + 1) = 3 * m + 3 from by ring] at hm
      refine ⟨⟨F + 5 * m + 7, 0, 0, 5 * m + 10, 0⟩,
        ⟨F + 5 * m + 7, 5 * m + 10, rfl, by omega, by omega⟩, ?_⟩
      rw [hm]; exact macro_d0
    · -- d % 3 = 1
      rcases (show d = 1 ∨ d ≥ 4 from by omega) with rfl | hd4
      · -- d = 1
        obtain ⟨F, rfl⟩ : ∃ F, a = F + 1 := ⟨a - 1, by omega⟩
        exact ⟨⟨F + 3, 0, 0, 5, 0⟩,
          ⟨F + 3, 5, rfl, by omega, by omega⟩, macro_d1_base⟩
      · -- d = 3*(m+1)+1
        obtain ⟨m, hm⟩ : ∃ m, d = 3 * (m + 1) + 1 := by
          refine ⟨d / 3 - 1, ?_⟩; omega
        rw [show 3 * (m + 1) + 1 = 3 * m + 4 from by ring] at hm
        obtain ⟨F, rfl⟩ : ∃ F, a = F + m + 2 := ⟨a - m - 2, by omega⟩
        refine ⟨⟨F + 5 * m + 8, 0, 0, 5 * m + 10, 0⟩,
          ⟨F + 5 * m + 8, 5 * m + 10, rfl, by omega, by omega⟩, ?_⟩
        rw [hm]; exact macro_d1
    · -- d % 3 = 2
      rcases (show d = 2 ∨ d ≥ 5 from by omega) with rfl | hd5
      · -- d = 2
        obtain ⟨F, rfl⟩ : ∃ F, a = F + 1 := ⟨a - 1, by omega⟩
        exact ⟨⟨F + 4, 0, 0, 5, 0⟩,
          ⟨F + 4, 5, rfl, by omega, by omega⟩, macro_d2_base⟩
      · -- d = 3*(m+1)+2
        obtain ⟨m, hm⟩ : ∃ m, d = 3 * (m + 1) + 2 := by
          refine ⟨d / 3 - 1, ?_⟩; omega
        rw [show 3 * (m + 1) + 2 = 3 * m + 5 from by ring] at hm
        obtain ⟨F, rfl⟩ : ∃ F, a = F + m + 2 := ⟨a - m - 2, by omega⟩
        refine ⟨⟨F + 5 * m + 9, 0, 0, 5 * m + 10, 0⟩,
          ⟨F + 5 * m + 9, 5 * m + 10, rfl, by omega, by omega⟩, ?_⟩
        rw [hm]; exact macro_d2
  · exact ⟨2, 5, rfl, by omega, by omega⟩
