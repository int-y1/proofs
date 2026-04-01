import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #1205: [5/6, 539/2, 4/35, 3/49, 14/11]

Vector representation:
```
-1 -1  1  0  0
-1  0  0  2  1
 2  0 -1 -1  0
 0  1  0 -2  0
 1  0  0  1 -1
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_1205

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a+1, b+1, c, d, e⟩ => some ⟨a, b, c+1, d, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b, c, d+2, e+1⟩
  | ⟨a, b, c+1, d+1, e⟩ => some ⟨a+2, b, c, d, e⟩
  | ⟨a, b, c, d+2, e⟩ => some ⟨a, b+1, c, d, e⟩
  | ⟨a, b, c, d, e+1⟩ => some ⟨a+1, b, c, d+1, e⟩
  | _ => none

-- R4 drain: (0, b, 0, d+2k, e) →* (0, b+k, 0, d, e)
theorem r4_drain : ∀ k, ⟨(0:ℕ), b, 0, d + 2 * k, e⟩ [fm]⊢* ⟨0, b + k, 0, d, e⟩ := by
  intro k; induction' k with k ih generalizing b d e
  · exists 0
  · rw [show d + 2 * (k + 1) = (d + 2 * k) + 2 from by ring]
    step fm
    apply stepStar_trans (ih (b := b + 1))
    ring_nf; finish

-- Full spiral: (0, 0, C, d+1, e) →* (0, 0, 0, d+1+3*C, e+2*C)
theorem spiral : ∀ C, ⟨(0:ℕ), 0, C, d + 1, e⟩ [fm]⊢* ⟨0, 0, 0, d + 1 + 3 * C, e + 2 * C⟩ := by
  intro C; induction' C with C ih generalizing d e
  · exists 0
  · step fm; step fm; step fm
    rw [show d + 4 = (d + 3) + 1 from by ring]
    apply stepStar_trans (ih (d := d + 3) (e := e + 2))
    ring_nf; finish

-- Conversion chain: by induction on j
-- (0, 3j+r, c, 0, e+j) →* (0, r, c+2j, 0, e)
theorem conv_chain : ∀ j, ⟨(0:ℕ), 3 * j + r, c, 0, e + j⟩ [fm]⊢* ⟨0, r, c + 2 * j, 0, e⟩ := by
  intro j; induction' j with j ih generalizing r c e
  · simp; exists 0
  · -- From (0, 3(j+1)+r, c, 0, e+j+1) to (0, r, c+2(j+1), 0, e)
    -- Step 1: 5 steps R5,R1,R3,R1,R1 → (0, 3j+r, c+2, 0, e+j)
    -- Step 2: by IH → (0, r, c+2+2j, 0, e) = (0, r, c+2(j+1), 0, e)
    show ⟨0, 3 * (j + 1) + r, c, 0, e + (j + 1)⟩ [fm]⊢* ⟨0, r, c + 2 * (j + 1), 0, e⟩
    rw [show 3 * (j + 1) + r = (3 * j + r) + 3 from by ring,
        show e + (j + 1) = e + j + 1 from by ring]
    -- now: (0, (3j+r)+3, c, 0, (e+j)+1) →* ...
    -- apply 5 steps (R5, R1, R3, R1, R1):
    step fm; step fm; step fm; step fm; step fm
    -- now at (0, 3j+r, c+2, 0, e+j)
    apply stepStar_trans (ih (c := c + 2) (e := e))
    ring_nf; finish

-- End case r=0: (0, 0, c, 0, e+1) →* (0, 0, 0, 3+3c, e+1+2c)
theorem end_r0 : ⟨(0:ℕ), 0, c, 0, e + 1⟩ [fm]⊢* ⟨0, 0, 0, 3 + 3 * c, e + 1 + 2 * c⟩ := by
  step fm; step fm
  rw [show (3:ℕ) = 2 + 1 from by ring]
  apply stepStar_trans (spiral c (d := 2) (e := e + 1))
  ring_nf; finish

-- End case r=1: (0, 1, c, 0, e+1) →* (0, 0, 0, 4+3c, e+2+2c)
theorem end_r1 : ⟨(0:ℕ), 1, c, 0, e + 1⟩ [fm]⊢* ⟨0, 0, 0, 4 + 3 * c, e + 2 + 2 * c⟩ := by
  step fm; step fm; step fm; step fm; step fm
  rw [show (4:ℕ) = 3 + 1 from by ring]
  apply stepStar_trans (spiral c (d := 3) (e := e + 2))
  ring_nf; finish

-- End case r=2: (0, 2, c, 0, e+1) →* (0, 0, 0, 5+3c, e+3+2c)
theorem end_r2 : ⟨(0:ℕ), 2, c, 0, e + 1⟩ [fm]⊢* ⟨0, 0, 0, 5 + 3 * c, e + 3 + 2 * c⟩ := by
  step fm; step fm; step fm; step fm; step fm; step fm; step fm; step fm
  rw [show (5:ℕ) = 4 + 1 from by ring]
  apply stepStar_trans (spiral c (d := 4) (e := e + 3))
  ring_nf; finish

-- Odd start: (0, b+5, 0, 1, e+1) →* (0, b, 3, 0, e)
theorem odd_start : ⟨(0:ℕ), b + 5, 0, 1, e + 1⟩ [fm]⊢* ⟨0, b, 3, 0, e⟩ := by
  step fm; step fm; step fm; step fm; step fm; step fm; step fm; step fm; finish

-- Odd base k=1: (0, 1, 0, 1, e+1) →⁺ (0, 0, 0, 5, e+2)
theorem odd_k1 : ⟨(0:ℕ), 1, 0, 1, e + 1⟩ [fm]⊢⁺ ⟨0, 0, 0, 5, e + 2⟩ := by
  step fm; step fm; step fm; step fm; step fm; finish

-- Odd base k=2: (0, 2, 0, 1, e+1) →⁺ (0, 0, 0, 6, e+3)
theorem odd_k2 : ⟨(0:ℕ), 2, 0, 1, e + 1⟩ [fm]⊢⁺ ⟨0, 0, 0, 6, e + 3⟩ := by
  step fm; step fm; step fm; step fm; step fm; step fm; step fm; step fm; finish

-- Odd base k=3: (0, 3, 0, 1, e+1) →⁺ (0, 0, 0, 7, e+4)
theorem odd_k3 : ⟨(0:ℕ), 3, 0, 1, e + 1⟩ [fm]⊢⁺ ⟨0, 0, 0, 7, e + 4⟩ := by
  step fm; step fm; step fm; step fm; step fm; step fm; step fm; step fm
  step fm; step fm; step fm; finish

-- Odd base k=4: (0, 4, 0, 1, e+1) →⁺ (0, 0, 0, 8, e+5)
theorem odd_k4 : ⟨(0:ℕ), 4, 0, 1, e + 1⟩ [fm]⊢⁺ ⟨0, 0, 0, 8, e + 5⟩ := by
  step fm; step fm; step fm; step fm; step fm; step fm; step fm; step fm
  step fm; step fm; step fm; step fm; step fm; step fm; finish

-- Helper: one R4 step as ⊢⁺
theorem r4_step_plus : ⟨(0:ℕ), b, 0, d + 2, e⟩ [fm]⊢⁺ ⟨0, b + 1, 0, d, e⟩ := by
  step fm; finish

-- === Full even transitions ===
-- Strategy: first R4 step gives ⊢⁺, then R4 drain (k-1 steps) ⊢*,
-- then conv_chain ⊢*, then end ⊢*.
-- We compose: ⊢⁺ + ⊢* = ⊢⁺

-- Even, K = 3j+1, d = 6j+2:
-- d = (6j+2) = (6j) + 2. First R4 → (0, 1, 0, 6j, E). Then r4_drain 3j → (0, 3j+1, 0, 0, E).
-- conv j → (0, 1, 2j, 0, E-j). end_r1 → (0,0,0,4+6j,E+3j+1).
theorem even_c1 (j : ℕ) :
    ⟨(0:ℕ), 0, 0, 6 * j + 2, e + 3 * j + 1⟩ [fm]⊢⁺
    ⟨0, 0, 0, 6 * j + 4, e + 6 * j + 2⟩ := by
  show ⟨0, 0, 0, 6 * j + 2, e + 3 * j + 1⟩ [fm]⊢⁺ ⟨0, 0, 0, 6 * j + 4, e + 6 * j + 2⟩
  rw [show 6 * j + 2 = (6 * j) + 2 from by ring]
  apply stepPlus_stepStar_stepPlus (r4_step_plus (b := 0) (d := 6 * j) (e := e + 3 * j + 1))
  rw [show 0 + 1 = 1 from by ring,
      show 6 * j = 0 + 2 * (3 * j) from by ring]
  apply stepStar_trans (r4_drain (3 * j) (b := 1) (d := 0) (e := e + 3 * j + 1))
  rw [show 1 + (3 * j) = 3 * j + 1 from by ring,
      show e + 3 * j + 1 = (e + 2 * j + 1) + j from by ring]
  apply stepStar_trans (conv_chain j (r := 1) (c := 0) (e := e + 2 * j + 1))
  rw [show 0 + 2 * j = 2 * j from by ring,
      show e + 2 * j + 1 = (e + 2 * j) + 1 from by ring]
  apply stepStar_trans (end_r1 (c := 2 * j) (e := e + 2 * j))
  ring_nf; finish

-- Even, K = 3j+2, d = 6j+4:
theorem even_c2 (j : ℕ) :
    ⟨(0:ℕ), 0, 0, 6 * j + 4, e + 3 * j + 2⟩ [fm]⊢⁺
    ⟨0, 0, 0, 6 * j + 5, e + 6 * j + 4⟩ := by
  rw [show 6 * j + 4 = (6 * j + 2) + 2 from by ring]
  apply stepPlus_stepStar_stepPlus (r4_step_plus (b := 0) (d := 6 * j + 2) (e := e + 3 * j + 2))
  rw [show 0 + 1 = 1 from by ring,
      show 6 * j + 2 = 0 + 2 * (3 * j + 1) from by ring]
  apply stepStar_trans (r4_drain (3 * j + 1) (b := 1) (d := 0) (e := e + 3 * j + 2))
  rw [show 1 + (3 * j + 1) = 3 * j + 2 from by ring,
      show e + 3 * j + 2 = (e + 2 * j + 2) + j from by ring]
  apply stepStar_trans (conv_chain j (r := 2) (c := 0) (e := e + 2 * j + 2))
  rw [show 0 + 2 * j = 2 * j from by ring,
      show e + 2 * j + 2 = (e + 2 * j + 1) + 1 from by ring]
  apply stepStar_trans (end_r2 (c := 2 * j) (e := e + 2 * j + 1))
  ring_nf; finish

-- Even, K = 3(j+1), d = 6j+6:
theorem even_c0 (j : ℕ) :
    ⟨(0:ℕ), 0, 0, 6 * j + 6, e + 3 * j + 3⟩ [fm]⊢⁺
    ⟨0, 0, 0, 6 * j + 9, e + 6 * j + 6⟩ := by
  rw [show 6 * j + 6 = (6 * j + 4) + 2 from by ring]
  apply stepPlus_stepStar_stepPlus (r4_step_plus (b := 0) (d := 6 * j + 4) (e := e + 3 * j + 3))
  rw [show 0 + 1 = 1 from by ring,
      show 6 * j + 4 = 0 + 2 * (3 * j + 2) from by ring]
  apply stepStar_trans (r4_drain (3 * j + 2) (b := 1) (d := 0) (e := e + 3 * j + 3))
  rw [show 1 + (3 * j + 2) = 3 * (j + 1) + 0 from by ring,
      show e + 3 * j + 3 = (e + 2 * j + 2) + (j + 1) from by ring]
  apply stepStar_trans (conv_chain (j + 1) (r := 0) (c := 0) (e := e + 2 * j + 2))
  rw [show 0 + 2 * (j + 1) = 2 * j + 2 from by ring,
      show e + 2 * j + 2 = (e + 2 * j + 1) + 1 from by ring]
  apply stepStar_trans (end_r0 (c := 2 * j + 2) (e := e + 2 * j + 1))
  ring_nf; finish

-- === Full odd transitions (K ≥ 5) ===

-- Odd, K=3j+5, d=6j+11:
-- d = 2*(3j+5)+1 = 6j+11. First R4 → (0,1,0,6j+9,E).
-- R4 drain (3j+4): (0,3j+5,0,1,E).
-- odd_start: (0,(3j)+5,0,1,E) →* (0,3j,3,0,E-1) [need E ≥ 1]
-- conv j: (0,3j,3,0,E-1-j+j) →* (0,0,3+2j,0,E-1-j)
-- Wait, conv_chain needs (0, 3j+0, 3, 0, (E-1-j)+j) = (0, 3j, 3, 0, E-1).
-- Hmm, the j in conv_chain's signature is the number of steps.
-- conv_chain j: (0, 3*j+r, c, 0, e_param+j) →* (0, r, c+2j, 0, e_param)
-- I need (0, 3*j+0, 3, 0, X) where X = e_param + j, so e_param = X - j.
-- X = E-1 = (e + 3j + 5) - 1 = e + 3j + 4. e_param = e + 3j + 4 - j = e + 2j + 4.
-- So conv_chain j with r=0, c=3, e_param=e+2j+4:
-- (0, 3j, 3, 0, (e+2j+4)+j) = (0, 3j, 3, 0, e+3j+4) →* (0, 0, 3+2j, 0, e+2j+4)
-- But E-1 = e+3j+4. ✓
-- end_r0: (0,0,3+2j,0,(e+2j+3)+1) →* (0,0,0,3+3(3+2j),(e+2j+3)+1+2(3+2j))
-- = (0,0,0,12+6j,e+2j+3+1+6+4j) = (0,0,0,6j+12,e+6j+10). ✓
theorem odd_c0 (j : ℕ) :
    ⟨(0:ℕ), 0, 0, 6 * j + 11, e + 3 * j + 5⟩ [fm]⊢⁺
    ⟨0, 0, 0, 6 * j + 12, e + 6 * j + 10⟩ := by
  rw [show 6 * j + 11 = (6 * j + 9) + 2 from by ring]
  apply stepPlus_stepStar_stepPlus (r4_step_plus (b := 0) (d := 6 * j + 9) (e := e + 3 * j + 5))
  rw [show 0 + 1 = 1 from by ring,
      show 6 * j + 9 = 1 + 2 * (3 * j + 4) from by ring]
  apply stepStar_trans (r4_drain (3 * j + 4) (b := 1) (d := 1) (e := e + 3 * j + 5))
  rw [show 1 + (3 * j + 4) = (3 * j) + 5 from by ring,
      show e + 3 * j + 5 = (e + 3 * j + 4) + 1 from by ring]
  apply stepStar_trans (odd_start (b := 3 * j) (e := e + 3 * j + 4))
  rw [show e + 3 * j + 4 = (e + 2 * j + 4) + j from by ring]
  apply stepStar_trans (conv_chain j (r := 0) (c := 3) (e := e + 2 * j + 4))
  rw [show 3 + 2 * j = 2 * j + 3 from by ring,
      show e + 2 * j + 4 = (e + 2 * j + 3) + 1 from by ring]
  apply stepStar_trans (end_r0 (c := 2 * j + 3) (e := e + 2 * j + 3))
  ring_nf; finish

-- Odd, K=3j+6, d=6j+13:
theorem odd_c1 (j : ℕ) :
    ⟨(0:ℕ), 0, 0, 6 * j + 13, e + 3 * j + 6⟩ [fm]⊢⁺
    ⟨0, 0, 0, 6 * j + 13, e + 6 * j + 12⟩ := by
  rw [show 6 * j + 13 = (6 * j + 11) + 2 from by ring]
  apply stepPlus_stepStar_stepPlus (r4_step_plus (b := 0) (d := 6 * j + 11) (e := e + 3 * j + 6))
  rw [show 0 + 1 = 1 from by ring,
      show 6 * j + 11 = 1 + 2 * (3 * j + 5) from by ring]
  apply stepStar_trans (r4_drain (3 * j + 5) (b := 1) (d := 1) (e := e + 3 * j + 6))
  rw [show 1 + (3 * j + 5) = (3 * j + 1) + 5 from by ring,
      show e + 3 * j + 6 = (e + 3 * j + 5) + 1 from by ring]
  apply stepStar_trans (odd_start (b := 3 * j + 1) (e := e + 3 * j + 5))
  rw [show e + 3 * j + 5 = (e + 2 * j + 5) + j from by ring]
  apply stepStar_trans (conv_chain j (r := 1) (c := 3) (e := e + 2 * j + 5))
  rw [show 3 + 2 * j = 2 * j + 3 from by ring,
      show e + 2 * j + 5 = (e + 2 * j + 4) + 1 from by ring]
  apply stepStar_trans (end_r1 (c := 2 * j + 3) (e := e + 2 * j + 4))
  ring_nf; finish

-- Odd, K=3j+7, d=6j+15:
theorem odd_c2 (j : ℕ) :
    ⟨(0:ℕ), 0, 0, 6 * j + 15, e + 3 * j + 7⟩ [fm]⊢⁺
    ⟨0, 0, 0, 6 * j + 14, e + 6 * j + 14⟩ := by
  rw [show 6 * j + 15 = (6 * j + 13) + 2 from by ring]
  apply stepPlus_stepStar_stepPlus (r4_step_plus (b := 0) (d := 6 * j + 13) (e := e + 3 * j + 7))
  rw [show 0 + 1 = 1 from by ring,
      show 6 * j + 13 = 1 + 2 * (3 * j + 6) from by ring]
  apply stepStar_trans (r4_drain (3 * j + 6) (b := 1) (d := 1) (e := e + 3 * j + 7))
  rw [show 1 + (3 * j + 6) = (3 * j + 2) + 5 from by ring,
      show e + 3 * j + 7 = (e + 3 * j + 6) + 1 from by ring]
  apply stepStar_trans (odd_start (b := 3 * j + 2) (e := e + 3 * j + 6))
  rw [show e + 3 * j + 6 = (e + 2 * j + 6) + j from by ring]
  apply stepStar_trans (conv_chain j (r := 2) (c := 3) (e := e + 2 * j + 6))
  rw [show 3 + 2 * j = 2 * j + 3 from by ring,
      show e + 2 * j + 6 = (e + 2 * j + 5) + 1 from by ring]
  apply stepStar_trans (end_r2 (c := 2 * j + 3) (e := e + 2 * j + 5))
  ring_nf; finish

-- === Small transitions ===
theorem d2_trans : ⟨(0:ℕ), 0, 0, 2, e + 1⟩ [fm]⊢⁺ ⟨0, 0, 0, 4, e + 2⟩ := by
  apply stepPlus_stepStar_stepPlus (r4_step_plus (b := 0) (d := 0) (e := e + 1))
  rw [show 0 + 1 = 1 from by ring]
  apply stepStar_trans (end_r1 (c := 0) (e := e))
  ring_nf; finish

theorem d3_trans : ⟨(0:ℕ), 0, 0, 3, e + 1⟩ [fm]⊢⁺ ⟨0, 0, 0, 5, e + 2⟩ := by
  rw [show (3:ℕ) = 1 + 2 from by ring]
  apply stepPlus_stepStar_stepPlus (r4_step_plus (b := 0) (d := 1) (e := e + 1))
  rw [show 0 + 1 = 1 from by ring]
  exact stepPlus_stepStar (odd_k1 (e := e))

theorem d5_trans : ⟨(0:ℕ), 0, 0, 5, e + 2⟩ [fm]⊢⁺ ⟨0, 0, 0, 6, e + 4⟩ := by
  rw [show (5:ℕ) = 3 + 2 from by ring]
  apply stepPlus_stepStar_stepPlus (r4_step_plus (b := 0) (d := 3) (e := e + 2))
  rw [show 0 + 1 = 1 from by ring,
      show (3:ℕ) = 1 + 2 * 1 from by ring]
  apply stepStar_trans (r4_drain 1 (b := 1) (d := 1) (e := e + 2))
  rw [show 1 + 1 = 2 from by ring,
      show e + 2 = (e + 1) + 1 from by ring]
  apply stepStar_trans (stepPlus_stepStar (odd_k2 (e := e + 1)))
  ring_nf; finish

theorem d7_trans : ⟨(0:ℕ), 0, 0, 7, e + 3⟩ [fm]⊢⁺ ⟨0, 0, 0, 7, e + 6⟩ := by
  rw [show (7:ℕ) = 5 + 2 from by ring]
  apply stepPlus_stepStar_stepPlus (r4_step_plus (b := 0) (d := 5) (e := e + 3))
  rw [show 0 + 1 = 1 from by ring,
      show (5:ℕ) = 1 + 2 * 2 from by ring]
  apply stepStar_trans (r4_drain 2 (b := 1) (d := 1) (e := e + 3))
  rw [show 1 + 2 = 3 from by ring,
      show e + 3 = (e + 2) + 1 from by ring]
  apply stepStar_trans (stepPlus_stepStar (odd_k3 (e := e + 2)))
  ring_nf; finish

theorem d9_trans : ⟨(0:ℕ), 0, 0, 9, e + 4⟩ [fm]⊢⁺ ⟨0, 0, 0, 8, e + 8⟩ := by
  rw [show (9:ℕ) = 7 + 2 from by ring]
  apply stepPlus_stepStar_stepPlus (r4_step_plus (b := 0) (d := 7) (e := e + 4))
  rw [show 0 + 1 = 1 from by ring,
      show (7:ℕ) = 1 + 2 * 3 from by ring]
  apply stepStar_trans (r4_drain 3 (b := 1) (d := 1) (e := e + 4))
  rw [show 1 + 3 = 4 from by ring,
      show e + 4 = (e + 3) + 1 from by ring]
  apply stepStar_trans (stepPlus_stepStar (odd_k4 (e := e + 3)))
  ring_nf; finish

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨0, 0, 0, 2, 1⟩)
  · execute fm 1
  apply progress_nonhalt (fm := fm)
    (P := fun q ↦ ∃ d E, q = ⟨0, 0, 0, d, E⟩ ∧ d ≥ 2 ∧ E ≥ d / 2)
  · intro c ⟨d, E, hq, hd, hE⟩; subst hq
    rcases Nat.even_or_odd d with ⟨K, hK⟩ | ⟨K, hK⟩
    · -- d even: d = K + K
      rw [show K + K = 2 * K from by ring] at hK; subst hK
      -- Split K into residue classes mod 3
      -- K ≥ 1 since d = 2K ≥ 2
      have hK1 : K ≥ 1 := by omega
      obtain ⟨j, hj⟩ : ∃ j, K = 3 * j + 1 ∨ K = 3 * j + 2 ∨ K = 3 * j + 3 :=
        ⟨(K - 1) / 3, by omega⟩
      rcases hj with hj | hj | hj
      · -- K = 3j+1, d = 6j+2
        subst hj
        obtain ⟨e, rfl⟩ : ∃ e, E = e + (3 * j + 1) := ⟨E - (3 * j + 1), by omega⟩
        refine ⟨⟨0, 0, 0, 6 * j + 4, e + 6 * j + 2⟩,
          ⟨6 * j + 4, e + 6 * j + 2, rfl, by omega, by omega⟩, ?_⟩
        show ⟨0, 0, 0, 2 * (3 * j + 1), e + (3 * j + 1)⟩ [fm]⊢⁺ _
        rw [show 2 * (3 * j + 1) = 6 * j + 2 from by ring]
        exact even_c1 j
      · -- K = 3j+2, d = 6j+4
        subst hj
        obtain ⟨e, rfl⟩ : ∃ e, E = e + (3 * j + 2) := ⟨E - (3 * j + 2), by omega⟩
        refine ⟨⟨0, 0, 0, 6 * j + 5, e + 6 * j + 4⟩,
          ⟨6 * j + 5, e + 6 * j + 4, rfl, by omega, by omega⟩, ?_⟩
        show ⟨0, 0, 0, 2 * (3 * j + 2), e + (3 * j + 2)⟩ [fm]⊢⁺ _
        rw [show 2 * (3 * j + 2) = 6 * j + 4 from by ring]
        exact even_c2 j
      · -- K = 3j+3, d = 6j+6
        subst hj
        obtain ⟨e, rfl⟩ : ∃ e, E = e + (3 * j + 3) := ⟨E - (3 * j + 3), by omega⟩
        refine ⟨⟨0, 0, 0, 6 * j + 9, e + 6 * j + 6⟩,
          ⟨6 * j + 9, e + 6 * j + 6, rfl, by omega, by omega⟩, ?_⟩
        show ⟨0, 0, 0, 2 * (3 * j + 3), e + (3 * j + 3)⟩ [fm]⊢⁺ _
        rw [show 2 * (3 * j + 3) = 6 * j + 6 from by ring,
            show e + (3 * j + 3) = e + 3 * j + 3 from by ring]
        exact even_c0 j
    · -- d odd: d = 2K + 1
      subst hK
      rcases (show K = 0 ∨ K = 1 ∨ K = 2 ∨ K = 3 ∨ K = 4 ∨ K ≥ 5 from by omega) with
        rfl | rfl | rfl | rfl | rfl | hK5
      · omega
      · obtain ⟨e, rfl⟩ : ∃ e, E = e + 1 := ⟨E - 1, by omega⟩
        exact ⟨⟨0, 0, 0, 5, e + 2⟩, ⟨5, e + 2, rfl, by omega, by omega⟩, d3_trans⟩
      · obtain ⟨e, rfl⟩ : ∃ e, E = e + 2 := ⟨E - 2, by omega⟩
        exact ⟨⟨0, 0, 0, 6, e + 4⟩, ⟨6, e + 4, rfl, by omega, by omega⟩, d5_trans⟩
      · obtain ⟨e, rfl⟩ : ∃ e, E = e + 3 := ⟨E - 3, by omega⟩
        exact ⟨⟨0, 0, 0, 7, e + 6⟩, ⟨7, e + 6, rfl, by omega, by omega⟩, d7_trans⟩
      · obtain ⟨e, rfl⟩ : ∃ e, E = e + 4 := ⟨E - 4, by omega⟩
        exact ⟨⟨0, 0, 0, 8, e + 8⟩, ⟨8, e + 8, rfl, by omega, by omega⟩, d9_trans⟩
      · obtain ⟨j, rfl | rfl | rfl⟩ : ∃ j, K = 3 * j + 5 ∨ K = 3 * j + 6 ∨ K = 3 * j + 7 :=
          ⟨(K - 5) / 3, by omega⟩
        · obtain ⟨e, rfl⟩ : ∃ e, E = e + (3 * j + 5) := ⟨E - (3 * j + 5), by omega⟩
          refine ⟨⟨0, 0, 0, 6 * j + 12, e + 6 * j + 10⟩,
            ⟨6 * j + 12, e + 6 * j + 10, rfl, by omega, by omega⟩, ?_⟩
          show ⟨0, 0, 0, 2 * (3 * j + 5) + 1, e + (3 * j + 5)⟩ [fm]⊢⁺ _
          rw [show 2 * (3 * j + 5) + 1 = 6 * j + 11 from by ring,
              show e + (3 * j + 5) = e + 3 * j + 5 from by ring]
          exact odd_c0 j
        · obtain ⟨e, rfl⟩ : ∃ e, E = e + (3 * j + 6) := ⟨E - (3 * j + 6), by omega⟩
          refine ⟨⟨0, 0, 0, 6 * j + 13, e + 6 * j + 12⟩,
            ⟨6 * j + 13, e + 6 * j + 12, rfl, by omega, by omega⟩, ?_⟩
          show ⟨0, 0, 0, 2 * (3 * j + 6) + 1, e + (3 * j + 6)⟩ [fm]⊢⁺ _
          rw [show 2 * (3 * j + 6) + 1 = 6 * j + 13 from by ring,
              show e + (3 * j + 6) = e + 3 * j + 6 from by ring]
          exact odd_c1 j
        · obtain ⟨e, rfl⟩ : ∃ e, E = e + (3 * j + 7) := ⟨E - (3 * j + 7), by omega⟩
          refine ⟨⟨0, 0, 0, 6 * j + 14, e + 6 * j + 14⟩,
            ⟨6 * j + 14, e + 6 * j + 14, rfl, by omega, by omega⟩, ?_⟩
          show ⟨0, 0, 0, 2 * (3 * j + 7) + 1, e + (3 * j + 7)⟩ [fm]⊢⁺ _
          rw [show 2 * (3 * j + 7) + 1 = 6 * j + 15 from by ring,
              show e + (3 * j + 7) = e + 3 * j + 7 from by ring]
          exact odd_c2 j
  · exact ⟨2, 1, rfl, by omega, by omega⟩

end Sz22_2003_unofficial_1205
