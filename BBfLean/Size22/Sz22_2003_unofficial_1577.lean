import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #1577: [7/45, 5/77, 242/5, 3/11, 35/2]

Vector representation:
```
 0 -2 -1  1  0
 0  0  1 -1 -1
 1  0 -1  0  2
 0  1  0  0 -1
-1  0  1  1  0
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_1577

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a, b+2, c+1, d, e⟩ => some ⟨a, b, c, d+1, e⟩
  | ⟨a, b, c, d+1, e+1⟩ => some ⟨a, b, c+1, d, e⟩
  | ⟨a, b, c+1, d, e⟩ => some ⟨a+1, b, c, d, e+2⟩
  | ⟨a, b, c, d, e+1⟩ => some ⟨a, b+1, c, d, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b, c+1, d+1, e⟩
  | _ => none

-- R4 chain: transfer e to b (c=0, d=0)
theorem e_to_b : ∀ k a b, ⟨a, b, 0, 0, k⟩ [fm]⊢* ⟨a, b + k, 0, 0, 0⟩ := by
  intro k; induction' k with k ih <;> intro a b
  · exists 0
  · rw [Nat.add_succ]
    step fm
    apply stepStar_trans (ih a (b + 1)); ring_nf; finish

-- R5R1 even drain: (a+m, 2m, 0, d, 0) ⊢* (a, 0, 0, d+2m, 0)
theorem r5r1_even : ∀ m a d, ⟨a + m, 2 * m, 0, d, 0⟩ [fm]⊢* ⟨a, 0, 0, d + 2 * m, 0⟩ := by
  intro m; induction' m with m ih <;> intro a d
  · exists 0
  · rw [show a + (m + 1) = (a + m) + 1 from by ring,
        show 2 * (m + 1) = (2 * m) + 2 from by ring]
    step fm; step fm
    apply stepStar_trans (ih a (d + 2)); ring_nf; finish

-- R5R1 odd drain: (a+k, 2k+1, 0, d, 0) ⊢* (a, 1, 0, d+2k, 0)
theorem r5r1_odd : ∀ k a d, ⟨a + k, 2 * k + 1, 0, d, 0⟩ [fm]⊢* ⟨a, 1, 0, d + 2 * k, 0⟩ := by
  intro k; induction' k with k ih <;> intro a d
  · exists 0
  · rw [show a + (k + 1) = (a + k) + 1 from by ring,
        show 2 * (k + 1) + 1 = (2 * k + 1) + 2 from by ring]
    step fm; step fm
    apply stepStar_trans (ih a (d + 2)); ring_nf; finish

-- R2R2R3 chain with b=1: (a, 1, c, 2j+1, 2) ⊢* (a+j, 1, c+j, 1, 2)
theorem r2r2r3_b1 : ∀ j a c, ⟨a, 1, c, 2 * j + 1, 2⟩ [fm]⊢* ⟨a + j, 1, c + j, 1, 2⟩ := by
  intro j; induction' j with j ih <;> intro a c
  · exists 0
  · rw [show 2 * (j + 1) + 1 = (2 * j + 1) + 2 from by ring]
    step fm; step fm; step fm
    apply stepStar_trans (ih (a + 1) (c + 1)); ring_nf; finish

-- R2R2R3 chain with b=0: (a, 0, c, 2j+1, 2) ⊢* (a+j, 0, c+j, 1, 2)
theorem r2r2r3_b0 : ∀ j a c, ⟨a, 0, c, 2 * j + 1, 2⟩ [fm]⊢* ⟨a + j, 0, c + j, 1, 2⟩ := by
  intro j; induction' j with j ih <;> intro a c
  · exists 0
  · rw [show 2 * (j + 1) + 1 = (2 * j + 1) + 2 from by ring]
    step fm; step fm; step fm
    apply stepStar_trans (ih (a + 1) (c + 1)); ring_nf; finish

-- R3 drain with b=1, d=0: (a, 1, c+k, 0, e) ⊢* (a+k, 1, c, 0, e+2k)
theorem r3_drain_b1 : ∀ k a c e, ⟨a, 1, c + k, 0, e⟩ [fm]⊢* ⟨a + k, 1, c, 0, e + 2 * k⟩ := by
  intro k; induction' k with k ih <;> intro a c e
  · exists 0
  · rw [show c + (k + 1) = (c + k) + 1 from by ring]
    step fm
    apply stepStar_trans (ih (a + 1) c (e + 2)); ring_nf; finish

-- R3 drain with b=0, d=0: (a, 0, c+k, 0, e) ⊢* (a+k, 0, c, 0, e+2k)
theorem r3_drain_b0 : ∀ k a c e, ⟨a, 0, c + k, 0, e⟩ [fm]⊢* ⟨a + k, 0, c, 0, e + 2 * k⟩ := by
  intro k; induction' k with k ih <;> intro a c e
  · exists 0
  · rw [show c + (k + 1) = (c + k) + 1 from by ring]
    step fm
    apply stepStar_trans (ih (a + 1) c (e + 2)); ring_nf; finish

-- Main transition: C(n) ⊢⁺ C(n+1)
-- C(n) = (3n²+3n+2, 0, 0, 0, 6n+3)
-- C(n+1) = (3n²+9n+8, 0, 0, 0, 6n+9)
theorem main_trans (n : ℕ) :
    ⟨3 * n * n + 3 * n + 2, 0, 0, 0, 6 * n + 3⟩ [fm]⊢⁺
    ⟨3 * n * n + 9 * n + 8, 0, 0, 0, 6 * n + 9⟩ := by
  -- Phase 1: R4 first step then chain: e -> b
  rw [show (6 * n + 3 : ℕ) = (6 * n + 2) + 1 from by ring]
  step fm
  apply stepStar_trans (e_to_b (6 * n + 2) (3 * n * n + 3 * n + 2) 1)
  -- At (3n²+3n+2, 6n+3, 0, 0, 0) with b = 6n+3 = 2(3n+1)+1 odd
  -- Phase 2a: R5R1 odd drain: (a+k, 2k+1, 0, 0, 0) -> (a, 1, 0, 2k, 0)
  rw [show 1 + (6 * n + 2) = 2 * (3 * n + 1) + 1 from by ring,
      show 3 * n * n + 3 * n + 2 = (3 * n * n + 1) + (3 * n + 1) from by ring]
  apply stepStar_trans (r5r1_odd (3 * n + 1) (3 * n * n + 1) 0)
  -- At (3n²+1, 1, 0, 6n+2, 0)
  rw [show 0 + 2 * (3 * n + 1) = 6 * n + 2 from by ring]
  -- Phase 2b: R5 then R3
  rw [show 3 * n * n + 1 = (3 * n * n) + 1 from by ring]
  step fm
  rw [show 6 * n + 2 + 1 = 6 * n + 3 from by ring]
  step fm
  -- At (3n²+1, 1, 0, 6n+3, 2)
  -- Phase 2c: R2R2R3 chain with b=1
  rw [show (6 * n + 3 : ℕ) = 2 * (3 * n + 1) + 1 from by ring,
      show 3 * n * n + 0 + 1 = 3 * n * n + 1 from by ring]
  apply stepStar_trans (r2r2r3_b1 (3 * n + 1) (3 * n * n + 1) 0)
  -- At (3n²+3n+2, 1, 3n+1, 1, 2)
  rw [show 3 * n * n + 1 + (3 * n + 1) = 3 * n * n + 3 * n + 2 from by ring,
      show 0 + (3 * n + 1) = 3 * n + 1 from by ring]
  -- Phase 2d: R2 then R3
  step fm; step fm
  -- At (3n²+3n+3, 1, 3n+1, 0, 3)
  rw [show 3 * n * n + 3 * n + 2 + 1 = 3 * n * n + 3 * n + 3 from by ring,
      show (3 * n + 1 : ℕ) = 0 + (3 * n + 1) from by ring]
  -- Phase 2e: R3 drain with b=1
  apply stepStar_trans (r3_drain_b1 (3 * n + 1) (3 * n * n + 3 * n + 3) 0 3)
  -- At (3n²+6n+4, 1, 0, 0, 6n+5)
  rw [show 3 * n * n + 3 * n + 3 + (3 * n + 1) = 3 * n * n + 6 * n + 4 from by ring,
      show 3 + 2 * (3 * n + 1) = 6 * n + 5 from by ring]
  -- Phase 3: R4 chain, e -> b
  rw [show (6 * n + 5 : ℕ) = (6 * n + 4) + 1 from by ring]
  step fm
  apply stepStar_trans (e_to_b (6 * n + 4) (3 * n * n + 6 * n + 4) 2)
  -- At (3n²+6n+4, 6n+6, 0, 0, 0) with b = 6n+6 = 2(3n+3) even
  -- Phase 4: R5R1 even drain: (a+m, 2m, 0, 0, 0) -> (a, 0, 0, 2m, 0)
  rw [show 2 + (6 * n + 4) = 2 * (3 * n + 3) from by ring,
      show 3 * n * n + 6 * n + 4 = (3 * n * n + 3 * n + 1) + (3 * n + 3) from by ring]
  apply stepStar_trans (r5r1_even (3 * n + 3) (3 * n * n + 3 * n + 1) 0)
  -- At (3n²+3n+1, 0, 0, 6n+6, 0)
  rw [show 0 + 2 * (3 * n + 3) = 6 * n + 6 from by ring]
  -- Phase 5: R5 then R3
  rw [show 3 * n * n + 3 * n + 1 = (3 * n * n + 3 * n) + 1 from by ring]
  step fm
  rw [show 6 * n + 6 + 1 = 6 * n + 7 from by ring]
  step fm
  -- At (3n²+3n+1, 0, 0, 6n+7, 2)
  -- Phase 6a: R2R2R3 chain with b=0
  rw [show (6 * n + 7 : ℕ) = 2 * (3 * n + 3) + 1 from by ring,
      show 3 * n * n + 3 * n + 0 + 1 = 3 * n * n + 3 * n + 1 from by ring]
  apply stepStar_trans (r2r2r3_b0 (3 * n + 3) (3 * n * n + 3 * n + 1) 0)
  -- At (3n²+6n+4, 0, 3n+3, 1, 2)
  rw [show 3 * n * n + 3 * n + 1 + (3 * n + 3) = 3 * n * n + 6 * n + 4 from by ring,
      show 0 + (3 * n + 3) = 3 * n + 3 from by ring]
  -- Phase 6b: R2 then R3
  step fm; step fm
  -- At (3n²+6n+5, 0, 3n+3, 0, 3)
  rw [show 3 * n * n + 6 * n + 4 + 1 = 3 * n * n + 6 * n + 5 from by ring,
      show (3 * n + 3 : ℕ) = 0 + (3 * n + 3) from by ring]
  -- Phase 6c: R3 drain with b=0
  apply stepStar_trans (r3_drain_b0 (3 * n + 3) (3 * n * n + 6 * n + 5) 0 3)
  rw [show 3 * n * n + 6 * n + 5 + (3 * n + 3) = 3 * n * n + 9 * n + 8 from by ring,
      show 3 + 2 * (3 * n + 3) = 6 * n + 9 from by ring]
  finish

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨2, 0, 0, 0, 3⟩)
  · execute fm 4
  apply progress_nonhalt_simple (fm := fm) (A := ℕ)
    (fun n ↦ ⟨3 * n * n + 3 * n + 2, 0, 0, 0, 6 * n + 3⟩) 0
  intro n; exact ⟨n + 1, by
    rw [show 3 * (n + 1) * (n + 1) + 3 * (n + 1) + 2 = 3 * n * n + 9 * n + 8 from by ring,
        show 6 * (n + 1) + 3 = 6 * n + 9 from by ring]
    exact main_trans n⟩

end Sz22_2003_unofficial_1577
