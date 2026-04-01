import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #1455: [7/15, 3/154, 275/7, 2/5, 147/2]

Vector representation:
```
 0 -1 -1  1  0
-1  1  0 -1 -1
 0  0  2 -1  1
 1  0 -1  0  0
-1  1  0  2  0
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_1455

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a, b+1, c+1, d, e⟩ => some ⟨a, b, c, d+1, e⟩
  | ⟨a+1, b, c, d+1, e+1⟩ => some ⟨a, b+1, c, d, e⟩
  | ⟨a, b, c, d+1, e⟩ => some ⟨a, b, c+2, d, e+1⟩
  | ⟨a, b, c+1, d, e⟩ => some ⟨a+1, b, c, d, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b+1, c, d+2, e⟩
  | _ => none

-- R5+R2+R2 chain: each round consumes 3 from a and 2 from e.
theorem r5r2r2_chain : ∀ k, ⟨a + 3 * k, b, 0, 0, e + 2 * k⟩ [fm]⊢* ⟨a, b + 3 * k, 0, 0, e⟩ := by
  intro k; induction' k with k ih generalizing a b e
  · exists 0
  · rw [show a + 3 * (k + 1) = (a + 3 * k) + 3 from by ring,
        show e + 2 * (k + 1) = (e + 2 * k) + 2 from by ring]
    step fm; step fm; step fm
    apply stepStar_trans (ih (b := b + 3)); ring_nf; finish

-- R3+R1+R1 interleave: each round decreases b by 2, increases d and e by 1.
theorem r3r1r1_chain : ∀ k, ⟨0, b + 2 * k, 0, d + 1, e⟩ [fm]⊢* ⟨0, b, 0, d + k + 1, e + k⟩ := by
  intro k; induction' k with k ih generalizing b d e
  · exists 0
  · rw [show b + 2 * (k + 1) = (b + 2 * k) + 2 from by ring]
    step fm; step fm; step fm
    rw [show d + 2 = (d + 1) + 1 from by ring]
    apply stepStar_trans (ih (d := d + 1) (e := e + 1)); ring_nf; finish

-- R3 drain: converts d to c and e.
theorem r3_drain : ∀ k, ⟨0, 0, c, d + k, e⟩ [fm]⊢* ⟨0, 0, c + 2 * k, d, e + k⟩ := by
  intro k; induction' k with k ih generalizing c d e
  · exists 0
  · rw [Nat.add_succ d k]; step fm
    apply stepStar_trans (ih (c := c + 2) (e := e + 1)); ring_nf; finish

-- R4 chain: converts c to a.
theorem r4_chain : ∀ k, ⟨a, 0, c + k, 0, e⟩ [fm]⊢* ⟨a + k, 0, c, 0, e⟩ := by
  intro k; induction' k with k ih generalizing a c e
  · exists 0
  · rw [show c + (k + 1) = (c + k) + 1 from by ring]; step fm
    apply stepStar_trans (ih (a := a + 1)); ring_nf; finish

-- Phase 234 for d=1 odd b: (0, 2n+1, 0, 1, e) ⊢* (2n+3, 0, 0, 0, e+2n+2)
theorem phase234_d1 (n : ℕ) :
    ⟨0, 2 * n + 1, 0, 1, e⟩ [fm]⊢* ⟨2 * n + 3, 0, 0, 0, e + 2 * n + 2⟩ := by
  rw [show 2 * n + 1 = 1 + 2 * n from by ring, show (1 : ℕ) = 0 + 1 from by ring]
  apply stepStar_trans (r3r1r1_chain n (b := 1) (d := 0) (e := e))
  rw [show 0 + n + 1 = n + 1 from by ring]
  step fm; step fm
  rw [show n + 1 = 0 + (n + 1) from by ring]
  apply stepStar_trans (r3_drain (n + 1) (c := 1) (d := 0) (e := e + n + 1))
  rw [show 1 + 2 * (n + 1) = 0 + (2 * n + 3) from by ring,
      show e + n + 1 + (n + 1) = e + 2 * n + 2 from by ring]
  apply stepStar_trans (r4_chain (2 * n + 3) (a := 0) (c := 0) (e := e + 2 * n + 2))
  ring_nf; finish

-- Phase 234 for d=2 odd b: (0, 2n+1, 0, 2, e) ⊢* (2n+5, 0, 0, 0, e+2n+3)
theorem phase234_d2 (n : ℕ) :
    ⟨0, 2 * n + 1, 0, 2, e⟩ [fm]⊢* ⟨2 * n + 5, 0, 0, 0, e + 2 * n + 3⟩ := by
  rw [show 2 * n + 1 = 1 + 2 * n from by ring, show (2 : ℕ) = 1 + 1 from by ring]
  apply stepStar_trans (r3r1r1_chain n (b := 1) (d := 1) (e := e))
  rw [show 1 + n + 1 = (n + 1) + 1 from by ring]
  step fm; step fm
  rw [show n + 1 + 1 = 0 + (n + 2) from by ring]
  apply stepStar_trans (r3_drain (n + 2) (c := 1) (d := 0) (e := e + n + 1))
  rw [show 1 + 2 * (n + 2) = 0 + (2 * n + 5) from by ring,
      show e + n + 1 + (n + 2) = e + 2 * n + 3 from by ring]
  apply stepStar_trans (r4_chain (2 * n + 5) (a := 0) (c := 0) (e := e + 2 * n + 3))
  ring_nf; finish

-- Main transition: C(m) ⊢⁺ C(m+1)
-- C(m) = (6m+5, 0, 0, 0, 2m²+6m+3)
-- First half: → (6m+7, 0, 0, 0, 2m²+8m+6)
-- Second half: → (6m+11, 0, 0, 0, 2m²+10m+11) = C(m+1)
theorem main_trans (m : ℕ) :
    ⟨6 * m + 5, 0, 0, 0, 2 * m ^ 2 + 6 * m + 3⟩ [fm]⊢⁺
    ⟨6 * m + 11, 0, 0, 0, 2 * m ^ 2 + 10 * m + 11⟩ := by
  -- First R5+R2+R2 for ⊢⁺
  rw [show 6 * m + 5 = (6 * m + 2) + 3 from by ring,
      show 2 * m ^ 2 + 6 * m + 3 = (2 * m ^ 2 + 6 * m + 1) + 2 from by ring]
  step fm; step fm; step fm
  -- Now at (6m+2, 3, 0, 0, 2m²+6m+1)
  -- r5r2r2_chain 2m: (6m+2, 3, 0, 0, 2m²+6m+1) = (2+3(2m), 3, 0, 0, (2m²+2m+1)+2(2m))
  --   → (2, 6m+3, 0, 0, 2m²+2m+1)
  rw [show 6 * m + 2 = 2 + 3 * (2 * m) from by ring,
      show 2 * m ^ 2 + 6 * m + 1 = (2 * m ^ 2 + 2 * m + 1) + 2 * (2 * m) from by ring]
  apply stepStar_trans (r5r2r2_chain (2 * m) (a := 2) (b := 3) (e := 2 * m ^ 2 + 2 * m + 1))
  rw [show 3 + 3 * (2 * m) = 6 * m + 3 from by ring]
  -- tail_a2: (2, 6m+3, 0, 0, 2m²+2m+1) = (2, 6m+3, 0, 0, (2m²+2m)+1)
  --   → (0, 6m+5, 0, 1, 2m²+2m)
  rw [show 2 * m ^ 2 + 2 * m + 1 = (2 * m ^ 2 + 2 * m) + 1 from by ring]
  step fm; step fm  -- R5, R2
  -- phase234_d1 (3m+2): (0, 6m+5, 0, 1, 2m²+2m) → (6m+7, 0, 0, 0, 2m²+8m+6)
  rw [show 6 * m + 3 + 2 = 2 * (3 * m + 2) + 1 from by ring]
  apply stepStar_trans (phase234_d1 (3 * m + 2) (e := 2 * m ^ 2 + 2 * m))
  rw [show 2 * (3 * m + 2) + 3 = 6 * m + 7 from by ring,
      show 2 * m ^ 2 + 2 * m + 2 * (3 * m + 2) + 2 = 2 * m ^ 2 + 8 * m + 6 from by ring]
  -- Second half: (6m+7, 0, 0, 0, 2m²+8m+6) → (6m+11, 0, 0, 0, 2m²+10m+11)
  -- r5r2r2_chain (2m+1): a=4, b=0
  rw [show 6 * m + 7 = 4 + 3 * (2 * m + 1) from by ring,
      show 2 * m ^ 2 + 8 * m + 6 = (2 * m ^ 2 + 4 * m + 4) + 2 * (2 * m + 1) from by ring]
  apply stepStar_trans (r5r2r2_chain (2 * m + 1) (a := 4) (b := 0) (e := 2 * m ^ 2 + 4 * m + 4))
  rw [show 0 + 3 * (2 * m + 1) = 6 * m + 3 from by ring]
  -- tail_a4: (4, 6m+3, 0, 0, (2m²+4m+2)+2) → (0, 6m+7, 0, 2, 2m²+4m+2)
  rw [show 2 * m ^ 2 + 4 * m + 4 = (2 * m ^ 2 + 4 * m + 2) + 2 from by ring]
  step fm; step fm; step fm; step fm  -- R5, R2, R2, R5
  -- phase234_d2 (3m+3): (0, 6m+7, 0, 2, 2m²+4m+2) → (6m+11, 0, 0, 0, 2m²+10m+11)
  rw [show 6 * m + 3 + 4 = 2 * (3 * m + 3) + 1 from by ring]
  apply stepStar_trans (phase234_d2 (3 * m + 3) (e := 2 * m ^ 2 + 4 * m + 2))
  rw [show 2 * (3 * m + 3) + 5 = 6 * m + 11 from by ring,
      show 2 * m ^ 2 + 4 * m + 2 + 2 * (3 * m + 3) + 3 = 2 * m ^ 2 + 10 * m + 11 from by ring]
  finish

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨5, 0, 0, 0, 3⟩)
  · execute fm 10
  show ¬halts fm (6 * 0 + 5, 0, 0, 0, 2 * 0 ^ 2 + 6 * 0 + 3)
  apply progress_nonhalt_simple (fm := fm) (A := ℕ)
    (fun m ↦ ⟨6 * m + 5, 0, 0, 0, 2 * m ^ 2 + 6 * m + 3⟩) 0
  intro m; refine ⟨m + 1, ?_⟩
  rw [show 6 * (m + 1) + 5 = 6 * m + 11 from by ring,
      show 2 * (m + 1) ^ 2 + 6 * (m + 1) + 3 = 2 * m ^ 2 + 10 * m + 11 from by ring]
  exact main_trans m

end Sz22_2003_unofficial_1455
