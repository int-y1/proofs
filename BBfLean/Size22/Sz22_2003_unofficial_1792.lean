import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #1792: [9/10, 44/21, 91/2, 5/11, 33/13]

Vector representation:
```
-1  2 -1  0  0  0
 2 -1  0 -1  1  0
-1  0  0  1  0  1
 0  0  1  0 -1  0
 0  1  0  0  1 -1
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_1792

def Q := ℕ × ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a+1, b, c+1, d, e, f⟩ => some ⟨a, b+2, c, d, e, f⟩
  | ⟨a, b+1, c, d+1, e, f⟩ => some ⟨a+2, b, c, d, e+1, f⟩
  | ⟨a+1, b, c, d, e, f⟩ => some ⟨a, b, c, d+1, e, f+1⟩
  | ⟨a, b, c, d, e+1, f⟩ => some ⟨a, b, c+1, d, e, f⟩
  | ⟨a, b, c, d, e, f+1⟩ => some ⟨a, b+1, c, d, e+1, f⟩
  | _ => none

-- R4 repeated: move e to c
theorem e_to_c : ∀ k, ⟨(0 : ℕ), 0, c, d, e + k, f⟩ [fm]⊢* ⟨0, 0, c + k, d, e, f⟩ := by
  intro k; induction' k with k ih generalizing c
  · exists 0
  · rw [show e + (k + 1) = (e + k) + 1 from by ring]
    step fm
    apply stepStar_trans (ih (c := c + 1))
    ring_nf; finish

-- R1R1R2 chain: each round does R1,R1,R2
theorem r1r1r2_chain : ∀ k, ⟨(2 : ℕ), b, c + 2 * k, d + k, e, f⟩ [fm]⊢*
    ⟨2, b + 3 * k, c, d, e + k, f⟩ := by
  intro k; induction' k with k ih generalizing b c d e
  · exists 0
  · rw [show c + 2 * (k + 1) = (c + 2) + 2 * k from by ring,
        show d + (k + 1) = (d + 1) + k from by ring]
    apply stepStar_trans (ih (b := b) (c := c + 2) (d := d + 1) (e := e))
    step fm; step fm; step fm
    ring_nf; finish

-- R2 drain: drain d using b
theorem r2_drain : ∀ k, ⟨a, b + k, (0 : ℕ), d + k, e, f⟩ [fm]⊢*
    ⟨a + 2 * k, b, 0, d, e + k, f⟩ := by
  intro k; induction' k with k ih generalizing a e
  · exists 0
  · rw [show b + (k + 1) = (b + k) + 1 from by ring,
        show d + (k + 1) = (d + k) + 1 from by ring]
    step fm  -- R2: (a+2, b+k, 0, d+k, e+1, f)
    apply stepStar_trans (ih (a := a + 2) (e := e + 1))
    ring_nf; finish

-- R3R2 drain: alternate R3 and R2
theorem r3r2_drain : ∀ k, ⟨a + 2, k, (0 : ℕ), 0, e, f⟩ [fm]⊢*
    ⟨a + k + 2, 0, 0, 0, e + k, f + k⟩ := by
  intro k; induction' k with k ih generalizing a e f
  · exists 0
  · -- state: (a+2, k+1, 0, 0, e, f)
    -- R3: needs a+2 >= 1. Pattern (a'+1, b, c, d, e, f) with a' = a+1.
    step fm  -- R3: ((a+2)-1, k+1, 0, 0+1, e, f+1) = (a+1, k+1, 0, 1, e, f+1)
    -- R2: needs b >= 1 (k+1 >= 1) and d >= 1 (1 >= 1)
    step fm  -- R2: (a+3, k, 0, 0, e+1, f+1)
    rw [show a + 3 = (a + 1) + 2 from by ring]
    apply stepStar_trans (ih (a := a + 1) (e := e + 1) (f := f + 1))
    ring_nf; finish

-- R3 chain: drain a to d and f
theorem r3_chain : ∀ k, ⟨k, (0 : ℕ), 0, d, e, f⟩ [fm]⊢*
    ⟨0, 0, 0, d + k, e, f + k⟩ := by
  intro k; induction' k with k ih generalizing d f
  · exists 0
  · -- state: (k+1, 0, 0, d, e, f). R3 fires.
    step fm  -- R3: (k, 0, 0, d+1, e, f+1)
    apply stepStar_trans (ih (d := d + 1) (f := f + 1))
    ring_nf; finish

-- Main transition
theorem main_trans (hGH : G + H = 3 * (E + 1)) :
    ⟨(0 : ℕ), 0, 0, G + E + 2, 2 * E + 2, F + 1⟩ [fm]⊢⁺
    ⟨0, 0, 0, G + 3 * E + 5, 4 * E + 6, F + 6 * E + 8⟩ := by
  -- Phase 1: R4 chain + R5 (gives ⊢⁺)
  apply stepStar_stepPlus_stepPlus
  · rw [show (2 * E + 2 : ℕ) = 0 + (2 * E + 2) from by ring]
    exact e_to_c (2 * E + 2) (c := 0) (d := G + E + 2) (e := 0) (f := F + 1)
  rw [show (0 : ℕ) + (2 * E + 2) = 2 * E + 2 from by ring]
  -- now at (0, 0, 2E+2, G+E+2, 0, F+1), goal is ⊢⁺
  -- R5 step
  step fm
  -- now at (0, 1, 2E+2, G+E+2, 1, F), goal is ⊢*
  -- R2 step
  step fm
  -- now at (2, 0, 2E+2, G+E+1, 2, F), goal is ⊢*
  -- R1R1R2 chain
  rw [show (2 * E + 2 : ℕ) = 0 + 2 * (E + 1) from by ring,
      show G + E + 1 = G + (E + 1) from by ring]
  apply stepStar_trans (r1r1r2_chain (E + 1) (b := 0) (c := 0) (d := G) (e := 2) (f := F))
  rw [show (0 : ℕ) + 3 * (E + 1) = H + G from by omega,
      show (2 : ℕ) + (E + 1) = E + 3 from by ring]
  -- R2 drain G
  rw [show H + G = H + G from rfl]
  have hr2 := r2_drain G (a := 2) (b := H) (d := 0) (e := E + 3) (f := F)
  simp only [Nat.zero_add] at hr2
  apply stepStar_trans hr2
  rw [show (2 : ℕ) + 2 * G = 2 * G + 2 from by ring]
  -- R3R2 drain H
  apply stepStar_trans (r3r2_drain H (a := 2 * G) (e := E + 3 + G) (f := F))
  -- R3 chain
  apply stepStar_trans (r3_chain (2 * G + H + 2) (d := 0) (e := E + 3 + G + H) (f := F + H))
  rw [show (0 : ℕ) + (2 * G + H + 2) = G + 3 * E + 5 from by omega,
      show E + 3 + G + H = 4 * E + 6 from by omega,
      show F + H + (2 * G + H + 2) = F + 6 * E + 8 from by omega]
  finish

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨0, 0, 0, 2, 2, 2⟩)
  · execute fm 5
  apply progress_nonhalt (fm := fm)
    (P := fun q ↦ ∃ G H E F, q = ⟨0, 0, 0, G + E + 2, 2 * E + 2, F + 1⟩ ∧
      G + H = 3 * (E + 1))
  · intro c ⟨G, H, E, F, hq, hGH⟩
    subst hq
    exact ⟨⟨0, 0, 0, G + 3 * E + 5, 4 * E + 6, F + 6 * E + 8⟩,
      ⟨G + E + 1, H + 2 * E + 5, 2 * E + 2, 6 * E + F + 7, by ring_nf, by omega⟩,
      main_trans hGH⟩
  · exact ⟨0, 3, 0, 1, by ring_nf, by omega⟩

end Sz22_2003_unofficial_1792
