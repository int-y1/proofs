import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #1848: [9/35, 1/363, 10/3, 11/10, 147/2]

Vector representation:
```
 0  2 -1 -1  0
 0 -1  0  0 -2
 1 -1  1  0  0
-1  0 -1  0  1
-1  1  0  2  0
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_1848

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a, b, c+1, d+1, e⟩ => some ⟨a, b+2, c, d, e⟩
  | ⟨a, b+1, c, d, e+2⟩ => some ⟨a, b, c, d, e⟩
  | ⟨a, b+1, c, d, e⟩ => some ⟨a+1, b, c+1, d, e⟩
  | ⟨a+1, b, c+1, d, e⟩ => some ⟨a, b, c, d, e+1⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b+1, c, d+2, e⟩
  | _ => none

-- R5+R2 drain: each step decreases a by 1, increases d by 2, decreases e by 2
theorem drain_even : ∀ k, ⟨a + k, 0, 0, d, 2 * k⟩ [fm]⊢* ⟨a, 0, 0, d + 2 * k, 0⟩ := by
  intro k; induction' k with k ih generalizing a d
  · exists 0
  · rw [show a + (k + 1) = a + k + 1 from by ring,
        show 2 * (k + 1) = 2 * k + 2 from by ring]
    step fm; step fm
    apply stepStar_trans (ih (d := d + 2)); ring_nf; finish

theorem drain_odd : ∀ k, ⟨a + k, 0, 0, d, 2 * k + 1⟩ [fm]⊢* ⟨a, 0, 0, d + 2 * k, 1⟩ := by
  intro k; induction' k with k ih generalizing a d
  · exists 0
  · rw [show a + (k + 1) = a + k + 1 from by ring,
        show 2 * (k + 1) + 1 = 2 * k + 1 + 2 from by ring]
    step fm; step fm
    apply stepStar_trans (ih (d := d + 2)); ring_nf; finish

-- R1+R3 spiral with e=0: each round increases a and j by 1, decreases d by 1
theorem spiral0 : ∀ d, ⟨a, j, 1, d + 1, 0⟩ [fm]⊢* ⟨a + d + 1, j + d + 1, 1, 0, 0⟩ := by
  intro d; induction' d with d ih generalizing a j
  · execute fm 2
  · rw [show (d + 1 + 1 : ℕ) = (d + 1) + 1 from rfl]
    step fm; step fm
    apply stepStar_trans (ih (a := a + 1) (j := j + 1)); ring_nf; finish

theorem spiral1 : ∀ d, ⟨a, j, 1, d + 1, 1⟩ [fm]⊢* ⟨a + d + 1, j + d + 1, 1, 0, 1⟩ := by
  intro d; induction' d with d ih generalizing a j
  · execute fm 2
  · rw [show (d + 1 + 1 : ℕ) = (d + 1) + 1 from rfl]
    step fm; step fm
    apply stepStar_trans (ih (a := a + 1) (j := j + 1)); ring_nf; finish

-- R3 chain with e=0: b transfers to a and c
theorem r3_chain0 : ∀ k, ⟨a, b + k, c, 0, 0⟩ [fm]⊢* ⟨a + k, b, c + k, 0, 0⟩ := by
  intro k; induction' k with k ih generalizing a b c
  · exists 0
  · rw [Nat.add_succ b k]
    step fm
    apply stepStar_trans (ih (a := a + 1) (c := c + 1)); ring_nf; finish

-- R3 chain with e=1: b transfers to a and c
theorem r3_chain1 : ∀ k, ⟨a, b + k, c, 0, 1⟩ [fm]⊢* ⟨a + k, b, c + k, 0, 1⟩ := by
  intro k; induction' k with k ih generalizing a b c
  · exists 0
  · rw [Nat.add_succ b k]
    step fm
    apply stepStar_trans (ih (a := a + 1) (c := c + 1)); ring_nf; finish

-- R4 chain: a and c transfer to e
theorem r4_chain : ∀ k, ⟨a + k, 0, c + k, 0, e⟩ [fm]⊢* ⟨a, 0, c, 0, e + k⟩ := by
  intro k; induction' k with k ih generalizing a c e
  · exists 0
  · rw [show a + (k + 1) = a + k + 1 from by ring,
        show c + (k + 1) = c + k + 1 from by ring]
    step fm
    apply stepStar_trans (ih (e := e + 1)); ring_nf; finish

-- (F+k+1, 0, 0, 0, 2k) →⁺ (F+2k+2, 0, 0, 0, 2k+3)
theorem half_even (F k : ℕ) :
    ⟨F + k + 1, 0, 0, 0, 2 * k⟩ [fm]⊢⁺ ⟨F + 2 * k + 2, 0, 0, 0, 2 * k + 3⟩ := by
  rw [show F + k + 1 = (F + 1) + k from by ring]
  apply stepStar_stepPlus_stepPlus (drain_even k (a := F + 1) (d := 0))
  rw [show 0 + 2 * k = 2 * k from by ring]
  step fm; step fm
  rw [show 2 * k + 2 = (2 * k + 1) + 1 from by ring]
  apply stepStar_trans (spiral0 (2 * k + 1) (a := F + 1) (j := 0))
  rw [show F + 1 + (2 * k + 1) + 1 = F + 2 * k + 3 from by ring,
      show 0 + (2 * k + 1) + 1 = 2 * k + 2 from by ring]
  rw [show (2 * k + 2 : ℕ) = 0 + (2 * k + 2) from by ring]
  apply stepStar_trans (r3_chain0 (2 * k + 2) (a := F + 2 * k + 3) (b := 0) (c := 1))
  rw [show F + 2 * k + 3 + (2 * k + 2) = (F + 2 * k + 2) + (2 * k + 3) from by ring,
      show 1 + (2 * k + 2) = 0 + (2 * k + 3) from by ring]
  apply stepStar_trans (r4_chain (2 * k + 3) (a := F + 2 * k + 2) (c := 0) (e := 0))
  rw [show 0 + (2 * k + 3) = 2 * k + 3 from by ring]; finish

-- (G+k+2, 0, 0, 0, 2k+3) →⁺ (G+2k+4, 0, 0, 0, 2k+6)
theorem half_odd (G k : ℕ) :
    ⟨G + k + 2, 0, 0, 0, 2 * k + 3⟩ [fm]⊢⁺ ⟨G + 2 * k + 4, 0, 0, 0, 2 * k + 6⟩ := by
  rw [show G + k + 2 = (G + 1) + (k + 1) from by ring,
      show 2 * k + 3 = 2 * (k + 1) + 1 from by ring]
  apply stepStar_stepPlus_stepPlus (drain_odd (k + 1) (a := G + 1) (d := 0))
  rw [show 0 + 2 * (k + 1) = 2 * k + 2 from by ring]
  step fm; step fm
  rw [show 2 * k + 2 + 2 = (2 * k + 3) + 1 from by ring]
  apply stepStar_trans (spiral1 (2 * k + 3) (a := G + 1) (j := 0))
  rw [show G + 1 + (2 * k + 3) + 1 = G + 2 * k + 5 from by ring,
      show 0 + (2 * k + 3) + 1 = 2 * k + 4 from by ring]
  rw [show (2 * k + 4 : ℕ) = 0 + (2 * k + 4) from by ring]
  apply stepStar_trans (r3_chain1 (2 * k + 4) (a := G + 2 * k + 5) (b := 0) (c := 1))
  rw [show G + 2 * k + 5 + (2 * k + 4) = (G + 2 * k + 4) + (2 * k + 5) from by ring,
      show 1 + (2 * k + 4) = 0 + (2 * k + 5) from by ring]
  apply stepStar_trans (r4_chain (2 * k + 5) (a := G + 2 * k + 4) (c := 0) (e := 1))
  rw [show 1 + (2 * k + 5) = 2 * k + 6 from by ring]; finish

theorem main_trans (F k : ℕ) :
    ⟨F + k + 1, 0, 0, 0, 2 * k⟩ [fm]⊢⁺ ⟨F + 3 * k + 4, 0, 0, 0, 2 * k + 6⟩ := by
  apply stepPlus_trans (half_even F k)
  show ⟨F + 2 * k + 2, 0, 0, 0, 2 * k + 3⟩ [fm]⊢⁺ ⟨F + 3 * k + 4, 0, 0, 0, 2 * k + 6⟩
  rw [show F + 2 * k + 2 = (F + k) + k + 2 from by ring,
      show F + 3 * k + 4 = (F + k) + 2 * k + 4 from by ring]
  exact half_odd (F + k) k

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨4, 0, 0, 0, 6⟩) (by execute fm 32)
  apply progress_nonhalt_simple (fm := fm) (A := ℕ × ℕ)
    (fun ⟨F, k⟩ ↦ ⟨F + k + 1, 0, 0, 0, 2 * k⟩) ⟨0, 3⟩
  intro ⟨F, k⟩
  refine ⟨⟨F + 2 * k, k + 3⟩, ?_⟩
  show ⟨F + k + 1, 0, 0, 0, 2 * k⟩ [fm]⊢⁺ ⟨F + 2 * k + (k + 3) + 1, 0, 0, 0, 2 * (k + 3)⟩
  rw [show F + 2 * k + (k + 3) + 1 = F + 3 * k + 4 from by ring,
      show 2 * (k + 3) = 2 * k + 6 from by ring]
  exact main_trans F k
