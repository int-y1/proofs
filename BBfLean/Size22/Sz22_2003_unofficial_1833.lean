import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #1833: [9/10, 77/2, 4/21, 5/7, 14/11]

Vector representation:
```
-1  2 -1  0  0
-1  0  0  1  1
 2 -1  0 -1  0
 0  0  1 -1  0
 1  0  0  1 -1
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_1833

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a+1, b, c+1, d, e⟩ => some ⟨a, b+2, c, d, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b, c, d+1, e+1⟩
  | ⟨a, b+1, c, d+1, e⟩ => some ⟨a+2, b, c, d, e⟩
  | ⟨a, b, c, d+1, e⟩ => some ⟨a, b, c+1, d, e⟩
  | ⟨a, b, c, d, e+1⟩ => some ⟨a+1, b, c, d+1, e⟩
  | _ => none

theorem r4_chain : ∀ k, ⟨0, 0, c, k, e⟩ [fm]⊢* ⟨0, 0, c + k, 0, e⟩ := by
  intro k; induction' k with k ih generalizing c
  · exists 0
  · step fm
    apply stepStar_trans (ih (c := c + 1)); ring_nf; finish

theorem r2_chain : ∀ a, ⟨a, b, 0, d, e⟩ [fm]⊢* ⟨0, b, 0, d + a, e + a⟩ := by
  intro a; induction' a with a ih generalizing d e
  · exists 0
  · step fm
    apply stepStar_trans (ih (d := d + 1) (e := e + 1)); ring_nf; finish

theorem opening_round : ⟨0, b, c + 3, 0, e + 1⟩ [fm]⊢* ⟨0, b + 5, c, 0, e⟩ := by
  step fm; step fm; step fm; step fm; step fm; finish

theorem opening_core : ∀ k, ⟨0, b, c + 3 * k, 0, e + k⟩ [fm]⊢* ⟨0, b + 5 * k, c, 0, e⟩ := by
  intro k; induction' k with k ih generalizing c e
  · exists 0
  · rw [show c + 3 * (k + 1) = (c + 3) + 3 * k from by ring,
        show e + (k + 1) = (e + 1) + k from by ring]
    apply stepStar_trans (ih (c := c + 3) (e := e + 1))
    apply stepStar_trans (opening_round (b := b + 5 * k) (c := c) (e := e))
    ring_nf; finish

theorem opening_tail1 : ⟨0, b, 1, 0, e + 1⟩ [fm]⊢* ⟨2, b + 1, 0, 0, e⟩ := by
  step fm; step fm; step fm; finish

theorem opening_tail2 : ⟨0, b, 2, 0, e + 1⟩ [fm]⊢* ⟨1, b + 3, 0, 0, e⟩ := by
  step fm; step fm; step fm; step fm; finish

theorem drain_round : ⟨0, b + 1, 0, d + 1, e⟩ [fm]⊢* ⟨0, b, 0, d + 2, e + 2⟩ := by
  step fm; step fm; step fm; finish

theorem drain_core : ∀ k, ⟨0, b + k, 0, d + 1, e⟩ [fm]⊢* ⟨0, b, 0, d + k + 1, e + 2 * k⟩ := by
  intro k; induction' k with k ih generalizing d e
  · exists 0
  · rw [show b + (k + 1) = (b + k) + 1 from by ring]
    apply stepStar_trans (drain_round (b := b + k) (d := d) (e := e))
    apply stepStar_trans (ih (d := d + 1) (e := e + 2))
    ring_nf; finish

-- Case 1: D=3k+1, E=e+3k+1.
theorem trans_case1 : ⟨0, 0, 0, 3 * k + 1, e + 3 * k + 1⟩ [fm]⊢⁺
    ⟨0, 0, 0, 5 * k + 3, e + 12 * k + 4⟩ := by
  rw [show 3 * k + 1 = (3 * k) + 1 from by ring]
  step fm
  apply stepStar_trans (r4_chain (3 * k) (c := 1) (e := e + 3 * k + 1))
  rw [show 1 + 3 * k = 1 + 3 * k from rfl,
      show e + 3 * k + 1 = (e + 2 * k + 1) + k from by ring]
  apply stepStar_trans (opening_core k (b := 0) (c := 1) (e := e + 2 * k + 1))
  rw [show 0 + 5 * k = 5 * k from Nat.zero_add _,
      show e + 2 * k + 1 = (e + 2 * k) + 1 from by ring]
  apply stepStar_trans (opening_tail1 (b := 5 * k) (e := e + 2 * k))
  apply stepStar_trans (r2_chain 2 (b := 5 * k + 1) (d := 0) (e := e + 2 * k))
  rw [show 0 + 2 = 2 from rfl,
      show (2 : ℕ) = 1 + 1 from rfl,
      show (5 * k + 1 : ℕ) = 0 + (5 * k + 1) from (Nat.zero_add _).symm]
  apply stepStar_trans (drain_core (5 * k + 1) (b := 0) (d := 1) (e := e + 2 * k + 2))
  ring_nf; finish

-- Case 2: D=3k+2, E=e+3k+2.
theorem trans_case2 : ⟨0, 0, 0, 3 * k + 2, e + 3 * k + 2⟩ [fm]⊢⁺
    ⟨0, 0, 0, 5 * k + 4, e + 12 * k + 8⟩ := by
  rw [show 3 * k + 2 = (3 * k + 1) + 1 from by ring]
  step fm
  apply stepStar_trans (r4_chain (3 * k + 1) (c := 1) (e := e + 3 * k + 2))
  rw [show 1 + (3 * k + 1) = 2 + 3 * k from by ring,
      show e + 3 * k + 2 = (e + 2 * k + 2) + k from by ring]
  apply stepStar_trans (opening_core k (b := 0) (c := 2) (e := e + 2 * k + 2))
  rw [show 0 + 5 * k = 5 * k from Nat.zero_add _,
      show e + 2 * k + 2 = (e + 2 * k + 1) + 1 from by ring]
  apply stepStar_trans (opening_tail2 (b := 5 * k) (e := e + 2 * k + 1))
  apply stepStar_trans (r2_chain 1 (b := 5 * k + 3) (d := 0) (e := e + 2 * k + 1))
  rw [show 0 + 1 = 1 from rfl,
      show e + 2 * k + 1 + 1 = e + 2 * k + 2 from by ring,
      show (1 : ℕ) = 0 + 1 from rfl,
      show (5 * k + 3 : ℕ) = 0 + (5 * k + 3) from (Nat.zero_add _).symm]
  apply stepStar_trans (drain_core (5 * k + 3) (b := 0) (d := 0) (e := e + 2 * k + 2))
  simp only [Nat.zero_add]; ring_nf; finish

-- Case 3: D=3(k+1), E=e+3(k+1).
theorem trans_case3 : ⟨0, 0, 0, 3 * (k + 1), e + 3 * (k + 1)⟩ [fm]⊢⁺
    ⟨0, 0, 0, 5 * k + 7, e + 12 * k + 12⟩ := by
  rw [show e + 3 * (k + 1) = e + 3 * k + 3 from by ring,
      show 3 * (k + 1) = (3 * k + 2) + 1 from by ring]
  step fm
  apply stepStar_trans (r4_chain (3 * k + 2) (c := 1) (e := e + 3 * k + 3))
  rw [show 1 + (3 * k + 2) = 0 + 3 * (k + 1) from by ring,
      show e + 3 * k + 3 = (e + 2 * k + 2) + (k + 1) from by ring]
  apply stepStar_trans (opening_core (k + 1) (b := 0) (c := 0) (e := e + 2 * k + 2))
  rw [show 0 + 5 * (k + 1) = 5 * k + 5 from by omega,
      show e + 2 * k + 2 = (e + 2 * k + 1) + 1 from by ring]
  step fm; step fm
  rw [show (5 * k + 5 : ℕ) = 0 + (5 * k + 5) from (Nat.zero_add _).symm,
      show (2 : ℕ) = 1 + 1 from rfl]
  apply stepStar_trans (drain_core (5 * k + 5) (b := 0) (d := 1) (e := e + 2 * k + 2))
  ring_nf; finish

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨0, 0, 0, 1, 1⟩) (by execute fm 1)
  apply progress_nonhalt_simple (fm := fm) (A := ℕ × ℕ)
    (fun ⟨d, e⟩ ↦ ⟨0, 0, 0, d + 1, e + d + 1⟩) ⟨0, 0⟩
  intro ⟨d, e⟩
  obtain ⟨j, rfl | rfl | rfl⟩ : ∃ j, d = 3 * j ∨ d = 3 * j + 1 ∨ d = 3 * j + 2 := ⟨d / 3, by omega⟩
  · refine ⟨⟨5 * j + 2, e + 7 * j + 1⟩, ?_⟩
    show ⟨0, 0, 0, 3 * j + 1, e + (3 * j + 1)⟩ [fm]⊢⁺ ⟨0, 0, 0, (5 * j + 2) + 1, (e + 7 * j + 1) + (5 * j + 2) + 1⟩
    rw [show e + (3 * j + 1) = e + 3 * j + 1 from by ring,
        show (5 * j + 2) + 1 = 5 * j + 3 from by ring,
        show (e + 7 * j + 1) + (5 * j + 2) + 1 = e + 12 * j + 4 from by ring]
    exact trans_case1
  · refine ⟨⟨5 * j + 3, e + 7 * j + 4⟩, ?_⟩
    show ⟨0, 0, 0, (3 * j + 1) + 1, e + ((3 * j + 1) + 1)⟩ [fm]⊢⁺ ⟨0, 0, 0, (5 * j + 3) + 1, (e + 7 * j + 4) + (5 * j + 3) + 1⟩
    rw [show (3 * j + 1) + 1 = 3 * j + 2 from by ring,
        show e + ((3 * j + 1) + 1) = e + 3 * j + 2 from by ring,
        show (5 * j + 3) + 1 = 5 * j + 4 from by ring,
        show (e + 7 * j + 4) + (5 * j + 3) + 1 = e + 12 * j + 8 from by ring]
    exact trans_case2
  · refine ⟨⟨5 * j + 6, e + 7 * j + 5⟩, ?_⟩
    show ⟨0, 0, 0, (3 * j + 2) + 1, e + ((3 * j + 2) + 1)⟩ [fm]⊢⁺ ⟨0, 0, 0, (5 * j + 6) + 1, (e + 7 * j + 5) + (5 * j + 6) + 1⟩
    rw [show (3 * j + 2) + 1 = 3 * (j + 1) from by ring,
        show e + (3 * (j + 1)) = e + 3 * (j + 1) from by ring,
        show (5 * j + 6) + 1 = 5 * j + 7 from by ring,
        show (e + 7 * j + 5) + (5 * j + 6) + 1 = e + 12 * j + 12 from by ring]
    exact trans_case3
