import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #1890: [9/35, 5/33, 98/3, 11/7, 45/2]

Vector representation:
```
 0  2 -1 -1  0
 0 -1  1  0 -1
 1 -1  0  2  0
 0  0  0 -1  1
-1  2  1  0  0
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_1890

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a, b, c+1, d+1, e⟩ => some ⟨a, b+2, c, d, e⟩
  | ⟨a, b+1, c, d, e+1⟩ => some ⟨a, b, c+1, d, e⟩
  | ⟨a, b+1, c, d, e⟩ => some ⟨a+1, b, c, d+2, e⟩
  | ⟨a, b, c, d+1, e⟩ => some ⟨a, b, c, d, e+1⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b+2, c+1, d, e⟩
  | _ => none

theorem d_to_e : ∀ k, ⟨a, 0, 0, d + k, e⟩ [fm]⊢* ⟨a, 0, 0, d, k + e⟩ := by
  intro k; induction' k with k ih generalizing d e
  · simp; exists 0
  · rw [show d + (k + 1) = d + 1 + k from by ring]
    apply stepStar_trans (ih (d := d + 1) (e := e))
    step fm; ring_nf; finish

theorem r5r2r2_chain : ∀ k, ⟨a + k, 0, c, 0, 2 * k⟩ [fm]⊢* ⟨a, 0, c + 3 * k, 0, 0⟩ := by
  intro k; induction' k with k ih generalizing a c
  · exists 0
  · rw [show a + (k + 1) = (a + k) + 1 from by ring,
        show 2 * (k + 1) = 2 * k + 1 + 1 from by ring]
    step fm; step fm; step fm
    apply stepStar_trans (ih (a := a) (c := c + 3))
    ring_nf; finish

theorem r5r2r2_odd : ∀ k, ⟨a + k + 1, 0, c, 0, 2 * k + 1⟩ [fm]⊢* ⟨a + 1, 0, c + 3 * k + 2, 2, 0⟩ := by
  intro k; induction' k with k ih generalizing a c
  · step fm; step fm; step fm; ring_nf; finish
  · rw [show a + (k + 1) + 1 = (a + k + 1) + 1 from by ring,
        show 2 * (k + 1) + 1 = 2 * k + 1 + 1 + 1 from by ring]
    step fm; step fm; step fm
    apply stepStar_trans (ih (a := a) (c := c + 3))
    ring_nf; finish

theorem r1r1r3_chain : ∀ k, ⟨a, b, c + 2 * k, 2, 0⟩ [fm]⊢* ⟨a + k, b + 3 * k, c, 2, 0⟩ := by
  intro k; induction' k with k ih generalizing a b c
  · exists 0
  · rw [show c + 2 * (k + 1) = (c + 2) + 2 * k from by ring]
    apply stepStar_trans (ih (a := a) (b := b) (c := c + 2))
    step fm; step fm; step fm
    ring_nf; finish

theorem r3_drain : ∀ k, ⟨a, b + k, 0, d, 0⟩ [fm]⊢* ⟨a + k, b, 0, d + 2 * k, 0⟩ := by
  intro k; induction' k with k ih generalizing a b d
  · exists 0
  · rw [show b + (k + 1) = (b + k) + 1 from by ring]
    step fm
    apply stepStar_trans (ih (a := a + 1) (b := b) (d := d + 2))
    ring_nf; finish

theorem phase3_odd :
    ⟨a, b, 2 * k + 1, 2, 0⟩ [fm]⊢* ⟨a + 4 * k + 2, b, 0, 6 * k + 5, 0⟩ := by
  rw [show 2 * k + 1 = 1 + 2 * k from by ring]
  apply stepStar_trans (r1r1r3_chain k (a := a) (b := b) (c := 1))
  step fm
  rw [show b + 3 * k + 2 = b + (3 * k + 2) from by ring]
  apply stepStar_trans (r3_drain (3 * k + 2) (a := a + k) (b := b) (d := 1))
  ring_nf; finish

theorem phase3_even :
    ⟨a, b, 2 * k, 2, 0⟩ [fm]⊢* ⟨a + 4 * k, b, 0, 6 * k + 2, 0⟩ := by
  rw [show 2 * k = 0 + 2 * k from by ring]
  apply stepStar_trans (r1r1r3_chain k (a := a) (b := b) (c := 0))
  rw [show b + 3 * k = b + (3 * k) from by ring]
  apply stepStar_trans (r3_drain (3 * k) (a := a + k) (b := b) (d := 2))
  ring_nf; finish

theorem phase3_any (C : ℕ) :
    ⟨a, b, C, 2, 0⟩ [fm]⊢* ⟨a + 2 * C, b, 0, 3 * C + 2, 0⟩ := by
  rcases Nat.even_or_odd C with ⟨k, hk⟩ | ⟨k, hk⟩
  · subst hk
    rw [show k + k = 2 * k from by ring]
    apply stepStar_trans (phase3_even (a := a) (b := b) (k := k))
    ring_nf; finish
  · subst hk
    apply stepStar_trans (phase3_odd (a := a) (b := b) (k := k))
    ring_nf; finish

theorem main_trans_odd :
    ⟨a + k + 1, 0, 0, 2 * k + 1, 0⟩ [fm]⊢⁺ ⟨a + 6 * k + 5, 0, 0, 9 * k + 8, 0⟩ := by
  rw [show 2 * k + 1 = (2 * k) + 1 from by ring]
  step fm
  rw [show 2 * k = 0 + 2 * k from by ring]
  apply stepStar_trans (d_to_e (2 * k) (a := a + k + 1) (d := 0) (e := 1))
  rw [show 2 * k + 1 = 2 * k + 1 from rfl]
  apply stepStar_trans (r5r2r2_odd k (a := a) (c := 0))
  rw [show 0 + 3 * k + 2 = 3 * k + 2 from by ring]
  apply stepStar_trans (phase3_any (3 * k + 2) (a := a + 1) (b := 0))
  ring_nf; finish

theorem main_trans_even :
    ⟨a + k + 2, 0, 0, 2 * k + 2, 0⟩ [fm]⊢⁺ ⟨a + 6 * k + 10, 0, 0, 9 * k + 16, 0⟩ := by
  rw [show 2 * k + 2 = (2 * k + 1) + 1 from by ring]
  step fm
  rw [show 2 * k + 1 = 0 + (2 * k + 1) from by ring]
  apply stepStar_trans (d_to_e (2 * k + 1) (a := a + k + 2) (d := 0) (e := 1))
  rw [show 2 * k + 1 + 1 = 2 * k + 2 from by ring,
      show a + k + 2 = (a + k + 1) + 1 from by ring]
  step fm; step fm; step fm
  rw [show a + k + 1 = (a + 1) + k from by ring]
  apply stepStar_trans (r5r2r2_chain k (a := a + 1) (c := 3))
  rw [show 3 + 3 * k = 3 * k + 3 from by ring]
  step fm; step fm
  rw [show 3 * k + 3 + 1 = 3 * k + 4 from by ring,
      show a + 1 = a + 1 from rfl]
  apply stepStar_trans (phase3_any (3 * k + 4) (a := a + 1) (b := 1))
  step fm
  ring_nf; finish

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨23, 0, 0, 35, 0⟩) (by execute fm 58)
  apply progress_nonhalt (fm := fm)
    (P := fun q ↦ ∃ a d, q = ⟨a, 0, 0, d, 0⟩ ∧ d ≥ 1 ∧ 2 * a ≥ d + 2)
  · intro c ⟨a, d, hq, hd, ha⟩; subst hq
    rcases Nat.even_or_odd d with ⟨j, hj⟩ | ⟨j, hj⟩
    · rw [show j + j = 2 * j from by ring] at hj; subst hj
      obtain ⟨j', rfl⟩ : ∃ j', j = j' + 1 := ⟨j - 1, by omega⟩
      obtain ⟨m, rfl⟩ : ∃ m, a = m + j' + 2 := ⟨a - j' - 2, by omega⟩
      refine ⟨⟨m + 6 * j' + 10, 0, 0, 9 * j' + 16, 0⟩,
        ⟨m + 6 * j' + 10, 9 * j' + 16, rfl, by omega, by omega⟩,
        ?_⟩
      show ⟨m + j' + 2, 0, 0, 2 * j' + 2, 0⟩ [fm]⊢⁺ _
      exact main_trans_even
    · subst hj
      obtain ⟨m, rfl⟩ : ∃ m, a = m + j + 1 := ⟨a - j - 1, by omega⟩
      exact ⟨⟨m + 6 * j + 5, 0, 0, 9 * j + 8, 0⟩,
        ⟨m + 6 * j + 5, 9 * j + 8, rfl, by omega, by omega⟩,
        main_trans_odd⟩
  · exact ⟨23, 35, rfl, by omega, by omega⟩
