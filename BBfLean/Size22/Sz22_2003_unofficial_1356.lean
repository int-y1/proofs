import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #1356: [63/10, 4/33, 121/2, 5/7, 10/11]

Vector representation:
```
-1  2 -1  1  0
 2 -1  0  0 -1
-1  0  0  0  2
 0  0  1 -1  0
 1  0  1  0 -1
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_1356

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a+1, b, c+1, d, e⟩ => some ⟨a, b+2, c, d+1, e⟩
  | ⟨a, b+1, c, d, e+1⟩ => some ⟨a+2, b, c, d, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b, c, d, e+2⟩
  | ⟨a, b, c, d+1, e⟩ => some ⟨a, b, c+1, d, e⟩
  | ⟨a, b, c, d, e+1⟩ => some ⟨a+1, b, c+1, d, e⟩
  | _ => none

theorem r2_chain : ∀ k, ⟨a, b + k, 0, d, e + k⟩ [fm]⊢* ⟨a + 2 * k, b, 0, d, e⟩ := by
  intro k; induction' k with k ih generalizing a b d e
  · exists 0
  · rw [show b + (k + 1) = (b + k) + 1 from by ring,
        show e + (k + 1) = (e + k) + 1 from by ring]
    step fm
    apply stepStar_trans (ih (a := a + 2))
    ring_nf; finish

theorem r3_chain : ∀ k, ⟨a + k, 0, 0, d, e⟩ [fm]⊢* ⟨a, 0, 0, d, e + 2 * k⟩ := by
  intro k; induction' k with k ih generalizing a d e
  · exists 0
  · rw [show a + (k + 1) = (a + k) + 1 from by ring]
    step fm
    apply stepStar_trans (ih (e := e + 2))
    ring_nf; finish

theorem r4_chain : ∀ k, ⟨0, 0, c, d + k, e⟩ [fm]⊢* ⟨0, 0, c + k, d, e⟩ := by
  intro k; induction' k with k ih generalizing c d e
  · exists 0
  · rw [show d + (k + 1) = (d + k) + 1 from by ring]
    step fm
    apply stepStar_trans (ih (c := c + 1))
    ring_nf; finish

theorem interleave : ∀ k, ∀ c d e,
    ⟨0, b + 1, c + 2 * k, d, e + k⟩ [fm]⊢* ⟨0, b + 1 + 3 * k, c, d + 2 * k, e⟩ := by
  intro k; induction' k with k ih generalizing b
  · intro c d e; exists 0
  · intro c d e
    rw [show c + 2 * (k + 1) = (c + 2 * k) + 2 from by ring,
        show e + (k + 1) = (e + k) + 1 from by ring]
    step fm; step fm; step fm
    show ⟨0, b + 4, c + 2 * k, d + 2, e + k⟩ [fm]⊢*
      ⟨0, b + 1 + 3 * (k + 1), c, d + 2 * (k + 1), e⟩
    rw [show b + 4 = (b + 3) + 1 from by ring]
    apply stepStar_trans (ih (b := b + 3) c (d + 2) e)
    ring_nf; finish

theorem even_trans (k : ℕ) :
    ⟨0, 0, 2 * k + 2, 0, 8 * k ^ 2 + 22 * k + 16⟩ [fm]⊢⁺
    ⟨0, 0, 2 * k + 3, 0, 8 * k ^ 2 + 30 * k + 29⟩ := by
  -- R5 step for ⊢⁺
  rw [show 8 * k ^ 2 + 22 * k + 16 = (8 * k ^ 2 + 22 * k + 15) + 1 from by ring]
  step fm
  -- After R5: (1, 0, 2k+3, 0, 8k²+22k+15)
  -- 4 more opening steps: R1, R2, R1, R1
  step fm; step fm; step fm; step fm
  -- State: (0, 5, 2k, 3, 8k²+22k+14)
  show ⟨0, 5, 2 * k, 3, 8 * k ^ 2 + 22 * k + 14⟩ [fm]⊢*
    ⟨0, 0, 2 * k + 3, 0, 8 * k ^ 2 + 30 * k + 29⟩
  rw [show (5 : ℕ) = 4 + 1 from by ring,
      show (2 * k : ℕ) = 0 + 2 * k from by ring,
      show 8 * k ^ 2 + 22 * k + 14 = (8 * k ^ 2 + 21 * k + 14) + k from by ring]
  apply stepStar_trans (interleave k (b := 4) (c := 0) (d := 3)
    (e := 8 * k ^ 2 + 21 * k + 14))
  rw [show 4 + 1 + 3 * k = 0 + (3 * k + 5) from by ring,
      show (3 + 2 * k : ℕ) = 2 * k + 3 from by ring,
      show 8 * k ^ 2 + 21 * k + 14 = (8 * k ^ 2 + 18 * k + 9) + (3 * k + 5) from by ring]
  apply stepStar_trans (r2_chain (3 * k + 5) (a := 0) (b := 0) (d := 2 * k + 3)
    (e := 8 * k ^ 2 + 18 * k + 9))
  rw [show 0 + 2 * (3 * k + 5) = 0 + (6 * k + 10) from by ring]
  apply stepStar_trans (r3_chain (6 * k + 10) (a := 0) (d := 2 * k + 3)
    (e := 8 * k ^ 2 + 18 * k + 9))
  rw [show 8 * k ^ 2 + 18 * k + 9 + 2 * (6 * k + 10) = 8 * k ^ 2 + 30 * k + 29 from by ring,
      show (2 * k + 3 : ℕ) = 0 + (2 * k + 3) from by ring]
  apply stepStar_trans (r4_chain (2 * k + 3) (c := 0) (d := 0)
    (e := 8 * k ^ 2 + 30 * k + 29))
  ring_nf; finish

theorem odd_trans (k : ℕ) :
    ⟨0, 0, 2 * k + 3, 0, 8 * k ^ 2 + 30 * k + 29⟩ [fm]⊢⁺
    ⟨0, 0, 2 * k + 4, 0, 8 * k ^ 2 + 38 * k + 46⟩ := by
  -- R5 step for ⊢⁺
  rw [show 8 * k ^ 2 + 30 * k + 29 = (8 * k ^ 2 + 30 * k + 28) + 1 from by ring]
  step fm
  -- After R5: (1, 0, 2k+4, 0, 8k²+30k+28)
  -- 4 more opening steps
  step fm; step fm; step fm; step fm
  -- State: (0, 5, 2k+1, 3, 8k²+30k+27)
  show ⟨0, 5, 2 * k + 1, 3, 8 * k ^ 2 + 30 * k + 27⟩ [fm]⊢*
    ⟨0, 0, 2 * k + 4, 0, 8 * k ^ 2 + 38 * k + 46⟩
  rw [show (5 : ℕ) = 4 + 1 from by ring,
      show 2 * k + 1 = 1 + 2 * k from by ring,
      show 8 * k ^ 2 + 30 * k + 27 = (8 * k ^ 2 + 29 * k + 27) + k from by ring]
  apply stepStar_trans (interleave k (b := 4) (c := 1) (d := 3)
    (e := 8 * k ^ 2 + 29 * k + 27))
  -- State: (0, 3k+5, 1, 2k+3, 8k²+29k+27)
  -- R2 then R1
  rw [show 4 + 1 + 3 * k = (3 * k + 4) + 1 from by ring,
      show 3 + 2 * k = 2 * k + 3 from by ring,
      show 8 * k ^ 2 + 29 * k + 27 = (8 * k ^ 2 + 29 * k + 26) + 1 from by ring]
  step fm; step fm
  -- State: (1, 3k+6, 0, 2k+4, 8k²+29k+26)
  show ⟨1, 3 * k + 6, 0, 2 * k + 4, 8 * k ^ 2 + 29 * k + 26⟩ [fm]⊢*
    ⟨0, 0, 2 * k + 4, 0, 8 * k ^ 2 + 38 * k + 46⟩
  rw [show 3 * k + 6 = 0 + (3 * k + 6) from by ring,
      show 8 * k ^ 2 + 29 * k + 26 = (8 * k ^ 2 + 26 * k + 20) + (3 * k + 6) from by ring]
  apply stepStar_trans (r2_chain (3 * k + 6) (a := 1) (b := 0) (d := 2 * k + 4)
    (e := 8 * k ^ 2 + 26 * k + 20))
  rw [show 1 + 2 * (3 * k + 6) = 0 + (6 * k + 13) from by ring]
  apply stepStar_trans (r3_chain (6 * k + 13) (a := 0) (d := 2 * k + 4)
    (e := 8 * k ^ 2 + 26 * k + 20))
  rw [show 8 * k ^ 2 + 26 * k + 20 + 2 * (6 * k + 13) = 8 * k ^ 2 + 38 * k + 46 from by ring,
      show (2 * k + 4 : ℕ) = 0 + (2 * k + 4) from by ring]
  apply stepStar_trans (r4_chain (2 * k + 4) (c := 0) (d := 0)
    (e := 8 * k ^ 2 + 38 * k + 46))
  ring_nf; finish

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨0, 0, 2, 0, 16⟩) (by execute fm 26)
  -- Need to normalize: 2 * (0 + 2) ^ 2 + 3 * (0 + 2) + 2 = 16
  change ¬halts fm ⟨0, 0, 0 + 2, 0, 2 * (0 + 2) ^ 2 + 3 * (0 + 2) + 2⟩
  apply progress_nonhalt_simple (fm := fm) (A := ℕ)
    (fun n ↦ ⟨0, 0, n + 2, 0, 2 * (n + 2) ^ 2 + 3 * (n + 2) + 2⟩) 0
  intro n
  rcases Nat.even_or_odd n with ⟨k, hk⟩ | ⟨k, hk⟩
  · rw [show k + k = 2 * k from by ring] at hk; subst hk
    refine ⟨2 * k + 1, ?_⟩
    show ⟨0, 0, 2 * k + 2, 0, 2 * (2 * k + 2) ^ 2 + 3 * (2 * k + 2) + 2⟩ [fm]⊢⁺
      ⟨0, 0, 2 * k + 3, 0, 2 * (2 * k + 3) ^ 2 + 3 * (2 * k + 3) + 2⟩
    rw [show 2 * (2 * k + 2) ^ 2 + 3 * (2 * k + 2) + 2 = 8 * k ^ 2 + 22 * k + 16 from by ring,
        show 2 * (2 * k + 3) ^ 2 + 3 * (2 * k + 3) + 2 = 8 * k ^ 2 + 30 * k + 29 from by ring]
    exact even_trans k
  · subst hk
    refine ⟨2 * k + 2, ?_⟩
    show ⟨0, 0, 2 * k + 3, 0, 2 * (2 * k + 3) ^ 2 + 3 * (2 * k + 3) + 2⟩ [fm]⊢⁺
      ⟨0, 0, 2 * k + 4, 0, 2 * (2 * k + 4) ^ 2 + 3 * (2 * k + 4) + 2⟩
    rw [show 2 * (2 * k + 3) ^ 2 + 3 * (2 * k + 3) + 2 = 8 * k ^ 2 + 30 * k + 29 from by ring,
        show 2 * (2 * k + 4) ^ 2 + 3 * (2 * k + 4) + 2 = 8 * k ^ 2 + 38 * k + 46 from by ring]
    exact odd_trans k
