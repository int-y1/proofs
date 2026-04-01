import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #1292: [63/10, 11/2, 4/33, 5/7, 42/11]

Vector representation:
```
-1  2 -1  1  0
-1  0  0  0  1
 2 -1  0  0 -1
 0  0  1 -1  0
 1  1  0  1 -1
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_1292

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a+1, b, c+1, d, e⟩ => some ⟨a, b+2, c, d+1, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b, c, d, e+1⟩
  | ⟨a, b+1, c, d, e+1⟩ => some ⟨a+2, b, c, d, e⟩
  | ⟨a, b, c, d+1, e⟩ => some ⟨a, b, c+1, d, e⟩
  | ⟨a, b, c, d, e+1⟩ => some ⟨a+1, b+1, c, d+1, e⟩
  | _ => none

-- R4 chain: move d to c
theorem d_to_c : ∀ k, ∀ c d, ⟨0, 0, c, d + k, e⟩ [fm]⊢* ⟨0, 0, c + k, d, e⟩ := by
  intro k; induction' k with k ih <;> intro c d
  · exists 0
  · rw [show d + (k + 1) = (d + k) + 1 from by ring]
    step fm
    apply stepStar_trans (ih (c + 1) d)
    ring_nf; finish

-- R3 + R1 + R1: processes 2 values of c
theorem inner_pair : ⟨0, b + 1, c + 2, d, e + 1⟩ [fm]⊢* ⟨0, b + 4, c, d + 2, e⟩ := by
  step fm; step fm; step fm; finish

-- R3 + R1 + R2: processes the last odd c
theorem inner_last : ⟨0, b + 1, 1, d, e + 1⟩ [fm]⊢* ⟨0, b + 2, 0, d + 1, e + 1⟩ := by
  step fm; step fm; step fm; finish

-- Inner spiral for even c = 2k
theorem inner_spiral_even : ∀ k, ∀ b d e, ⟨0, b + 1, 2 * k, d, e + k⟩ [fm]⊢* ⟨0, b + 3 * k + 1, 0, d + 2 * k, e⟩ := by
  intro k; induction' k with k ih <;> intro b d e
  · exists 0
  · rw [show 2 * (k + 1) = (2 * k) + 2 from by ring,
        show e + (k + 1) = e + k + 1 from by ring]
    apply stepStar_trans (inner_pair (b := b) (c := 2 * k) (d := d) (e := e + k))
    apply stepStar_trans (ih (b + 3) (d + 2) e)
    ring_nf; finish

-- Inner spiral for odd c = 2k+1
theorem inner_spiral_odd : ∀ k, ∀ b d e, ⟨0, b + 1, 2 * k + 1, d, e + k + 1⟩ [fm]⊢* ⟨0, b + 3 * k + 2, 0, d + 2 * k + 1, e + 1⟩ := by
  intro k; induction' k with k ih <;> intro b d e
  · exact inner_last
  · rw [show 2 * (k + 1) + 1 = (2 * k + 1) + 2 from by ring,
        show e + (k + 1) + 1 = e + k + 1 + 1 from by ring]
    apply stepStar_trans (inner_pair (b := b) (c := 2 * k + 1) (d := d) (e := e + k + 1))
    apply stepStar_trans (ih (b + 3) (d + 2) e)
    ring_nf; finish

-- Drain b using R3 + R2 + R2
theorem drain : ∀ k, ∀ d e, ⟨0, k, 0, d, e + 1⟩ [fm]⊢* ⟨0, 0, 0, d, e + k + 1⟩ := by
  intro k; induction' k with k ih <;> intro d e
  · exists 0
  · step fm; step fm; step fm
    rw [show e + 1 + 1 = (e + 1) + 1 from by ring]
    apply stepStar_trans (ih d (e + 1))
    ring_nf; finish

-- R4 + R5 + R1 opening
theorem opening : ⟨0, 0, 0, n + 1, E + 1⟩ [fm]⊢⁺ ⟨0, 3, n, 2, E⟩ := by
  rw [show n + 1 = 0 + (n + 1) from by ring]
  apply stepStar_stepPlus_stepPlus (d_to_c (n + 1) 0 0 (e := E + 1))
  rw [show 0 + (n + 1) = n + 1 from by ring]
  step fm; step fm; finish

-- Main transition for even d: (0,0,0,2k+1,e+k+2) ⊢⁺ (0,0,0,2k+2,e+3k+4)
-- Here e is shifted by 1 from before to ensure drain works
theorem main_even (k : ℕ) : ⟨0, 0, 0, 2 * k + 1, e + k + 2⟩ [fm]⊢⁺ ⟨0, 0, 0, 2 * k + 2, e + 3 * k + 4⟩ := by
  rw [show e + k + 2 = (e + k + 1) + 1 from by ring]
  apply stepPlus_stepStar_stepPlus (opening (n := 2 * k) (E := e + k + 1))
  rw [show e + k + 1 = (e + 1) + k from by ring,
      show (3 : ℕ) = 2 + 1 from rfl]
  apply stepStar_trans (inner_spiral_even k 2 2 (e + 1))
  rw [show 2 + 3 * k + 1 = 3 * k + 3 from by ring,
      show 2 + 2 * k = 2 * k + 2 from by ring]
  exact drain (3 * k + 3) (2 * k + 2) e

-- Main transition for odd d: (0,0,0,2k+2,e+k+2) ⊢⁺ (0,0,0,2k+3,e+3k+5)
theorem main_odd (k : ℕ) : ⟨0, 0, 0, 2 * k + 2, e + k + 2⟩ [fm]⊢⁺ ⟨0, 0, 0, 2 * k + 3, e + 3 * k + 5⟩ := by
  rw [show e + k + 2 = (e + k + 1) + 1 from by ring]
  apply stepPlus_stepStar_stepPlus (opening (n := 2 * k + 1) (E := e + k + 1))
  rw [show e + k + 1 = e + k + 1 from rfl,
      show (3 : ℕ) = 2 + 1 from rfl]
  apply stepStar_trans (inner_spiral_odd k 2 2 e)
  rw [show 2 + 3 * k + 2 = 3 * k + 4 from by ring,
      show 2 + 2 * k + 1 = 2 * k + 3 from by ring]
  exact drain (3 * k + 4) (2 * k + 3) e

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨0, 0, 0, 1, 2⟩) (by execute fm 6)
  apply progress_nonhalt (fm := fm)
    (P := fun q ↦ ∃ d e, q = ⟨0, 0, 0, d + 1, e⟩ ∧ e ≥ d + 2)
  · intro c ⟨d, e, hq, he⟩; subst hq
    rcases Nat.even_or_odd d with ⟨k, hk⟩ | ⟨k, hk⟩
    · -- d even: d = 2k
      rw [show k + k = 2 * k from by ring] at hk; subst hk
      obtain ⟨e', rfl⟩ : ∃ e', e = e' + k + 2 := ⟨e - k - 2, by omega⟩
      refine ⟨⟨0, 0, 0, 2 * k + 2, e' + 3 * k + 4⟩,
        ⟨2 * k + 1, e' + 3 * k + 4, rfl, by omega⟩,
        main_even k⟩
    · -- d odd: d = 2k + 1
      subst hk
      obtain ⟨e', rfl⟩ : ∃ e', e = e' + k + 2 := ⟨e - k - 2, by omega⟩
      refine ⟨⟨0, 0, 0, 2 * k + 3, e' + 3 * k + 5⟩,
        ⟨2 * k + 2, e' + 3 * k + 5, rfl, by omega⟩,
        main_odd k⟩
  · exact ⟨0, 2, rfl, by omega⟩
