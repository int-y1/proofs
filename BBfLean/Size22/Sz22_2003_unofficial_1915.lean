import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #1915: [9/385, 7/15, 242/3, 5/11, 33/2]

Vector representation:
```
 0  2 -1 -1 -1
 0 -1 -1  1  0
 1 -1  0  0  2
 0  0  1  0 -1
-1  1  0  0  1
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_1915

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a, b, c+1, d+1, e+1⟩ => some ⟨a, b+2, c, d, e⟩
  | ⟨a, b+1, c+1, d, e⟩ => some ⟨a, b, c, d+1, e⟩
  | ⟨a, b+1, c, d, e⟩ => some ⟨a+1, b, c, d, e+2⟩
  | ⟨a, b, c, d, e+1⟩ => some ⟨a, b, c+1, d, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b+1, c, d, e+1⟩
  | _ => none

theorem e_to_c : ∀ k, ⟨a, 0, c, 0, k⟩ [fm]⊢* ⟨a, 0, c + k, 0, 0⟩ := by
  intro k; induction' k with k ih generalizing c
  · exists 0
  · step fm
    apply stepStar_trans (ih (c := c + 1))
    ring_nf; finish

theorem inner_loop : ∀ D, ⟨a, 0, 0, D, e + 2⟩ [fm]⊢* ⟨a + 2 * D, 0, 0, 0, e + 2 + 2 * D⟩ := by
  intro D; induction' D with D ih generalizing a e
  · exists 0
  · step fm; step fm; step fm; step fm
    rw [show e + 2 + 2 = (e + 2) + 2 from by ring]
    apply stepStar_trans (ih (a := a + 2) (e := e + 2))
    ring_nf; finish

theorem drain_round : ∀ d, ⟨a + 1, 0, c + 4, d, 0⟩ [fm]⊢* ⟨a, 0, c, d + 2, 0⟩ := by
  intro d; rcases d with _ | d
  · execute fm 5
  · execute fm 5

theorem drain3 : ∀ d, ⟨a + 1, 0, 3, d, 0⟩ [fm]⊢* ⟨a + 1, 0, 0, d + 1, 2⟩ := by
  intro d; rcases d with _ | d
  · execute fm 5
  · execute fm 5

theorem drain_mod3 : ∀ m, ∀ d, ⟨a + m + 1, 0, 4 * m + 3, d, 0⟩ [fm]⊢*
    ⟨a + 1, 0, 0, d + 2 * m + 1, 2⟩ := by
  intro m; induction' m with m ih generalizing a
  · exact drain3
  · intro d
    show ⟨a + (m + 1) + 1, 0, 4 * (m + 1) + 3, d, 0⟩ [fm]⊢*
      ⟨a + 1, 0, 0, d + 2 * (m + 1) + 1, 2⟩
    rw [show a + (m + 1) + 1 = a + m + 1 + 1 from by ring,
        show 4 * (m + 1) + 3 = (4 * m + 3) + 4 from by ring]
    apply stepStar_trans (drain_round d (a := a + m + 1) (c := 4 * m + 3))
    apply stepStar_trans (ih (a := a) (d := d + 2))
    ring_nf; finish

theorem drain4 : ∀ d, ⟨a + 1, 0, 4, d, 0⟩ [fm]⊢* ⟨a, 0, 0, d + 2, 0⟩ := by
  intro d; rcases d with _ | d
  · execute fm 5
  · execute fm 5

theorem drain_mod0 : ∀ m, ∀ d, ⟨a + m + 1, 0, 4 * (m + 1), d, 0⟩ [fm]⊢*
    ⟨a, 0, 0, d + 2 * (m + 1), 0⟩ := by
  intro m; induction' m with m ih generalizing a
  · intro d; rw [show a + 0 + 1 = a + 1 from by ring]; exact drain4 d
  · intro d
    show ⟨a + (m + 1) + 1, 0, 4 * (m + 1 + 1), d, 0⟩ [fm]⊢*
      ⟨a, 0, 0, d + 2 * (m + 1 + 1), 0⟩
    rw [show a + (m + 1) + 1 = a + m + 1 + 1 from by ring,
        show 4 * (m + 1 + 1) = (4 * (m + 1)) + 4 from by ring]
    apply stepStar_trans (drain_round d (a := a + m + 1) (c := 4 * (m + 1)))
    apply stepStar_trans (ih (a := a) (d := d + 2))
    ring_nf; finish

theorem bootstrap : ⟨a + 1, 0, 0, d + 1, 0⟩ [fm]⊢* ⟨a + 1, 0, 0, d + 1, 3⟩ := by
  execute fm 2

theorem main_trans : ∀ k, ⟨3 * k ^ 2 + 2 * k + 1, 0, 0, 0, 4 * k + 3⟩ [fm]⊢⁺
    ⟨3 * (k + 1) ^ 2 + 2 * (k + 1) + 1, 0, 0, 0, 4 * (k + 1) + 3⟩ := by
  intro k
  apply step_stepStar_stepPlus
  · show fm ⟨3 * k ^ 2 + 2 * k + 1, 0, 0, 0, (4 * k + 2) + 1⟩ = _; rfl
  apply stepStar_trans (e_to_c (4 * k + 2) (a := 3 * k ^ 2 + 2 * k + 1) (c := 1))
  rw [show 1 + (4 * k + 2) = 4 * k + 3 from by ring,
      show 3 * k ^ 2 + 2 * k + 1 = (3 * k ^ 2 + k) + k + 1 from by ring]
  apply stepStar_trans (drain_mod3 k 0 (a := 3 * k ^ 2 + k))
  rw [show 0 + 2 * k + 1 = 2 * k + 1 from by ring,
      show (2 : ℕ) = 0 + 2 from by ring]
  apply stepStar_trans (inner_loop (2 * k + 1) (a := 3 * k ^ 2 + k + 1) (e := 0))
  rw [show 3 * k ^ 2 + k + 1 + 2 * (2 * k + 1) = 3 * k ^ 2 + 5 * k + 3 from by ring,
      show 0 + 2 + 2 * (2 * k + 1) = 4 * k + 4 from by ring]
  apply stepStar_trans (e_to_c (4 * k + 4) (a := 3 * k ^ 2 + 5 * k + 3) (c := 0))
  rw [show 0 + (4 * k + 4) = 4 * (k + 1) from by ring,
      show 3 * k ^ 2 + 5 * k + 3 = (3 * k ^ 2 + 4 * k + 2) + k + 1 from by ring]
  apply stepStar_trans (drain_mod0 k 0 (a := 3 * k ^ 2 + 4 * k + 2))
  rw [show 0 + 2 * (k + 1) = 2 * k + 2 from by ring,
      show 3 * k ^ 2 + 4 * k + 2 = (3 * k ^ 2 + 4 * k + 1) + 1 from by ring,
      show 2 * k + 2 = (2 * k + 1) + 1 from by ring]
  apply stepStar_trans bootstrap
  rw [show (3 : ℕ) = 1 + 2 from by ring,
      show (3 * k ^ 2 + 4 * k + 1) + 1 = 3 * k ^ 2 + 4 * k + 2 from by ring]
  apply stepStar_trans (inner_loop (2 * k + 2) (a := 3 * k ^ 2 + 4 * k + 2) (e := 1))
  rw [show 3 * k ^ 2 + 4 * k + 2 + 2 * (2 * k + 2) = 3 * (k + 1) ^ 2 + 2 * (k + 1) + 1 from by ring,
      show 1 + 2 + 2 * (2 * k + 2) = 4 * (k + 1) + 3 from by ring]
  finish

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨1, 0, 0, 0, 3⟩) (by execute fm 2)
  rw [show (1 : ℕ) = 3 * 0 ^ 2 + 2 * 0 + 1 from by ring,
      show (3 : ℕ) = 4 * 0 + 3 from by ring]
  apply progress_nonhalt_simple (fm := fm) (A := ℕ)
    (fun k ↦ ⟨3 * k ^ 2 + 2 * k + 1, 0, 0, 0, 4 * k + 3⟩) 0
  intro k; exact ⟨k + 1, main_trans k⟩
