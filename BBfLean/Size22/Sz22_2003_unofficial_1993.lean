import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #1993: [99/35, 5/6, 4/5, 7/11, 175/2]

Vector representation:
```
 0  2 -1 -1  1
-1 -1  1  0  0
 2  0 -1  0  0
 0  0  0  1 -1
-1  0  2  1  0
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_1993

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a, b, c+1, d+1, e⟩ => some ⟨a, b+2, c, d, e+1⟩
  | ⟨a+1, b+1, c, d, e⟩ => some ⟨a, b, c+1, d, e⟩
  | ⟨a, b, c+1, d, e⟩ => some ⟨a+2, b, c, d, e⟩
  | ⟨a, b, c, d, e+1⟩ => some ⟨a, b, c, d+1, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b, c+2, d+1, e⟩
  | _ => none

theorem e_to_d : ∀ k, ⟨a, 0, 0, d, k⟩ [fm]⊢* ⟨a, 0, 0, d + k, 0⟩ := by
  intro k; induction' k with k ih generalizing d
  · exists 0
  · rw [show d + (k + 1) = (d + 1) + k from by ring]
    step fm
    exact ih (d := d + 1)

theorem r3_chain : ∀ k, ⟨a, 0, k, 0, e⟩ [fm]⊢* ⟨a + 2 * k, 0, 0, 0, e⟩ := by
  intro k; induction' k with k ih generalizing a
  · exists 0
  · step fm
    apply stepStar_trans (ih (a := a + 2))
    ring_nf; finish

theorem r2_drain : ∀ k, ∀ c, ⟨a + k, k, c, 0, e⟩ [fm]⊢* ⟨a, 0, c + k, 0, e⟩ := by
  intro k; induction' k with k ih generalizing a
  · intro c; exists 0
  · intro c
    rw [show c + (k + 1) = (c + 1) + k from by ring,
        show a + (k + 1) = a + k + 1 from by ring]
    show ⟨(a + k) + 1, k + 1, c, 0, e⟩ [fm]⊢* ⟨a, 0, (c + 1) + k, 0, e⟩
    rcases c with _ | c
    · apply stepStar_trans (step_stepStar (by simp [fm] : (fm : FM) ⟨a + k + 1, k + 1, 0, 0, e⟩ = some ⟨a + k, k, 1, 0, e⟩))
      exact ih (a := a) 1
    · apply stepStar_trans (step_stepStar (by simp [fm] : (fm : FM) ⟨a + k + 1, k + 1, c + 1, 0, e⟩ = some ⟨a + k, k, c + 2, 0, e⟩))
      exact ih (a := a) (c + 2)

theorem r2r1_chain : ∀ k, ⟨a + k, b + 1, 0, k, e⟩ [fm]⊢* ⟨a, b + k + 1, 0, 0, e + k⟩ := by
  intro k; induction' k with k ih generalizing a b e
  · exists 0
  · rw [show a + (k + 1) = a + k + 1 from by ring]
    step fm
    step fm
    apply stepStar_trans (ih (a := a) (b := b + 1) (e := e + 1))
    ring_nf; finish

theorem main_trans : ⟨3 * n + 7, 0, 0, 0, n + 2⟩ [fm]⊢⁺ ⟨3 * n + 10, 0, 0, 0, n + 3⟩ := by
  apply stepStar_stepPlus_stepPlus (e_to_d (n + 2) (a := 3 * n + 7) (d := 0))
  rw [show 0 + (n + 2) = n + 2 from by ring]
  apply step_stepStar_stepPlus (by show (fm : FM) ⟨3 * n + 7, 0, 0, n + 2, 0⟩ = some ⟨3 * n + 6, 0, 2, n + 3, 0⟩; simp [fm])
  rw [show n + 3 = (n + 1) + 2 from by ring]
  step fm
  step fm
  rw [show 3 * n + 6 = (2 * n + 5) + (n + 1) from by ring,
      show (4 : ℕ) = 3 + 1 from by ring]
  apply stepStar_trans (r2r1_chain (n + 1) (a := 2 * n + 5) (b := 3) (e := 2))
  rw [show 3 + (n + 1) + 1 = n + 5 from by ring,
      show 2 + (n + 1) = n + 3 from by ring,
      show 2 * n + 5 = n + (n + 5) from by ring]
  apply stepStar_trans (r2_drain (n + 5) 0 (a := n) (e := n + 3))
  rw [show 0 + (n + 5) = n + 5 from by ring]
  apply stepStar_trans (r3_chain (n + 5) (a := n) (e := n + 3))
  ring_nf; finish

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨7, 0, 0, 0, 2⟩) (by execute fm 19)
  apply progress_nonhalt_simple (fm := fm) (A := ℕ)
    (fun n ↦ ⟨3 * n + 7, 0, 0, 0, n + 2⟩) 0
  intro n; exact ⟨n + 1, main_trans⟩
