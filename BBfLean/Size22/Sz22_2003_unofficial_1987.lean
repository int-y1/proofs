import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #1987: [99/35, 4/5, 5/6, 7/11, 275/2]

Vector representation:
```
 0  2 -1 -1  1
 2  0 -1  0  0
-1 -1  1  0  0
 0  0  0  1 -1
-1  0  2  0  1
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_1987

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a, b, c+1, d+1, e⟩ => some ⟨a, b+2, c, d, e+1⟩
  | ⟨a, b, c+1, d, e⟩ => some ⟨a+2, b, c, d, e⟩
  | ⟨a+1, b+1, c, d, e⟩ => some ⟨a, b, c+1, d, e⟩
  | ⟨a, b, c, d, e+1⟩ => some ⟨a, b, c, d+1, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b, c+2, d, e+1⟩
  | _ => none

theorem e_to_d_gen : ∀ k d, ⟨a, 0, 0, d, k⟩ [fm]⊢* ⟨a, 0, 0, d + k, 0⟩ := by
  intro k; induction' k with k ih <;> intro d
  · exists 0
  · rw [show d + (k + 1) = (d + 1) + k from by omega]
    step fm; exact ih (d + 1)

theorem e_to_d : ⟨a, 0, 0, 0, k⟩ [fm]⊢* ⟨a, 0, 0, k, 0⟩ := by
  have h := e_to_d_gen (a := a) k 0
  simp at h; exact h

theorem r3_r2_drain : ∀ k, ⟨a + 1, b + k, 0, 0, e⟩ [fm]⊢* ⟨a + 1 + k, b, 0, 0, e⟩ := by
  intro k; induction' k with k ih generalizing a b
  · exists 0
  · step fm; step fm
    rw [show a + 2 = (a + 1) + 1 from by ring]
    apply stepStar_trans (ih (a := a + 1)); ring_nf; finish

theorem r3_r1_drain : ∀ k, ∀ b e, ⟨a + k + 1, b + 1, 0, k, e⟩ [fm]⊢* ⟨a + 1, b + k + 1, 0, 0, e + k⟩ := by
  intro k; induction' k with k ih <;> intro b e
  · exists 0
  · rw [show a + (k + 1) + 1 = (a + k + 1) + 1 from by ring]
    step fm; step fm
    apply stepStar_trans (ih (b := b + 1) (e := e + 1)); ring_nf; finish

theorem opening : ⟨a + 1, 0, 0, d + 1 + 1, 0⟩ [fm]⊢⁺ ⟨a, 4, 0, d, 3⟩ := by
  step fm; step fm; step fm; finish

theorem n0_trans : ⟨4, 0, 0, 1, 0⟩ [fm]⊢⁺ ⟨7, 0, 0, 2, 0⟩ := by
  execute fm 9

theorem middle_phase : ⟨3 * n + 6, 4, 0, n, 3⟩ [fm]⊢* ⟨3 * n + 10, 0, 0, n + 3, 0⟩ := by
  rw [show 3 * n + 6 = (2 * n + 5) + n + 1 from by ring,
      show (4 : ℕ) = 3 + 1 from by ring]
  apply stepStar_trans (r3_r1_drain (a := 2 * n + 5) n 3 3)
  rw [show 2 * n + 5 + 1 = (2 * n + 5) + 1 from by ring,
      show 3 + n + 1 = 0 + (n + 4) from by ring,
      show (3 + n : ℕ) = n + 3 from by ring]
  apply stepStar_trans (r3_r2_drain (a := 2 * n + 5) (b := 0) (n + 4) (e := n + 3))
  rw [show 2 * n + 5 + 1 + (n + 4) = 3 * n + 10 from by ring]
  exact e_to_d (a := 3 * n + 10) (k := n + 3)

theorem main_trans : ∀ n, ⟨3 * n + 7, 0, 0, n + 2, 0⟩ [fm]⊢⁺ ⟨3 * n + 10, 0, 0, n + 3, 0⟩ := by
  intro n
  rw [show 3 * n + 7 = (3 * n + 6) + 1 from by ring,
      show n + 2 = n + 1 + 1 from by ring]
  apply stepPlus_stepStar_stepPlus (opening (a := 3 * n + 6) (d := n))
  exact middle_phase

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨4, 0, 0, 1, 0⟩) (by execute fm 4)
  apply progress_nonhalt_simple (fm := fm) (A := ℕ)
    (fun n ↦ ⟨3 * n + 4, 0, 0, n + 1, 0⟩) 0
  intro n
  rcases n with _ | n
  · exact ⟨1, n0_trans⟩
  · refine ⟨n + 2, ?_⟩
    show ⟨3 * (n + 1) + 4, 0, 0, (n + 1) + 1, 0⟩ [fm]⊢⁺ ⟨3 * (n + 2) + 4, 0, 0, (n + 2) + 1, 0⟩
    rw [show 3 * (n + 1) + 4 = 3 * n + 7 from by ring,
        show (n + 1) + 1 = n + 2 from by ring,
        show 3 * (n + 2) + 4 = 3 * n + 10 from by ring,
        show (n + 2) + 1 = n + 3 from by ring]
    exact main_trans n
