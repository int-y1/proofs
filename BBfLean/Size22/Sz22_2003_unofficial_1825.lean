import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #1825: [9/10, 55/21, 44/3, 7/11, 33/2]

Vector representation:
```
-1  2 -1  0  0
 0 -1  1 -1  1
 2 -1  0  0  1
 0  0  0  1 -1
-1  1  0  0  1
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_1825

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a+1, b, c+1, d, e⟩ => some ⟨a, b+2, c, d, e⟩
  | ⟨a, b+1, c, d+1, e⟩ => some ⟨a, b, c+1, d, e+1⟩
  | ⟨a, b+1, c, d, e⟩ => some ⟨a+2, b, c, d, e+1⟩
  | ⟨a, b, c, d, e+1⟩ => some ⟨a, b, c, d+1, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b+1, c, d, e+1⟩
  | _ => none

theorem e_to_d : ∀ k, ⟨a, 0, 0, d, e + k⟩ [fm]⊢* ⟨a, 0, 0, d + k, e⟩ := by
  intro k; induction' k with k ih generalizing d e
  · exists 0
  · rw [show e + (k + 1) = (e + k) + 1 from by ring]
    step fm
    apply stepStar_trans (ih (d := d + 1) (e := e))
    ring_nf; finish

theorem r3_chain : ∀ k, ⟨a, b + k, 0, 0, e⟩ [fm]⊢* ⟨a + 2 * k, b, 0, 0, e + k⟩ := by
  intro k; induction' k with k ih generalizing a b e
  · exists 0
  · rw [show b + (k + 1) = (b + k) + 1 from by ring]
    step fm
    apply stepStar_trans (ih (a := a + 2) (b := b) (e := e + 1))
    ring_nf; finish

theorem r2r1_pairs : ∀ k, ∀ B d e,
    ⟨k, B + 1, 0, d + k, e⟩ [fm]⊢* ⟨0, B + k + 1, 0, d, e + k⟩ := by
  intro k; induction' k with k ih <;> intro B d e
  · exists 0
  · rw [show d + (k + 1) = (d + k) + 1 from by ring]
    step fm; step fm
    apply stepStar_trans (ih (B + 1) d (e + 1))
    ring_nf; finish

theorem r2_repeat : ∀ k, ∀ b c e,
    ⟨0, b + k, c, k, e⟩ [fm]⊢* ⟨0, b, c + k, 0, e + k⟩ := by
  intro k; induction' k with k ih <;> intro b c e
  · exists 0
  · rw [show b + (k + 1) = (b + k) + 1 from by ring,
        show (k + 1 : ℕ) = k + 1 from rfl]
    step fm
    apply stepStar_trans (ih b (c + 1) (e + 1))
    ring_nf; finish

theorem phase4 : ∀ C, ∀ B E,
    ⟨0, B + 1, C + 1, 0, E⟩ [fm]⊢* ⟨2 * B + 3 * C + 5, 0, 0, 0, E + B + 2 * C + 3⟩ := by
  intro C; induction' C using Nat.strongRecOn with C ih; intro B E
  rcases C with _ | _ | C
  · step fm; step fm
    show ⟨1, B + 1 + 1, 0, 0, E + 1⟩ [fm]⊢* ⟨2 * B + 5, 0, 0, 0, E + B + 3⟩
    rw [show B + 1 + 1 = 0 + (B + 2) from by ring]
    apply stepStar_trans (r3_chain (B + 2) (a := 1) (b := 0) (e := E + 1))
    ring_nf; finish
  · step fm; step fm; step fm
    show ⟨0, B + 3 + 1, 0, 0, E + 1⟩ [fm]⊢* ⟨2 * B + 8, 0, 0, 0, E + B + 5⟩
    rw [show B + 3 + 1 = 0 + (B + 4) from by ring]
    apply stepStar_trans (r3_chain (B + 4) (a := 0) (b := 0) (e := E + 1))
    ring_nf; finish
  · step fm; step fm; step fm
    show ⟨0, B + 3 + 1, C + 1, 0, E + 1⟩ [fm]⊢*
      ⟨2 * B + 3 * (C + 2) + 5, 0, 0, 0, E + B + 2 * (C + 2) + 3⟩
    apply stepStar_trans (ih C (by omega) (B + 3) (E + 1))
    ring_nf; finish

theorem main_trans : ∀ a g,
    ⟨a + g + 2, 0, 0, a + 2 * g + 2, 0⟩ [fm]⊢⁺
    ⟨2 * a + 3 * g + 5, 0, 0, 2 * a + 4 * g + 6, 0⟩ := by
  intro a g
  step fm
  show ⟨a + g + 1, 0 + 1, 0, a + 2 * g + 2, 1⟩ [fm]⊢*
    ⟨2 * a + 3 * g + 5, 0, 0, 2 * a + 4 * g + 6, 0⟩
  rw [show a + 2 * g + 2 = (g + 1) + (a + g + 1) from by ring]
  apply stepStar_trans (r2r1_pairs (a + g + 1) 0 (g + 1) 1)
  show ⟨0, 0 + (a + g + 1) + 1, 0, g + 1, 1 + (a + g + 1)⟩ [fm]⊢*
    ⟨2 * a + 3 * g + 5, 0, 0, 2 * a + 4 * g + 6, 0⟩
  rw [show 0 + (a + g + 1) + 1 = (a + 1) + (g + 1) from by ring,
      show 1 + (a + g + 1) = a + g + 2 from by ring]
  apply stepStar_trans (r2_repeat (g + 1) (a + 1) 0 (a + g + 2))
  show ⟨0, a + 1, 0 + (g + 1), 0, a + g + 2 + (g + 1)⟩ [fm]⊢*
    ⟨2 * a + 3 * g + 5, 0, 0, 2 * a + 4 * g + 6, 0⟩
  rw [show 0 + (g + 1) = g + 1 from by ring,
      show a + g + 2 + (g + 1) = a + 2 * g + 3 from by ring,
      show a + 1 = a + 1 from rfl,
      show g + 1 = g + 1 from rfl]
  apply stepStar_trans (phase4 g a (a + 2 * g + 3))
  show ⟨2 * a + 3 * g + 5, 0, 0, 0, a + 2 * g + 3 + a + 2 * g + 3⟩ [fm]⊢*
    ⟨2 * a + 3 * g + 5, 0, 0, 2 * a + 4 * g + 6, 0⟩
  rw [show a + 2 * g + 3 + a + 2 * g + 3 = 0 + (2 * a + 4 * g + 6) from by ring]
  apply stepStar_trans (e_to_d (2 * a + 4 * g + 6) (a := 2 * a + 3 * g + 5) (d := 0) (e := 0))
  ring_nf; finish

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨2, 0, 0, 2, 0⟩) (by execute fm 4)
  apply progress_nonhalt_simple (fm := fm) (A := ℕ × ℕ)
    (fun ⟨a, g⟩ ↦ ⟨a + g + 2, 0, 0, a + 2 * g + 2, 0⟩) ⟨0, 0⟩
  intro ⟨a, g⟩
  refine ⟨⟨2 * a + 2 * g + 2, g + 1⟩, ?_⟩
  show ⟨a + g + 2, 0, 0, a + 2 * g + 2, 0⟩ [fm]⊢⁺
    ⟨2 * a + 2 * g + 2 + (g + 1) + 2, 0, 0, 2 * a + 2 * g + 2 + 2 * (g + 1) + 2, 0⟩
  rw [show 2 * a + 2 * g + 2 + (g + 1) + 2 = 2 * a + 3 * g + 5 from by ring,
      show 2 * a + 2 * g + 2 + 2 * (g + 1) + 2 = 2 * a + 4 * g + 6 from by ring]
  exact main_trans a g

end Sz22_2003_unofficial_1825
