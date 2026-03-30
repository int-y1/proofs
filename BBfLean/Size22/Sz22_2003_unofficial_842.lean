import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #842: [36/35, 5/22, 147/2, 11/3, 5/7]

Vector representation:
```
 2  2 -1 -1  0
-1  0  1  0 -1
-1  1  0  2  0
 0 -1  0  0  1
 0  0  1 -1  0
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_842

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a, b, c+1, d+1, e⟩ => some ⟨a+2, b+2, c, d, e⟩
  | ⟨a+1, b, c, d, e+1⟩ => some ⟨a, b, c+1, d, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b+1, c, d+2, e⟩
  | ⟨a, b+1, c, d, e⟩ => some ⟨a, b, c, d, e+1⟩
  | ⟨a, b, c, d+1, e⟩ => some ⟨a, b, c+1, d, e⟩
  | _ => none

theorem b_to_e : ∀ k, ⟨0, b + k, 0, d, e⟩ [fm]⊢* ⟨0, b, 0, d, e + k⟩ := by
  intro k; induction' k with k ih generalizing b e
  · exists 0
  · rw [Nat.add_succ b k]
    step fm
    apply stepStar_trans (ih (e := e + 1))
    ring_nf; finish

theorem r3_drain : ∀ a, ⟨a, b, 0, d, 0⟩ [fm]⊢* ⟨0, b + a, 0, d + 2 * a, 0⟩ := by
  intro a; induction' a with a ih generalizing b d
  · exists 0
  · step fm
    apply stepStar_trans (ih (b := b + 1) (d := d + 2))
    ring_nf; finish

theorem r2r1_pairs : ∀ k, ⟨a + 1, b, 0, d + k, e + k⟩ [fm]⊢* ⟨a + k + 1, b + 2 * k, 0, d, e⟩ := by
  intro k; induction' k with k ih generalizing a b d e
  · exists 0
  · rw [show d + (k + 1) = (d + k) + 1 from by ring,
        show e + (k + 1) = (e + k) + 1 from by ring]
    step fm; step fm
    rw [show a + 1 + 1 = (a + 1) + 1 from by ring]
    apply stepStar_trans (ih (a := a + 1) (b := b + 2))
    ring_nf; finish

theorem r2_drain : ∀ k, ⟨a + k, b, c, 0, k⟩ [fm]⊢* ⟨a, b, c + k, 0, 0⟩ := by
  intro k; induction' k with k ih generalizing a b c
  · exists 0
  · rw [show a + (k + 1) = (a + k) + 1 from by ring]
    step fm
    apply stepStar_trans (ih (c := c + 1))
    ring_nf; finish

theorem discharge : ∀ c, ∀ a b, ⟨a + 1, b, c, 0, 0⟩ [fm]⊢* ⟨0, b + a + 4 * c + 1, 0, 2 * a + 3 * c + 2, 0⟩ := by
  intro c; induction' c using Nat.strongRecOn with c ih; intro a b
  rcases c with _ | _ | c
  · apply stepStar_trans (r3_drain (a + 1) (b := b) (d := 0))
    ring_nf; finish
  · step fm; step fm; step fm
    apply stepStar_trans (r3_drain (a + 1) (b := b + 4) (d := 3))
    ring_nf; finish
  · step fm; step fm; step fm
    rw [show a + 3 + 1 = (a + 3) + 1 from by ring]
    apply stepStar_trans (ih c (by omega) (a + 3) (b + 5))
    ring_nf; finish

theorem spiral_to_end : ⟨2, 2, 0, n, 2 * n + 1⟩ [fm]⊢* ⟨0, 6 * n + 7, 0, 3 * n + 5, 0⟩ := by
  have h1 : ⟨2, 2, 0, n, 2 * n + 1⟩ [fm]⊢* ⟨n + 2, 2 * n + 2, 0, 0, n + 1⟩ := by
    convert r2r1_pairs n (a := 1) (b := 2) (d := 0) (e := n + 1) using 2
    all_goals (first | rfl | ring_nf)
  have h2 : ⟨n + 2, 2 * n + 2, 0, 0, n + 1⟩ [fm]⊢* ⟨1, 2 * n + 2, n + 1, 0, 0⟩ := by
    convert r2_drain (n + 1) (a := 1) (b := 2 * n + 2) (c := 0) using 2
    all_goals (first | rfl | ring_nf)
  have h3 : ⟨1, 2 * n + 2, n + 1, 0, 0⟩ [fm]⊢* ⟨0, 6 * n + 7, 0, 3 * n + 5, 0⟩ := by
    convert discharge (n + 1) 0 (2 * n + 2) using 2
    all_goals (first | rfl | ring_nf)
  exact stepStar_trans h1 (stepStar_trans h2 h3)

theorem phase2 : ⟨0, 0, 0, n + 2, 2 * n + 1⟩ [fm]⊢⁺ ⟨0, 6 * n + 7, 0, 3 * n + 5, 0⟩ := by
  step fm; step fm
  show ⟨2, 2, 0, n, 2 * n + 1⟩ [fm]⊢* ⟨0, 6 * n + 7, 0, 3 * n + 5, 0⟩
  exact spiral_to_end

theorem main_trans : ⟨0, 2 * n + 1, 0, n + 2, 0⟩ [fm]⊢⁺ ⟨0, 6 * n + 7, 0, 3 * n + 5, 0⟩ := by
  have hb : ⟨0, 2 * n + 1, 0, n + 2, 0⟩ [fm]⊢* ⟨0, 0, 0, n + 2, 2 * n + 1⟩ := by
    convert b_to_e (2 * n + 1) (b := 0) (d := n + 2) (e := 0) using 2
    all_goals (first | rfl | ring_nf)
  exact stepStar_stepPlus_stepPlus hb phase2

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨0, 1, 0, 2, 0⟩)
  · execute fm 1
  apply progress_nonhalt_simple (fm := fm) (A := ℕ)
    (fun n ↦ ⟨0, 2 * n + 1, 0, n + 2, 0⟩) 0
  intro n; refine ⟨3 * n + 3, ?_⟩
  convert main_trans using 2
  all_goals (first | rfl | ring_nf)
