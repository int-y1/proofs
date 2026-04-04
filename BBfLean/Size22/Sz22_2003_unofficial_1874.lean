import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #1874: [9/35, 325/33, 14/3, 11/13, 39/2]

Vector representation:
```
 0  2 -1 -1  0  0
 0 -1  2  0 -1  1
 1 -1  0  1  0  0
 0  0  0  0  1 -1
-1  1  0  0  0  1
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_1874

def Q := ℕ × ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a, b, c+1, d+1, e, f⟩ => some ⟨a, b+2, c, d, e, f⟩
  | ⟨a, b+1, c, d, e+1, f⟩ => some ⟨a, b, c+2, d, e, f+1⟩
  | ⟨a, b+1, c, d, e, f⟩ => some ⟨a+1, b, c, d+1, e, f⟩
  | ⟨a, b, c, d, e, f+1⟩ => some ⟨a, b, c, d, e+1, f⟩
  | ⟨a+1, b, c, d, e, f⟩ => some ⟨a, b+1, c, d, e, f+1⟩
  | _ => none

theorem f_to_e : ∀ k, ∀ a d e, ⟨a, 0, 0, d, e, k⟩ [fm]⊢* ⟨a, 0, 0, d, e + k, 0⟩ := by
  intro k; induction' k with k ih <;> intro a d e
  · exists 0
  · step fm; apply stepStar_trans (ih a d (e + 1)); ring_nf; finish

theorem b_to_ad : ∀ k, ∀ a d f, ⟨a, k, 0, d, 0, f⟩ [fm]⊢* ⟨a + k, 0, 0, d + k, 0, f⟩ := by
  intro k; induction' k with k ih <;> intro a d f
  · exists 0
  · step fm; apply stepStar_trans (ih (a + 1) (d + 1) f); ring_nf; finish

theorem r3r1_drain : ∀ C, ∀ a b f, ⟨a, b + 1, C + 1, 0, 0, f⟩ [fm]⊢*
    ⟨a + C + 1, b + C + 2, 0, 0, 0, f⟩ := by
  intro C; induction' C with C ih <;> intro a b f
  · step fm; step fm; finish
  · step fm; step fm
    convert ih (a + 1) (b + 1) f using 2
    ring_nf

theorem middle_e0 : ∀ D, D ≥ 1 → ∀ a b f,
    ⟨a, b, 2, D, 0, f⟩ [fm]⊢* ⟨a + b + 4, 0, 0, b + D + 2, f, 0⟩ := by
  intro D; induction' D using Nat.strongRecOn with D ihD; intro hD a b f
  rcases D with _ | _ | D
  · omega
  · step fm; apply stepStar_trans (r3r1_drain 0 a (b + 1) f)
    apply stepStar_trans (b_to_ad (b + 3) (a + 1) 0 f)
    convert f_to_e f (a + 1 + (b + 3)) (0 + (b + 3)) 0 using 2
    ring_nf
  · step fm; step fm
    apply stepStar_trans (b_to_ad (b + 2 + 2) a D f)
    convert f_to_e f (a + (b + 2 + 2)) (D + (b + 2 + 2)) 0 using 2
    ring_nf

theorem r1r1r2_chain : ∀ E, ∀ a b R f,
    ⟨a, b, 2, 2 * E + R, E, f⟩ [fm]⊢* ⟨a, b + 3 * E, 2, R, 0, f + E⟩ := by
  intro E; induction' E with E ih <;> intro a b R f
  · ring_nf; exists 0
  · rw [show 2 * (E + 1) + R = (2 * E + R) + 1 + 1 from by ring]
    step fm; step fm
    rw [show b + 2 + 2 = (b + 3) + 1 from by ring,
        show E + 1 = E + 1 from rfl]
    step fm
    apply stepStar_trans (ih a (b + 3) R (f + 1))
    ring_nf; finish

theorem main_trans : ∀ k n, ⟨3 * (n + k) + 1, 0, 0, 2 * n + k + 1, n + 1, 0⟩ [fm]⊢⁺
    ⟨3 * (2 * n + k + 1) + 1, 0, 0, 2 * (n + 1) + (n + k) + 1, (n + 1) + 1, 0⟩ := by
  intro k n
  step fm; step fm
  rw [show 2 * n + k + 1 = 2 * n + (k + 1) from by ring]
  apply stepStar_trans (r1r1r2_chain n (3 * (n + k)) 0 (k + 1) 2)
  rw [show (0 : ℕ) + 3 * n = 3 * n from by ring,
      show (2 : ℕ) + n = n + 2 from by ring]
  apply stepStar_trans (middle_e0 (k + 1) (by omega) (3 * (n + k)) (3 * n) (n + 2))
  ring_nf; finish

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨1, 0, 0, 1, 1, 0⟩) (by execute fm 3)
  apply progress_nonhalt_simple (fm := fm) (A := ℕ × ℕ)
    (fun ⟨k, n⟩ ↦ ⟨3 * (n + k) + 1, 0, 0, 2 * n + k + 1, n + 1, 0⟩) ⟨0, 0⟩
  intro ⟨k, n⟩
  refine ⟨⟨n + k, n + 1⟩, ?_⟩
  convert main_trans k n using 2
  ring_nf
