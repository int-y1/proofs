import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #1745: [8/15, 33/14, 715/2, 7/11, 3/13]

Vector representation:
```
 3 -1 -1  0  0  0
-1  1  0 -1  1  0
-1  0  1  0  1  1
 0  0  0  1 -1  0
 0  1  0  0  0 -1
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_1745

def Q := ℕ × ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a, b+1, c+1, d, e, f⟩ => some ⟨a+3, b, c, d, e, f⟩
  | ⟨a+1, b, c, d+1, e, f⟩ => some ⟨a, b+1, c, d, e+1, f⟩
  | ⟨a+1, b, c, d, e, f⟩ => some ⟨a, b, c+1, d, e+1, f+1⟩
  | ⟨a, b, c, d, e+1, f⟩ => some ⟨a, b, c, d+1, e, f⟩
  | ⟨a, b, c, d, e, f+1⟩ => some ⟨a, b+1, c, d, e, f⟩
  | _ => none

theorem r3_chain : ∀ n, ⟨a + n, 0, c, 0, e, f⟩ [fm]⊢* ⟨a, 0, c + n, 0, e + n, f + n⟩ := by
  intro n; induction' n with n ih generalizing a c e f
  · exists 0
  · rw [show a + (n + 1) = (a + n) + 1 from by ring]
    step fm
    apply stepStar_trans (ih (a := a) (c := c + 1) (e := e + 1) (f := f + 1))
    ring_nf; finish

theorem r4_chain : ∀ n, ⟨0, 0, c, d, e + n, f⟩ [fm]⊢* ⟨0, 0, c, d + n, e, f⟩ := by
  intro n; induction' n with n ih generalizing c d e f
  · exists 0
  · rw [show e + (n + 1) = (e + n) + 1 from by ring]
    step fm
    apply stepStar_trans (ih (d := d + 1))
    ring_nf; finish

theorem r5r1 : ⟨0, 0, c + 1, d, 0, f + 1⟩ [fm]⊢⁺ ⟨3, 0, c, d, 0, f⟩ := by
  step fm; step fm; finish

theorem r2r1_chain : ∀ n, ⟨a + 1, 0, c + n, d + n, e, f⟩ [fm]⊢* ⟨a + 2 * n + 1, 0, c, d, e + n, f⟩ := by
  intro n; induction' n with n ih generalizing a c d e f
  · exists 0
  · rw [show a + 1 = (a + 2) + 1 - 2 from by omega]
    rw [show c + (n + 1) = (c + n) + 1 from by ring]
    rw [show d + (n + 1) = (d + n) + 1 from by ring]
    rw [show (a + 2) + 1 - 2 = a + 1 from by omega]
    step fm
    step fm
    apply stepStar_trans (ih (a := a + 2) (c := c) (d := d) (e := e + 1))
    ring_nf; finish

theorem r2_chain : ∀ n, ⟨a + n, b, 0, d + n, e, f⟩ [fm]⊢* ⟨a, b + n, 0, d, e + n, f⟩ := by
  intro n; induction' n with n ih generalizing a b d e f
  · exists 0
  · rw [show a + (n + 1) = (a + n) + 1 from by ring,
        show d + (n + 1) = (d + n) + 1 from by ring]
    step fm
    apply stepStar_trans (ih (a := a) (b := b + 1) (d := d) (e := e + 1))
    ring_nf; finish

theorem r3r1_chain : ∀ n, ⟨a + 1, b + n, 0, 0, e, f⟩ [fm]⊢* ⟨a + 2 * n + 1, b, 0, 0, e + n, f + n⟩ := by
  intro n; induction' n with n ih generalizing a b e f
  · exists 0
  · rw [show b + (n + 1) = (b + n) + 1 from by ring]
    step fm
    step fm
    apply stepStar_trans (ih (a := a + 2) (b := b) (e := e + 1) (f := f + 1))
    ring_nf; finish

theorem main_trans (k G : ℕ) :
    ⟨2 * k + G + 1, 0, 0, 0, k + G, G⟩ [fm]⊢⁺
    ⟨5 * k + 3 * G + 4, 0, 0, 0, 4 * k + 3 * G + 2, 3 * k + 3 * G + 1⟩ := by
  rw [show 2 * k + G + 1 = 0 + (2 * k + G + 1) from by ring]
  apply stepStar_stepPlus_stepPlus
    (r3_chain (2 * k + G + 1) (a := 0) (c := 0) (e := k + G) (f := G))
  rw [show 0 + (2 * k + G + 1) = 2 * k + G + 1 from by ring,
      show k + G + (2 * k + G + 1) = 0 + (3 * k + 2 * G + 1) from by ring,
      show G + (2 * k + G + 1) = 2 * k + 2 * G + 1 from by ring]
  apply stepStar_stepPlus_stepPlus
    (r4_chain (3 * k + 2 * G + 1) (c := 2 * k + G + 1) (d := 0) (e := 0) (f := 2 * k + 2 * G + 1))
  rw [show 2 * k + G + 1 = (2 * k + G) + 1 from by ring,
      show 2 * k + 2 * G + 1 = (2 * k + 2 * G) + 1 from by ring]
  apply stepPlus_stepStar_stepPlus
    (r5r1 (c := 2 * k + G) (d := 0 + (3 * k + 2 * G + 1)) (f := 2 * k + 2 * G))
  rw [show 2 * k + G = 0 + (2 * k + G) from by ring,
      show 0 + (3 * k + 2 * G + 1) = (k + G + 1) + (2 * k + G) from by ring]
  apply stepStar_trans
    (r2r1_chain (2 * k + G) (a := 2) (c := 0) (d := k + G + 1) (e := 0) (f := 2 * k + 2 * G))
  rw [show 0 + (2 * k + G) = 2 * k + G from by ring,
      show 2 + 2 * (2 * k + G) + 1 = 4 * k + 2 * G + 3 from by ring]
  have h5 := r2_chain (k + G + 1) (a := 3 * k + G + 2) (b := 0) (d := 0) (e := 2 * k + G) (f := 2 * k + 2 * G)
  rw [Nat.zero_add] at h5
  rw [show 4 * k + 2 * G + 3 = (3 * k + G + 2) + (k + G + 1) from by ring]
  apply stepStar_trans h5
  rw [show 3 * k + G + 2 = (3 * k + G + 1) + 1 from by ring,
      show 2 * k + G + (k + G + 1) = 3 * k + 2 * G + 1 from by ring]
  have h6 := r3r1_chain (k + G + 1) (a := 3 * k + G + 1) (b := 0) (e := 3 * k + 2 * G + 1) (f := 2 * k + 2 * G)
  rw [Nat.zero_add] at h6
  apply stepStar_trans h6
  ring_nf; finish

theorem nonhalt : ¬halts fm c₀ := by
  apply progress_nonhalt_simple (fm := fm) (A := ℕ × ℕ)
    (fun p ↦ ⟨2 * p.1 + p.2 + 1, 0, 0, 0, p.1 + p.2, p.2⟩) ⟨0, 0⟩
  intro ⟨k, G⟩
  refine ⟨⟨k + 1, 3 * k + 3 * G + 1⟩, ?_⟩
  show ⟨2 * k + G + 1, 0, 0, 0, k + G, G⟩ [fm]⊢⁺ ⟨2 * (k + 1) + (3 * k + 3 * G + 1) + 1, 0, 0, 0, (k + 1) + (3 * k + 3 * G + 1), 3 * k + 3 * G + 1⟩
  rw [show 2 * (k + 1) + (3 * k + 3 * G + 1) + 1 = 5 * k + 3 * G + 4 from by ring,
      show (k + 1) + (3 * k + 3 * G + 1) = 4 * k + 3 * G + 2 from by ring]
  exact main_trans k G
