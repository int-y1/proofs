import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #1032: [4/45, 5/14, 99/2, 21/11, 5/3]

Vector representation:
```
 2 -2 -1  0  0
-1  0  1 -1  0
-1  2  0  0  1
 0  1  0  1 -1
 0 -1  1  0  0
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_1032

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a, b+2, c+1, d, e⟩ => some ⟨a+2, b, c, d, e⟩
  | ⟨a+1, b, c, d+1, e⟩ => some ⟨a, b, c+1, d, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b+2, c, d, e+1⟩
  | ⟨a, b, c, d, e+1⟩ => some ⟨a, b+1, c, d+1, e⟩
  | ⟨a, b+1, c, d, e⟩ => some ⟨a, b, c+1, d, e⟩
  | _ => none

theorem r3_chain : ∀ k, ∀ a b e,
    ⟨a + k, b, (0 : ℕ), 0, e⟩ [fm]⊢* ⟨a, b + 2 * k, 0, 0, e + k⟩ := by
  intro k; induction' k with k ih <;> intro a b e
  · ring_nf; finish
  · rw [show a + (k + 1) = (a + k) + 1 from by ring,
        show b + 2 * (k + 1) = (b + 2) + 2 * k from by ring,
        show e + (k + 1) = (e + 1) + k from by ring]
    step fm
    apply stepStar_trans (ih a (b + 2) (e + 1))
    ring_nf; finish

theorem r4_chain : ∀ k, ∀ b d,
    ⟨(0 : ℕ), b, 0, d, k⟩ [fm]⊢* ⟨0, b + k, 0, d + k, 0⟩ := by
  intro k; induction' k with k ih <;> intro b d
  · ring_nf; finish
  · rw [show b + (k + 1) = (b + 1) + k from by ring,
        show d + (k + 1) = (d + 1) + k from by ring]
    step fm
    apply stepStar_trans (ih (b + 1) (d + 1))
    ring_nf; finish

theorem r1_step : ∀ a b d,
    ⟨a, b + 2, (1 : ℕ), d, 0⟩ [fm]⊢ ⟨a + 2, b, 0, d, 0⟩ := by
  intro a b d; unfold fm; simp

theorem r2_apply (a b d e : ℕ) :
    fm ⟨a + 1, b, 0, d + 1, e⟩ = some ⟨a, b, 1, d, e⟩ := by
  unfold fm
  cases b with
  | zero => simp
  | succ b' => cases b' with
    | zero => simp
    | succ b'' => simp

theorem r1r2_step : ∀ a b d,
    ⟨a, b + 2, (1 : ℕ), d + 1, 0⟩ [fm]⊢* ⟨a + 1, b, 1, d, 0⟩ := by
  intro a b d
  apply stepStar_trans (step_stepStar (r1_step a b (d + 1)))
  rw [show a + 2 = (a + 1) + 1 from by ring]
  exact step_stepStar (r2_apply (a + 1) b d 0)

theorem r1r2_chain : ∀ k, ∀ a b d,
    ⟨a, b + 2 * k, (1 : ℕ), d + k, 0⟩ [fm]⊢* ⟨a + k, b, 1, d, 0⟩ := by
  intro k; induction' k with k ih <;> intro a b d
  · ring_nf; finish
  · rw [show b + 2 * (k + 1) = (b + 2 * k) + 2 from by ring,
        show d + (k + 1) = (d + k) + 1 from by ring,
        show a + (k + 1) = (a + 1) + k from by ring]
    apply stepStar_trans (r1r2_step a (b + 2 * k) (d + k))
    apply stepStar_trans (ih (a + 1) b d)
    ring_nf; finish

theorem main_trans (n : ℕ) :
    ⟨2 * n + 7, n * n + 3 * n, (0 : ℕ), 0, 0⟩ [fm]⊢⁺
    ⟨2 * n + 9, n * n + 5 * n + 4, 0, 0, 0⟩ := by
  have h1 : ⟨2 * n + 7, n * n + 3 * n, (0 : ℕ), 0, 0⟩ [fm]⊢*
      ⟨0, n * n + 3 * n + 2 * (2 * n + 7), 0, 0, 2 * n + 7⟩ := by
    have := r3_chain (2 * n + 7) 0 (n * n + 3 * n) 0
    convert this using 1; ring_nf
  have h2 : ⟨(0 : ℕ), n * n + 3 * n + 2 * (2 * n + 7), 0, 0, 2 * n + 7⟩ [fm]⊢*
      ⟨0, n * n + 3 * n + 3 * (2 * n + 7), 0, 2 * n + 7, 0⟩ := by
    have := r4_chain (2 * n + 7) (n * n + 3 * n + 2 * (2 * n + 7)) 0
    convert this using 1; ring_nf
  have h3 : ⟨(0 : ℕ), n * n + 3 * n + 3 * (2 * n + 7), 0, 2 * n + 7, 0⟩ [fm]⊢⁺
      ⟨0, n * n + 9 * n + 20, 1, 2 * n + 7, 0⟩ := by
    rw [show n * n + 3 * n + 3 * (2 * n + 7) = (n * n + 9 * n + 20) + 1 from by ring]
    step fm; finish
  have h4 : ⟨(0 : ℕ), n * n + 9 * n + 20, 1, 2 * n + 7, 0⟩ [fm]⊢*
      ⟨2 * n + 7, n * n + 5 * n + 6, 1, 0, 0⟩ := by
    have := r1r2_chain (2 * n + 7) 0 (n * n + 5 * n + 6) 0
    convert this using 1; ring_nf
  have h5 : ⟨2 * n + 7, n * n + 5 * n + 6, (1 : ℕ), 0, 0⟩ [fm]⊢⁺
      ⟨2 * n + 9, n * n + 5 * n + 4, 0, 0, 0⟩ := by
    rw [show n * n + 5 * n + 6 = (n * n + 5 * n + 4) + 2 from by ring]
    step fm; finish
  exact stepStar_stepPlus_stepPlus h1
    (stepStar_stepPlus_stepPlus h2
      (stepPlus_trans h3
        (stepStar_stepPlus_stepPlus h4 h5)))

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨7, 0, 0, 0, 0⟩) (by execute fm 42)
  apply progress_nonhalt_simple (fm := fm) (A := ℕ)
    (fun n ↦ ⟨2 * n + 7, n * n + 3 * n, 0, 0, 0⟩) 0
  intro n
  refine ⟨n + 1, ?_⟩
  have := main_trans n
  convert this using 1; ring_nf
