import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #811: [35/6, 715/2, 8/77, 3/5, 7/13]

Vector representation:
```
-1 -1  1  1  0  0
-1  0  1  0  1  1
 3  0  0 -1 -1  0
 0  1 -1  0  0  0
 0  0  0  1  0 -1
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_811

def Q := ℕ × ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a+1, b+1, c, d, e, f⟩ => some ⟨a, b, c+1, d+1, e, f⟩
  | ⟨a+1, b, c, d, e, f⟩ => some ⟨a, b, c+1, d, e+1, f+1⟩
  | ⟨a, b, c, d+1, e+1, f⟩ => some ⟨a+3, b, c, d, e, f⟩
  | ⟨a, b, c+1, d, e, f⟩ => some ⟨a, b+1, c, d, e, f⟩
  | ⟨a, b, c, d, e, f+1⟩ => some ⟨a, b, c, d+1, e, f⟩
  | _ => none

theorem c_to_b : ∀ k b, ⟨(0 : ℕ), b, k, 0, e, f⟩ [fm]⊢* ⟨(0 : ℕ), b + k, 0, 0, e, f⟩ := by
  intro k; induction' k with k ih <;> intro b
  · exists 0
  · step fm
    apply stepStar_trans (ih (b + 1))
    ring_nf; finish

theorem r1x3_r3_chain : ∀ k c d e f,
    ⟨(3 : ℕ), 3 * k, c, d, e + k, f⟩ [fm]⊢* ⟨(3 : ℕ), 0, c + 3 * k, d + 2 * k, e, f⟩ := by
  intro k; induction' k with k ih <;> intro c d e f
  · exists 0
  · rw [show 3 * (k + 1) = (3 * k) + 3 from by ring,
        show e + (k + 1) = (e + k) + 1 from by ring]
    step fm; step fm; step fm
    rw [show d + 3 = (d + 2) + 1 from by ring]
    step fm
    apply stepStar_trans (ih (c + 3) (d + 2) e f)
    ring_nf; finish

theorem r2x3_r3_chain : ∀ k c d e f,
    ⟨(3 : ℕ), 0, c, d + k, e, f⟩ [fm]⊢* ⟨(3 : ℕ), 0, c + 3 * k, d, e + 2 * k, f + 3 * k⟩ := by
  intro k; induction' k with k ih <;> intro c d e f
  · exists 0
  · rw [show d + (k + 1) = (d + k) + 1 from by ring]
    step fm; step fm; step fm
    rw [show e + 3 = (e + 2) + 1 from by ring]
    step fm
    apply stepStar_trans (ih (c + 3) d (e + 2) (f + 3))
    ring_nf; finish

theorem final_r2x3 : ⟨(3 : ℕ), 0, c, 0, e, f⟩ [fm]⊢⁺ ⟨(0 : ℕ), 0, c + 3, 0, e + 3, f + 3⟩ := by
  step fm; step fm; step fm; finish

theorem main_transition (n e f : ℕ) :
    ⟨(0 : ℕ), 3 * n, 0, 0, e + n + 1, f + 1⟩ [fm]⊢⁺
    ⟨(0 : ℕ), 9 * n + 3, 0, 0, e + 4 * n + 3, f + 6 * n + 3⟩ := by
  step fm
  rw [show e + n + 1 = (e + n) + 1 from by ring]
  step fm
  apply stepStar_trans (r1x3_r3_chain n 0 0 e f)
  rw [show (0 : ℕ) + 3 * n = 3 * n from by ring,
      show (0 : ℕ) + 2 * n = 2 * n from by ring]
  rw [show (2 * n : ℕ) = 0 + 2 * n from by ring]
  apply stepStar_trans (r2x3_r3_chain (2 * n) (3 * n) 0 e f)
  rw [show 3 * n + 3 * (2 * n) = 9 * n from by ring,
      show e + 2 * (2 * n) = e + 4 * n from by ring,
      show f + 3 * (2 * n) = f + 6 * n from by ring]
  apply stepStar_trans (stepPlus_stepStar (final_r2x3 (c := 9 * n) (e := e + 4 * n) (f := f + 6 * n)))
  apply stepStar_trans (c_to_b (9 * n + 3) 0 (e := e + 4 * n + 3) (f := f + 6 * n + 3))
  ring_nf; finish

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨0, 6, 0, 0, 4, 5⟩)
  · execute fm 17
  apply progress_nonhalt_simple (fm := fm) (A := ℕ × ℕ × ℕ)
    (fun ⟨n, e, f⟩ ↦ ⟨(0 : ℕ), 3 * n, 0, 0, e + n + 1, f + 1⟩) ⟨2, 1, 4⟩
  intro ⟨n, e, f⟩
  refine ⟨⟨3 * n + 1, e + n + 1, f + 6 * n + 2⟩, ?_⟩
  show ⟨(0 : ℕ), 3 * n, 0, 0, e + n + 1, f + 1⟩ [fm]⊢⁺
    ⟨(0 : ℕ), 3 * (3 * n + 1), 0, 0, (e + n + 1) + (3 * n + 1) + 1, (f + 6 * n + 2) + 1⟩
  rw [show 3 * (3 * n + 1) = 9 * n + 3 from by ring,
      show (e + n + 1) + (3 * n + 1) + 1 = e + 4 * n + 3 from by ring,
      show (f + 6 * n + 2) + 1 = f + 6 * n + 3 from by ring]
  exact main_transition n e f
