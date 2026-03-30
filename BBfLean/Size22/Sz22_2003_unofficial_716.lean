import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #716: [35/6, 4/55, 1331/2, 3/7, 14/11]

Vector representation:
```
-1 -1  1  1  0
 2  0 -1  0 -1
-1  0  0  0  3
 0  1  0 -1  0
 1  0  0  1 -1
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_716

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a+1, b+1, c, d, e⟩ => some ⟨a, b, c+1, d+1, e⟩
  | ⟨a, b, c+1, d, e+1⟩ => some ⟨a+2, b, c, d, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b, c, d, e+3⟩
  | ⟨a, b, c, d+1, e⟩ => some ⟨a, b+1, c, d, e⟩
  | ⟨a, b, c, d, e+1⟩ => some ⟨a+1, b, c, d+1, e⟩
  | _ => none

theorem r3_chain : ∀ k, ∀ a d e, ⟨a + k, 0, 0, d, e⟩ [fm]⊢* ⟨a, 0, 0, d, e + 3 * k⟩ := by
  intro k; induction' k with k ih <;> intro a d e
  · exists 0
  · rw [show a + (k + 1) = (a + k) + 1 from by ring]
    step fm
    apply stepStar_trans (ih a d (e + 3))
    ring_nf; finish

theorem r4_chain : ∀ k, ∀ b d e, ⟨0, b, 0, d + k, e⟩ [fm]⊢* ⟨0, b + k, 0, d, e⟩ := by
  intro k; induction' k with k ih <;> intro b d e
  · exists 0
  · rw [show d + (k + 1) = (d + k) + 1 from by ring]
    step fm
    apply stepStar_trans (ih (b + 1) d e)
    ring_nf; finish

theorem interleaved : ∀ b, ∀ a c d e, ⟨a + 1, b, c, d, e + c + b⟩ [fm]⊢* ⟨a + 2 * c + b + 1, 0, 0, d + b, e⟩ := by
  intro b; induction' b with b ih <;> intro a c d e
  · induction' c with c ihc generalizing a d e
    · ring_nf; finish
    · rw [show e + (c + 1) + 0 = (e + c + 0) + 1 from by ring,
          show a + 2 * (c + 1) + 0 + 1 = (a + 2) + 2 * c + 0 + 1 from by ring]
      rw [show (e + c + 0) + 1 = e + c + 0 + 1 from by ring]
      step fm
      apply stepStar_trans (ihc (a + 2) d e)
      ring_nf; finish
  · rw [show e + c + (b + 1) = (e + c + b) + 1 from by ring]
    step fm
    rcases a with _ | a
    · rw [show 0 + 2 * c + (b + 1) + 1 = 1 + 2 * c + b + 1 from by ring,
          show d + (b + 1) = (d + 1) + b from by ring,
          show e + c + b + 1 = (e + c + b) + 1 from by ring]
      step fm
      apply stepStar_trans (ih 1 c (d + 1) e)
      ring_nf; finish
    · rw [show (a + 1) + 2 * c + (b + 1) + 1 = a + 2 * (c + 1) + b + 1 from by ring,
          show d + (b + 1) = (d + 1) + b from by ring,
          show e + c + b + 1 = e + (c + 1) + b from by ring]
      exact ih a (c + 1) (d + 1) e

theorem main_trans (n : ℕ) :
    ⟨n + 2, 0, 0, n + 2, n * n + 2 * n + 3⟩ [fm]⊢⁺
    ⟨n + 3, 0, 0, n + 3, n * n + 4 * n + 6⟩ := by
  step fm
  rw [show n + 1 = 0 + (n + 1) from by ring]
  apply stepStar_trans (r3_chain (n + 1) 0 (n + 2) (n * n + 2 * n + 6))
  rw [show n * n + 2 * n + 6 + 3 * (n + 1) = n * n + 5 * n + 9 from by ring]
  rw [show n + 2 = 0 + (n + 2) from by ring]
  apply stepStar_trans (r4_chain (n + 2) 0 0 (n * n + 5 * n + 9))
  rw [show 0 + (n + 2) = n + 2 from by ring]
  rw [show n * n + 5 * n + 9 = (n * n + 5 * n + 8) + 1 from by ring]
  step fm
  rw [show n * n + 5 * n + 8 = (n * n + 4 * n + 6) + 0 + (n + 2) from by ring]
  apply stepStar_trans (interleaved (n + 2) 0 0 1 (n * n + 4 * n + 6))
  rw [show 0 + 2 * 0 + (n + 2) + 1 = n + 3 from by ring,
      show 1 + (n + 2) = n + 3 from by ring]
  finish

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨2, 0, 0, 2, 3⟩) (by execute fm 7)
  apply progress_nonhalt_simple (fm := fm) (A := ℕ)
    (fun n ↦ ⟨n + 2, 0, 0, n + 2, n * n + 2 * n + 3⟩) 0
  intro n
  refine ⟨n + 1, ?_⟩
  convert main_trans n using 2
  all_goals ring_nf

end Sz22_2003_unofficial_716
