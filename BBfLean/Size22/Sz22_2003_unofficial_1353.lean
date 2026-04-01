import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #1353: [63/10, 4/33, 11/2, 5/7, 20/11]

Vector representation:
```
-1  2 -1  1  0
 2 -1  0  0 -1
-1  0  0  0  1
 0  0  1 -1  0
 2  0  1  0 -1
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_1353

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a+1, b, c+1, d, e⟩ => some ⟨a, b+2, c, d+1, e⟩
  | ⟨a, b+1, c, d, e+1⟩ => some ⟨a+2, b, c, d, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b, c, d, e+1⟩
  | ⟨a, b, c, d+1, e⟩ => some ⟨a, b, c+1, d, e⟩
  | ⟨a, b, c, d, e+1⟩ => some ⟨a+2, b, c+1, d, e⟩
  | _ => none

theorem r1r2_chain : ∀ k, ∀ b c d e,
    ⟨2, b, c + 2 * k, d, e + k⟩ [fm]⊢* ⟨2, b + 3 * k, c, d + 2 * k, e⟩ := by
  intro k; induction' k with k ih <;> intro b c d e
  · exists 0
  · rw [show c + 2 * (k + 1) = (c + 2 * k) + 1 + 1 from by ring,
        show e + (k + 1) = (e + k) + 1 from by ring]
    step fm; step fm; step fm
    apply stepStar_trans (ih (b + 3) c (d + 2) e); ring_nf; finish

theorem drain : ∀ b, ∀ a d e,
    ⟨a + 1, b, 0, d, e⟩ [fm]⊢* ⟨0, 0, 0, d, a + 1 + b + e⟩ := by
  intro b; induction' b with b ih <;> intro a d e
  · induction' a with a iha generalizing e
    · step fm; ring_nf; finish
    · step fm
      apply stepStar_trans (iha (e + 1)); ring_nf; finish
  · rcases e with _ | e
    · step fm; step fm
      apply stepStar_trans (ih (a + 1) d 0); ring_nf; finish
    · step fm
      apply stepStar_trans (ih (a + 2) d e); ring_nf; finish

theorem r4_transfer : ∀ k, ∀ c e,
    ⟨0, 0, c, k, e⟩ [fm]⊢* ⟨0, 0, c + k, 0, e⟩ := by
  intro k; induction' k with k ih <;> intro c e
  · exists 0
  · step fm
    apply stepStar_trans (ih (c + 1) e); ring_nf; finish

theorem main_even (m : ℕ) :
    ⟨0, 0, 2 * m + 2, 0, (2 * m + 3) * (m + 2)⟩ [fm]⊢⁺
    ⟨0, 0, 2 * m + 3, 0, (2 * m + 5) * (m + 2)⟩ := by
  rw [show (2 * m + 3) * (m + 2) = (2 * m * m + 6 * m + 4) + (m + 1) + 1 from by ring]
  step fm
  rw [show 2 * m + 2 + 1 = 1 + 2 * (m + 1) from by ring]
  apply stepStar_trans (r1r2_chain (m + 1) 0 1 0 (2 * m * m + 6 * m + 4))
  step fm
  rw [show (1 : ℕ) = 0 + 1 from rfl]
  apply stepStar_trans (drain (0 + 3 * (m + 1) + 2) 0 (0 + 2 * (m + 1) + 1) (2 * m * m + 6 * m + 4))
  rw [show 0 + 1 + (0 + 3 * (m + 1) + 2) + (2 * m * m + 6 * m + 4) = (2 * m + 5) * (m + 2) from by ring]
  apply stepStar_trans (r4_transfer (0 + 2 * (m + 1) + 1) 0 ((2 * m + 5) * (m + 2)))
  ring_nf; finish

theorem main_odd (m : ℕ) :
    ⟨0, 0, 2 * m + 3, 0, (2 * m + 5) * (m + 2)⟩ [fm]⊢⁺
    ⟨0, 0, 2 * m + 4, 0, (2 * m + 5) * (m + 3)⟩ := by
  rw [show (2 * m + 5) * (m + 2) = (2 * m * m + 8 * m + 7) + (m + 2) + 1 from by ring]
  step fm
  rw [show 2 * m + 3 + 1 = 0 + 2 * (m + 2) from by ring]
  apply stepStar_trans (r1r2_chain (m + 2) 0 0 0 (2 * m * m + 8 * m + 7))
  rw [show (2 : ℕ) = 1 + 1 from rfl]
  apply stepStar_trans (drain (0 + 3 * (m + 2)) 1 (0 + 2 * (m + 2)) (2 * m * m + 8 * m + 7))
  rw [show 1 + 1 + (0 + 3 * (m + 2)) + (2 * m * m + 8 * m + 7) = (2 * m + 5) * (m + 3) from by ring]
  apply stepStar_trans (r4_transfer (0 + 2 * (m + 2)) 0 ((2 * m + 5) * (m + 3)))
  ring_nf; finish

theorem main_trans (m : ℕ) :
    ⟨0, 0, 2 * m + 2, 0, (2 * m + 3) * (m + 2)⟩ [fm]⊢⁺
    ⟨0, 0, 2 * m + 4, 0, (2 * m + 5) * (m + 3)⟩ :=
  stepPlus_trans (main_even m) (main_odd m)

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨0, 0, 2, 0, 6⟩)
  · execute fm 28
  apply progress_nonhalt_simple (fm := fm) (A := ℕ)
    (fun m ↦ ⟨0, 0, 2 * m + 2, 0, (2 * m + 3) * (m + 2)⟩) 0
  intro m; exact ⟨m + 1, main_trans m⟩

end Sz22_2003_unofficial_1353
