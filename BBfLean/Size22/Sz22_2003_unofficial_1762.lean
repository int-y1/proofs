import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #1762: [9/10, 22/21, 343/2, 5/11, 3/7]

Vector representation:
```
-1  2 -1  0  0
 1 -1  0 -1  1
-1  0  0  3  0
 0  0  1  0 -1
 0  1  0 -1  0
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_1762

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a+1, b, c+1, d, e⟩ => some ⟨a, b+2, c, d, e⟩
  | ⟨a, b+1, c, d+1, e⟩ => some ⟨a+1, b, c, d, e+1⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b, c, d+3, e⟩
  | ⟨a, b, c, d, e+1⟩ => some ⟨a, b, c+1, d, e⟩
  | ⟨a, b, c, d+1, e⟩ => some ⟨a, b+1, c, d, e⟩
  | _ => none

theorem r3_chain : ∀ k d e, ⟨k, 0, 0, d, e⟩ [fm]⊢* ⟨0, 0, 0, d + 3 * k, e⟩ := by
  intro k; induction' k with k ih <;> intro d e
  · exists 0
  · step fm
    apply stepStar_trans (ih (d + 3) e)
    ring_nf; finish

theorem e_to_c : ∀ k d c, ⟨0, 0, c, d, k⟩ [fm]⊢* ⟨0, 0, c + k, d, 0⟩ := by
  intro k; induction' k with k ih <;> intro d c
  · exists 0
  · step fm
    apply stepStar_trans (ih d (c + 1))
    ring_nf; finish

theorem chain : ∀ c b d e, ⟨0, b + 1, c, d + c, e⟩ [fm]⊢*
    ⟨0, b + c + 1, 0, d, e + c⟩ := by
  intro c; induction' c with c ih <;> intro b d e
  · exists 0
  · rw [show d + (c + 1) = (d + c) + 1 from by ring]
    step fm
    step fm
    rw [show b + 1 + 1 = (b + 1) + 1 from by ring]
    apply stepStar_trans (ih (b + 1) d (e + 1))
    ring_nf; finish

theorem drain : ∀ b a d e, ⟨a, b + 1, 0, d + 1, e⟩ [fm]⊢*
    ⟨0, 0, 0, 3 * a + 2 * b + d + 3, e + b + 1⟩ := by
  intro b; induction' b with b ih <;> intro a d e
  · step fm
    apply stepStar_trans (r3_chain (a + 1) d (e + 1))
    ring_nf; finish
  · step fm
    rcases d with _ | d'
    · step fm
      apply stepStar_trans (ih a 2 (e + 1))
      ring_nf; finish
    · apply stepStar_trans (ih (a + 1) d' (e + 1))
      ring_nf; finish

theorem main_trans : ∀ n, ⟨0, 0, 0, n + 3, n⟩ [fm]⊢⁺ ⟨0, 0, 0, 2 * n + 4, 2 * n + 1⟩ := by
  intro n
  rcases n with _ | m
  · execute fm 3
  · apply stepStar_stepPlus_stepPlus
    · show ⟨0, 0, 0, m + 1 + 3, m + 1⟩ [fm]⊢* ⟨0, 0, m + 1, m + 1 + 3, 0⟩
      have := e_to_c (m + 1) (m + 1 + 3) 0
      simp at this; exact this
    · show ⟨0, 0, m + 1, m + 1 + 3, 0⟩ [fm]⊢⁺ _
      rw [show m + 1 + 3 = (m + 3) + 1 from by ring]
      step fm
      show ⟨0, 1, m + 1, m + 3, 0⟩ [fm]⊢* _
      rw [show m + 3 = 2 + (m + 1) from by ring]
      apply stepStar_trans (chain (m + 1) 0 2 0)
      show ⟨0, 0 + (m + 1) + 1, 0, 2, 0 + (m + 1)⟩ [fm]⊢* _
      rw [show 0 + (m + 1) + 1 = (m + 1) + 1 from by ring,
          show 0 + (m + 1) = m + 1 from by ring,
          show m + 1 + 1 = (m + 1) + 1 from rfl,
          show (2 : ℕ) = 1 + 1 from by ring]
      apply stepStar_trans (drain (m + 1) 0 1 (m + 1))
      ring_nf; finish

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨0, 0, 0, 3, 0⟩) (by execute fm 1)
  apply progress_nonhalt_simple (fm := fm) (A := ℕ)
    (fun n ↦ ⟨0, 0, 0, n + 3, n⟩) 0
  intro n
  exact ⟨2 * n + 1, main_trans n⟩
