import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #874: [4/15, 1/154, 21/2, 11/3, 100/7]

Vector representation:
```
 2 -1 -1  0  0
-1  0  0 -1 -1
-1  1  0  1  0
 0 -1  0  0  1
 2  0  2 -1  0
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_874

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a, b+1, c+1, d, e⟩ => some ⟨a+2, b, c, d, e⟩
  | ⟨a+1, b, c, d+1, e+1⟩ => some ⟨a, b, c, d, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b+1, c, d+1, e⟩
  | ⟨a, b+1, c, d, e⟩ => some ⟨a, b, c, d, e+1⟩
  | ⟨a, b, c, d+1, e⟩ => some ⟨a+2, b, c+2, d, e⟩
  | _ => none

theorem a_to_b : ∀ k a b d, ⟨a + k, b, 0, d, 0⟩ [fm]⊢* ⟨a, b + k, 0, d + k, 0⟩ := by
  intro k; induction' k with k ih <;> intro a b d
  · exists 0
  · rw [show a + (k + 1) = a + k + 1 from by ring]
    step fm
    apply stepStar_trans (ih a (b + 1) (d + 1))
    rw [show b + 1 + k = b + (k + 1) from by ring,
        show d + 1 + k = d + (k + 1) from by ring]
    finish

theorem b_to_e : ∀ k b d e, ⟨0, b + k, 0, d, e⟩ [fm]⊢* ⟨0, b, 0, d, e + k⟩ := by
  intro k; induction' k with k ih <;> intro b d e
  · exists 0
  · rw [show b + (k + 1) = b + k + 1 from by ring]
    step fm
    apply stepStar_trans (ih b d (e + 1))
    rw [show e + 1 + k = e + (k + 1) from by ring]
    finish

theorem drain_rounds : ∀ k c d e, ⟨0, 0, c, d + 3 * k, e + 2 * k⟩ [fm]⊢* ⟨0, 0, c + 2 * k, d, e⟩ := by
  intro k; induction' k with k ih <;> intro c d e
  · exists 0
  · rw [show d + 3 * (k + 1) = (d + 3) + 3 * k from by ring,
        show e + 2 * (k + 1) = (e + 2) + 2 * k from by ring]
    apply stepStar_trans (ih c (d + 3) (e + 2))
    rw [show d + 3 = d + 2 + 1 from by ring, show e + 2 = e + 1 + 1 from by ring]
    step fm
    rw [show d + 2 = d + 1 + 1 from by ring]
    step fm
    rw [show d + 1 = d + 0 + 1 from by ring, show e + 1 = e + 0 + 1 from by ring]
    step fm
    rw [show c + 2 * k + 2 = c + 2 * (k + 1) from by ring]
    finish

theorem drain_final : ∀ c d, ⟨0, 0, c, d + 2, 1⟩ [fm]⊢* ⟨1, 0, c + 2, d, 0⟩ := by
  intro c d
  rw [show d + 2 = d + 1 + 1 from by ring]
  step fm
  rw [show d + 1 = d + 0 + 1 from by ring]
  step fm
  finish

theorem drain : ∀ k c d, ⟨0, 0, c, d + 3 * k + 2, 2 * k + 1⟩ [fm]⊢* ⟨1, 0, c + 2 * k + 2, d, 0⟩ := by
  intro k c d
  rw [show d + 3 * k + 2 = (d + 2) + 3 * k from by ring,
      show 2 * k + 1 = 1 + 2 * k from by ring]
  apply stepStar_trans (drain_rounds k c (d + 2) 1)
  exact drain_final (c + 2 * k) d

theorem spiral : ∀ k a c d, ⟨a + 1, 0, c + k, d, 0⟩ [fm]⊢* ⟨a + k + 1, 0, c, d + k, 0⟩ := by
  intro k; induction' k with k ih <;> intro a c d
  · exists 0
  · rw [show c + (k + 1) = c + k + 1 from by ring,
        show a + 1 = a + 0 + 1 from by ring]
    step fm
    rw [show c + k + 1 = (c + k) + 1 from by ring]
    step fm
    rw [show a + 0 + 2 = (a + 1) + 1 from by ring]
    apply stepStar_trans (ih (a + 1) c (d + 1))
    rw [show a + 1 + k + 1 = a + (k + 1) + 1 from by ring,
        show d + 1 + k = d + (k + 1) from by ring]
    finish

theorem transition (m d' : ℕ) :
    ⟨2 * m + 1, 0, 0, d' + m + 1, 0⟩ [fm]⊢⁺ ⟨2 * m + 3, 0, 0, d' + 2 * m + 2, 0⟩ := by
  rw [show 2 * m + 1 = 2 * m + 0 + 1 from by ring]
  step fm
  -- After R3: (2*m+0, 0+1, 0, d'+m+1+1, 0) = (2*m, 1, 0, d'+m+2, 0)
  rw [show 2 * m = 0 + 2 * m from by ring,
      show d' + m + 1 + 1 = d' + m + 2 from by ring]
  apply stepStar_trans (a_to_b (2 * m) 0 1 (d' + m + 2))
  rw [show 1 + 2 * m = 2 * m + 1 from by ring,
      show d' + m + 2 + 2 * m = d' + 3 * m + 2 from by ring,
      show 2 * m + 1 = 0 + (2 * m + 1) from by ring]
  apply stepStar_trans (b_to_e (2 * m + 1) 0 (d' + 3 * m + 2) 0)
  rw [show 0 + (2 * m + 1) = 2 * m + 1 from by ring]
  apply stepStar_trans (drain m 0 d')
  rw [show 0 + 2 * m + 2 = 0 + (2 * m + 2) from by ring]
  apply stepStar_trans (spiral (2 * m + 2) 0 0 d')
  ring_nf; finish

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨5, 0, 0, 3, 0⟩) (by execute fm 27)
  apply progress_nonhalt_simple (fm := fm) (A := ℕ × ℕ)
    (fun ⟨m, d'⟩ ↦ ⟨2 * m + 1, 0, 0, d' + m + 1, 0⟩) ⟨2, 0⟩
  intro ⟨m, d'⟩
  refine ⟨⟨m + 1, d' + m⟩, ?_⟩
  show ⟨2 * m + 1, 0, 0, d' + m + 1, 0⟩ [fm]⊢⁺ ⟨2 * (m + 1) + 1, 0, 0, d' + m + (m + 1) + 1, 0⟩
  rw [show 2 * (m + 1) + 1 = 2 * m + 3 from by ring,
      show d' + m + (m + 1) + 1 = d' + 2 * m + 2 from by ring]
  exact transition m d'

end Sz22_2003_unofficial_874
