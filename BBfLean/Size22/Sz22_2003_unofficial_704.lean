import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #704: [35/6, 4/55, 121/2, 3/7, 28/11]

Vector representation:
```
-1 -1  1  1  0
 2  0 -1  0 -1
-1  0  0  0  2
 0  1  0 -1  0
 2  0  0  1 -1
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_704

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a+1, b+1, c, d, e⟩ => some ⟨a, b, c+1, d+1, e⟩
  | ⟨a, b, c+1, d, e+1⟩ => some ⟨a+2, b, c, d, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b, c, d, e+2⟩
  | ⟨a, b, c, d+1, e⟩ => some ⟨a, b+1, c, d, e⟩
  | ⟨a, b, c, d, e+1⟩ => some ⟨a+2, b, c, d+1, e⟩
  | _ => none

theorem r3_chain : ∀ k, ∀ a d e, ⟨a + k, 0, 0, d, e⟩ [fm]⊢* ⟨a, 0, 0, d, e + 2 * k⟩ := by
  intro k; induction' k with k ih <;> intro a d e
  · exists 0
  · rw [show a + (k + 1) = (a + k) + 1 from by ring]
    step fm
    apply stepStar_trans (ih a d (e + 2))
    ring_nf; finish

theorem r4_chain : ∀ k, ∀ b d e, ⟨0, b, 0, d + k, e⟩ [fm]⊢* ⟨0, b + k, 0, d, e⟩ := by
  intro k; induction' k with k ih <;> intro b d e
  · exists 0
  · rw [show d + (k + 1) = (d + k) + 1 from by ring]
    step fm
    apply stepStar_trans (ih (b + 1) d e)
    ring_nf; finish

theorem r2_chain : ∀ k, ∀ a d e, ⟨a, 0, k, d, e + k⟩ [fm]⊢* ⟨a + 2 * k, 0, 0, d, e⟩ := by
  intro k; induction' k with k ih <;> intro a d e
  · exists 0
  · rw [show e + (k + 1) = (e + k) + 1 from by ring]
    step fm
    apply stepStar_trans (ih (a + 2) d e)
    ring_nf; finish

theorem r1r1r2_chain : ∀ k, ∀ b c d e, ⟨2, b + 2 * k, c, d, e + k⟩ [fm]⊢* ⟨2, b, c + k, d + 2 * k, e⟩ := by
  intro k; induction' k with k ih <;> intro b c d e
  · exists 0
  · rw [show b + 2 * (k + 1) = (b + 2 * k + 1) + 1 from by ring,
        show e + (k + 1) = (e + k) + 1 from by ring]
    step fm
    rw [show b + 2 * k + 1 = (b + 2 * k) + 1 from by ring]
    step fm; step fm
    apply stepStar_trans (ih b (c + 1) (d + 2) e)
    ring_nf; finish

theorem main_even (k e : ℕ) :
    ⟨2 * k + 1, 0, 0, 2 * k, e⟩ [fm]⊢⁺ ⟨2 * k + 2, 0, 0, 2 * k + 1, e + 2 * k + 1⟩ := by
  rw [show 2 * k + 1 = 0 + (2 * k + 1) from by ring]
  apply step_stepStar_stepPlus
  · show fm ⟨0 + (2 * k + 1), 0, 0, 2 * k, e⟩ = some ⟨0 + (2 * k), 0, 0, 2 * k, e + 2⟩
    simp [fm]
  apply stepStar_trans (r3_chain (2 * k) 0 (2 * k) (e + 2))
  rw [show e + 2 + 2 * (2 * k) = e + 4 * k + 2 from by ring,
      show 2 * k = 0 + (2 * k) from by ring]
  apply stepStar_trans (r4_chain (2 * k) 0 0 (e + 4 * k + 2))
  rw [show 0 + (2 * k) = 2 * k from by ring,
      show e + 4 * k + 2 = (e + 4 * k + 1) + 1 from by ring]
  step fm
  rw [show e + 4 * k + 1 = (e + 3 * k + 1) + k from by ring,
      show 2 * k = 0 + 2 * k from by ring]
  apply stepStar_trans (r1r1r2_chain k 0 0 1 (e + 3 * k + 1))
  rw [show 0 + k = k from by ring,
      show 1 + 2 * k = 2 * k + 1 from by ring,
      show e + 3 * k + 1 = (e + 2 * k + 1) + k from by ring]
  apply stepStar_trans (r2_chain k 2 (2 * k + 1) (e + 2 * k + 1))
  ring_nf; finish

theorem main_odd (k e : ℕ) :
    ⟨2 * k + 2, 0, 0, 2 * k + 1, e⟩ [fm]⊢⁺ ⟨2 * k + 3, 0, 0, 2 * k + 2, e + 2 * k + 2⟩ := by
  rw [show 2 * k + 2 = 0 + (2 * k + 2) from by ring]
  apply step_stepStar_stepPlus
  · show fm ⟨0 + (2 * k + 2), 0, 0, 2 * k + 1, e⟩ = some ⟨0 + (2 * k + 1), 0, 0, 2 * k + 1, e + 2⟩
    simp [fm]
  apply stepStar_trans (r3_chain (2 * k + 1) 0 (2 * k + 1) (e + 2))
  rw [show e + 2 + 2 * (2 * k + 1) = e + 4 * k + 4 from by ring,
      show 2 * k + 1 = 0 + (2 * k + 1) from by ring]
  apply stepStar_trans (r4_chain (2 * k + 1) 0 0 (e + 4 * k + 4))
  rw [show 0 + (2 * k + 1) = 2 * k + 1 from by ring,
      show e + 4 * k + 4 = (e + 4 * k + 3) + 1 from by ring]
  step fm
  rw [show e + 4 * k + 3 = (e + 3 * k + 3) + k from by ring,
      show 2 * k + 1 = 1 + 2 * k from by ring]
  apply stepStar_trans (r1r1r2_chain k 1 0 1 (e + 3 * k + 3))
  rw [show 0 + k = k from by ring,
      show 1 + 2 * k = 2 * k + 1 from by ring]
  step fm
  rw [show e + 3 * k + 3 = (e + 2 * k + 2) + (k + 1) from by ring]
  apply stepStar_trans (r2_chain (k + 1) 1 (2 * k + 2) (e + 2 * k + 2))
  ring_nf; finish

theorem main_trans (n e : ℕ) :
    ⟨n + 1, 0, 0, n, e⟩ [fm]⊢⁺ ⟨n + 2, 0, 0, n + 1, e + n + 1⟩ := by
  rcases Nat.even_or_odd n with ⟨k, hk⟩ | ⟨k, hk⟩
  · rw [show k + k = 2 * k from by ring] at hk; subst hk
    have := main_even k e
    convert this using 2
  · subst hk
    have := main_odd k e
    convert this using 2

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨3, 0, 0, 2, 3⟩) (by execute fm 8)
  apply progress_nonhalt_simple (fm := fm) (A := ℕ × ℕ)
    (fun ⟨n, e⟩ ↦ ⟨n + 1, 0, 0, n, e⟩) ⟨2, 3⟩
  intro ⟨n, e⟩; exact ⟨⟨n + 1, e + n + 1⟩, main_trans n e⟩

end Sz22_2003_unofficial_704
