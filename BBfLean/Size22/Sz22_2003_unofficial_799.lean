import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #799: [35/6, 605/2, 4/77, 3/5, 6/11]

Vector representation:
```
-1 -1  1  1  0
-1  0  1  0  2
 2  0  0 -1 -1
 0  1 -1  0  0
 1  1  0  0 -1
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_799

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a+1, b+1, c, d, e⟩ => some ⟨a, b, c+1, d+1, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b, c+1, d, e+2⟩
  | ⟨a, b, c, d+1, e+1⟩ => some ⟨a+2, b, c, d, e⟩
  | ⟨a, b, c+1, d, e⟩ => some ⟨a, b+1, c, d, e⟩
  | ⟨a, b, c, d, e+1⟩ => some ⟨a+1, b+1, c, d, e⟩
  | _ => none

theorem c_to_b : ∀ k, ⟨0, b, c + k, 0, e⟩ [fm]⊢* ⟨0, b + k, c, 0, e⟩ := by
  intro k; induction' k with k ih generalizing b c
  · exists 0
  · rw [show c + (k + 1) = (c + k) + 1 from by ring]
    step fm
    apply stepStar_trans (ih (b := b + 1))
    ring_nf; finish

theorem spiral_chain : ∀ n, ∀ p q r,
    ⟨0, 2 * n + 1, p, q + 1, r + n + 1⟩ [fm]⊢* ⟨1, 0, p + 2 * n + 1, q + n + 1, r⟩ := by
  intro n; induction' n with n ih <;> intro p q r
  · step fm; step fm; ring_nf; finish
  · rw [show 2 * (n + 1) + 1 = (2 * n + 1) + 2 from by ring,
        show r + (n + 1) + 1 = (r + n + 1) + 1 from by ring]
    step fm
    step fm
    step fm
    rw [show q + 2 = (q + 1) + 1 from by ring]
    apply stepStar_trans (ih (p + 2) (q + 1) r)
    ring_nf; finish

theorem drain_chain : ∀ n, ∀ p r,
    ⟨0, 0, p, n + 1, r + 1⟩ [fm]⊢* ⟨0, 0, p + 2 * (n + 1), 0, r + 4 + 3 * n⟩ := by
  intro n; induction' n with n ih <;> intro p r
  · step fm; step fm; step fm; ring_nf; finish
  · rw [show (n + 1) + 1 = n + 2 from by ring]
    step fm
    step fm
    step fm
    rw [show r + 4 = (r + 3) + 1 from by ring]
    apply stepStar_trans (ih (p + 2) (r + 3))
    ring_nf; finish

theorem main_transition (k e : ℕ) :
    ⟨0, 0, 2 * k + 1, 0, e + k + 2⟩ [fm]⊢⁺ ⟨0, 0, 4 * k + 5, 0, e + 3 * k + 5⟩ := by
  apply stepStar_stepPlus_stepPlus
  · rw [show (2 * k + 1 : ℕ) = 0 + (2 * k + 1) from by ring]
    exact c_to_b (2 * k + 1) (b := 0) (c := 0) (e := e + k + 2)
  rw [show (0 : ℕ) + (2 * k + 1) = 2 * k + 1 from by ring]
  rw [show e + k + 2 = (e + k + 1) + 1 from by ring]
  step fm
  step fm
  rw [show (1 : ℕ) = 0 + 1 from by ring]
  apply stepStar_trans (spiral_chain k 1 0 e)
  rw [show 1 + 2 * k + 1 = 2 * k + 2 from by ring,
      show 0 + k + 1 = k + 1 from by ring]
  step fm
  rw [show e + 2 = (e + 1) + 1 from by ring]
  apply stepStar_trans (drain_chain k (2 * k + 3) (e + 1))
  ring_nf; finish

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨0, 0, 1, 0, 2⟩) (by execute fm 1)
  apply progress_nonhalt_simple (fm := fm) (A := ℕ × ℕ)
    (fun ⟨k, e⟩ ↦ ⟨0, 0, 2 * k + 1, 0, e + k + 2⟩) ⟨0, 0⟩
  intro ⟨k, e⟩
  refine ⟨⟨2 * k + 2, e + k + 1⟩, ?_⟩
  show ⟨0, 0, 2 * k + 1, 0, e + k + 2⟩ [fm]⊢⁺ ⟨0, 0, 2 * (2 * k + 2) + 1, 0, (e + k + 1) + (2 * k + 2) + 2⟩
  rw [show 2 * (2 * k + 2) + 1 = 4 * k + 5 from by ring,
      show (e + k + 1) + (2 * k + 2) + 2 = e + 3 * k + 5 from by ring]
  exact main_transition k e

end Sz22_2003_unofficial_799
