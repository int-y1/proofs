import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #1005: [4/15, 7/3, 3993/2, 5/847, 3/11]

Vector representation:
```
 2 -1 -1  0  0
 0 -1  0  1  0
-1  1  0  0  3
 0  0  1 -1 -2
 0  1  0  0 -1
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_1005

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a, b+1, c+1, d, e⟩ => some ⟨a+2, b, c, d, e⟩
  | ⟨a, b+1, c, d, e⟩ => some ⟨a, b, c, d+1, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b+1, c, d, e+3⟩
  | ⟨a, b, c, d+1, e+2⟩ => some ⟨a, b, c+1, d, e⟩
  | ⟨a, b, c, d, e+1⟩ => some ⟨a, b+1, c, d, e⟩
  | _ => none

theorem r3r2_chain : ∀ k, ∀ d e,
    ⟨k, 0, 0, d, e⟩ [fm]⊢* ⟨0, 0, 0, d + k, e + 3 * k⟩ := by
  intro k; induction' k with k ih <;> intro d e
  · ring_nf; finish
  · rw [show d + (k + 1) = (d + 1) + k from by ring,
        show e + 3 * (k + 1) = (e + 3) + 3 * k from by ring]
    step fm; step fm
    apply stepStar_trans (ih (d + 1) (e + 3))
    ring_nf; finish

theorem r4_chain : ∀ k, ∀ c e,
    ⟨0, 0, c, k, e + 2 * k⟩ [fm]⊢* ⟨0, 0, c + k, 0, e⟩ := by
  intro k; induction' k with k ih <;> intro c e
  · ring_nf; finish
  · rw [show e + 2 * (k + 1) = e + 2 * k + 2 from by ring]
    step fm
    apply stepStar_trans (ih (c + 1) e)
    ring_nf; finish

theorem r3r1_chain : ∀ c, ∀ k e,
    ⟨k + 2, 0, c, 0, e⟩ [fm]⊢* ⟨k + c + 2, 0, 0, 0, e + 3 * c⟩ := by
  intro c; induction' c with c ih <;> intro k e
  · ring_nf; finish
  · rw [show k + (c + 1) + 2 = (k + 1) + c + 2 from by ring,
        show e + 3 * (c + 1) = (e + 3) + 3 * c from by ring]
    step fm; step fm
    exact ih (k + 1) (e + 3)

theorem main_trans (n : ℕ) :
    ⟨n + 2, 0, 0, 0, 2 * n * (n + 1)⟩ [fm]⊢⁺
    ⟨n + 3, 0, 0, 0, 2 * (n + 1) * (n + 2)⟩ := by
  -- Phase 1: R3R2 chain draining a into d
  have h1 : ⟨n + 2, 0, 0, 0, 2 * n * (n + 1)⟩ [fm]⊢*
      ⟨0, 0, 0, n + 2, 2 * n * (n + 1) + 3 * (n + 2)⟩ := by
    have := r3r2_chain (n + 2) 0 (2 * n * (n + 1))
    rw [show 0 + (n + 2) = n + 2 from by ring] at this; exact this
  -- Phase 2: R4 chain draining d into c
  have h2 : ⟨0, 0, 0, n + 2, 2 * n * (n + 1) + 3 * (n + 2)⟩ [fm]⊢*
      ⟨0, 0, n + 2, 0, 2 * n * (n + 1) + (n + 2)⟩ := by
    have := r4_chain (n + 2) 0 (2 * n * (n + 1) + (n + 2))
    rw [show 0 + (n + 2) = n + 2 from by ring,
        show 2 * n * (n + 1) + (n + 2) + 2 * (n + 2) = 2 * n * (n + 1) + 3 * (n + 2) from by ring]
      at this; exact this
  -- Phase 3: R5 then R1
  have h3 : ⟨0, 0, n + 2, 0, 2 * n * (n + 1) + (n + 2)⟩ [fm]⊢⁺
      ⟨2, 0, n + 1, 0, 2 * n * (n + 1) + n + 1⟩ := by
    rw [show n + 2 = (n + 1) + 1 from by ring,
        show 2 * n * (n + 1) + (n + 2) = (2 * n * (n + 1) + n + 1) + 1 from by ring]
    step fm; step fm; finish
  -- Phase 4: R3R1 chain consuming c
  have h4 : ⟨2, 0, n + 1, 0, 2 * n * (n + 1) + n + 1⟩ [fm]⊢*
      ⟨n + 3, 0, 0, 0, 2 * (n + 1) * (n + 2)⟩ := by
    have := r3r1_chain (n + 1) 0 (2 * n * (n + 1) + n + 1)
    rw [show 0 + 2 = 2 from by ring,
        show 0 + (n + 1) + 2 = n + 3 from by ring,
        show 2 * n * (n + 1) + n + 1 + 3 * (n + 1) = 2 * (n + 1) * (n + 2) from by ring]
      at this; exact this
  exact stepStar_stepPlus_stepPlus h1
    (stepStar_stepPlus_stepPlus h2
      (stepPlus_stepStar_stepPlus h3 h4))

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨2, 0, 0, 0, 0⟩) (by execute fm 5)
  apply progress_nonhalt_simple (fm := fm) (A := ℕ)
    (fun n ↦ ⟨n + 2, 0, 0, 0, 2 * n * (n + 1)⟩) 0
  intro n; exact ⟨n + 1, main_trans n⟩
