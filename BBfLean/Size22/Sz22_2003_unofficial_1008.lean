import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #1008: [4/15, 77/3, 147/2, 5/539, 3/7]

Vector representation:
```
 2 -1 -1  0  0
 0 -1  0  1  1
-1  1  0  2  0
 0  0  1 -2 -1
 0  1  0 -1  0
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_1008

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a, b+1, c+1, d, e⟩ => some ⟨a+2, b, c, d, e⟩
  | ⟨a, b+1, c, d, e⟩ => some ⟨a, b, c, d+1, e+1⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b+1, c, d+2, e⟩
  | ⟨a, b, c, d+2, e+1⟩ => some ⟨a, b, c+1, d, e⟩
  | ⟨a, b, c, d+1, e⟩ => some ⟨a, b+1, c, d, e⟩
  | _ => none

theorem r3r2_chain : ∀ k, ∀ a d e,
    ⟨a + k, 0, 0, d, e⟩ [fm]⊢* ⟨a, 0, 0, d + 3 * k, e + k⟩ := by
  intro k; induction' k with k ih <;> intro a d e
  · ring_nf; finish
  · rw [show a + (k + 1) = (a + k) + 1 from by ring]
    step fm; step fm
    apply stepStar_trans (ih a (d + 2 + 1) (e + 1))
    ring_nf; finish

theorem r4_chain : ∀ k, ∀ c d,
    ⟨0, 0, c, d + 2 * k, k⟩ [fm]⊢* ⟨0, 0, c + k, d, 0⟩ := by
  intro k; induction' k with k ih <;> intro c d
  · ring_nf; finish
  · rw [show d + 2 * (k + 1) = (d + 2 * k) + 2 from by ring,
        show (k : ℕ) + 1 = k + 1 from rfl]
    step fm
    apply stepStar_trans (ih (c + 1) d)
    ring_nf; finish

theorem r3r1_chain : ∀ k, ∀ a c d,
    ⟨a + 1, 0, c + k, d, 0⟩ [fm]⊢* ⟨a + k + 1, 0, c, d + 2 * k, 0⟩ := by
  intro k; induction' k with k ih <;> intro a c d
  · ring_nf; finish
  · rw [show c + (k + 1) = (c + k) + 1 from by ring]
    step fm; step fm
    apply stepStar_trans (ih (a + 1) c (d + 2))
    ring_nf; finish

theorem main_trans (n d : ℕ) :
    ⟨n + 2, 0, 0, d, 0⟩ [fm]⊢⁺ ⟨n + 3, 0, 0, d + 3 * (n + 1), 0⟩ := by
  -- Phase 1: R3R2 chain (n+2 rounds)
  have h1 : ⟨n + 2, 0, 0, d, 0⟩ [fm]⊢* ⟨0, 0, 0, d + 3 * (n + 2), n + 2⟩ := by
    have := r3r2_chain (n + 2) 0 d 0
    rw [show 0 + (n + 2) = n + 2 from by ring] at this; exact this
  -- Phase 2: R4 chain (n+2 rounds)
  have h2 : ⟨0, 0, 0, d + 3 * (n + 2), n + 2⟩ [fm]⊢*
      ⟨0, 0, n + 2, d + n + 2, 0⟩ := by
    have := r4_chain (n + 2) 0 (d + n + 2)
    rw [show d + n + 2 + 2 * (n + 2) = d + 3 * (n + 2) from by ring,
        show 0 + (n + 2) = n + 2 from by ring] at this; exact this
  -- Phase 3: R5R1 step
  have h3 : ⟨0, 0, n + 2, d + n + 2, 0⟩ [fm]⊢⁺ ⟨2, 0, n + 1, d + n + 1, 0⟩ := by
    rw [show n + 2 = (n + 1) + 1 from by ring,
        show d + n + 2 = (d + n + 1) + 1 from by ring]
    step fm; step fm; finish
  -- Phase 4: R3R1 chain (n+1 rounds)
  have h4 : ⟨2, 0, n + 1, d + n + 1, 0⟩ [fm]⊢* ⟨n + 3, 0, 0, d + 3 * (n + 1), 0⟩ := by
    rw [show n + 1 = 0 + (n + 1) from by ring]
    apply stepStar_trans (r3r1_chain (n + 1) 1 0 (d + n + 1))
    ring_nf; finish
  exact stepStar_stepPlus_stepPlus h1
    (stepStar_stepPlus_stepPlus h2
      (stepPlus_stepStar_stepPlus h3 h4))

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨2, 0, 0, 0, 0⟩) (by execute fm 5)
  apply progress_nonhalt_simple (fm := fm) (A := ℕ × ℕ)
    (fun ⟨n, d⟩ ↦ ⟨n + 2, 0, 0, d, 0⟩) ⟨0, 0⟩
  intro ⟨n, d⟩
  exact ⟨⟨n + 1, d + 3 * (n + 1)⟩, main_trans n d⟩
