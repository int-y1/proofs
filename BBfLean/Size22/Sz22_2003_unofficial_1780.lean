import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #1780: [9/10, 343/2, 22/21, 5/11, 9/7]

Vector representation:
```
-1  2 -1  0  0
-1  0  0  3  0
 1 -1  0 -1  1
 0  0  1  0 -1
 0  2  0 -1  0
```

This Fractran program doesn't halt.

Canonical form: `(0, 0, 0, E+F+2, E)` parameterized by `(E, F) : ℕ × ℕ`.
Recurrence: `(E, F) → (2E+2, F+1)`.

Phases: R4 chain (e→c), R5, R3R1 chain (drain c), R3R2 chain (drain b).

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_1780

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a+1, b, c+1, d, e⟩ => some ⟨a, b+2, c, d, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b, c, d+3, e⟩
  | ⟨a, b+1, c, d+1, e⟩ => some ⟨a+1, b, c, d, e+1⟩
  | ⟨a, b, c, d, e+1⟩ => some ⟨a, b, c+1, d, e⟩
  | ⟨a, b, c, d+1, e⟩ => some ⟨a, b+2, c, d, e⟩
  | _ => none

theorem r4_chain : ∀ k, ∀ c d, ⟨(0:ℕ), 0, c, d, k⟩ [fm]⊢* ⟨0, 0, c + k, d, 0⟩ := by
  intro k; induction' k with k ih <;> intro c d
  · exists 0
  · step fm
    apply stepStar_trans (ih (c + 1) d)
    ring_nf; finish

theorem r3r1_chain : ∀ k, ∀ B D G, ⟨(0:ℕ), B + 1, k, D + k, G⟩ [fm]⊢* ⟨0, B + k + 1, 0, D, G + k⟩ := by
  intro k; induction' k with k ih <;> intro B D G
  · exists 0
  · rw [show D + (k + 1) = (D + k) + 1 from by ring]
    step fm
    step fm
    rw [show B + 2 = (B + 1) + 1 from by ring]
    apply stepStar_trans (ih (B + 1) D (G + 1))
    ring_nf; finish

theorem r3r2_chain : ∀ k, ∀ D e, ⟨(0:ℕ), k, 0, D + 1, e⟩ [fm]⊢* ⟨0, 0, 0, D + 2 * k + 1, e + k⟩ := by
  intro k; induction' k with k ih <;> intro D e
  · exists 0
  · step fm
    step fm
    apply stepStar_trans (ih (D + 2) (e + 1))
    ring_nf; finish

theorem phase1 : ∀ E F, ⟨(0:ℕ), 0, 0, E + F + 2, E⟩ [fm]⊢* ⟨0, 2, E, E + F + 1, 0⟩ := by
  intro E F
  apply stepStar_trans (r4_chain E 0 (E + F + 2))
  rw [show (0:ℕ) + E = E from by ring,
      show E + F + 2 = (E + F + 1) + 1 from by ring]
  step fm; finish

theorem phase2 : ∀ E F, ⟨(0:ℕ), 2, E, E + F + 1, 0⟩ [fm]⊢* ⟨0, E + 2, 0, F + 1, E⟩ := by
  intro E F
  rw [show (2:ℕ) = 1 + 1 from by ring,
      show E + F + 1 = (F + 1) + E from by ring]
  apply stepStar_trans (r3r1_chain E 1 (F + 1) 0)
  ring_nf; finish

theorem phase3 : ∀ E F, ⟨(0:ℕ), E + 2, 0, F + 1, E⟩ [fm]⊢* ⟨0, 0, 0, 2 * E + F + 5, 2 * E + 2⟩ := by
  intro E F
  apply stepStar_trans (r3r2_chain (E + 2) F E)
  ring_nf; finish

theorem main_trans : ∀ E F, ⟨(0:ℕ), 0, 0, E + F + 2, E⟩ [fm]⊢⁺ ⟨0, 0, 0, 2 * E + F + 5, 2 * E + 2⟩ := by
  intro E F
  apply stepStar_stepPlus
  · apply stepStar_trans (phase1 E F)
    apply stepStar_trans (phase2 E F)
    exact phase3 E F
  · intro h
    simp [Q] at h
    omega

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨0, 0, 0, 3, 0⟩)
  · execute fm 1
  apply progress_nonhalt_simple (fm := fm) (A := ℕ × ℕ)
    (fun ⟨E, F⟩ ↦ ⟨0, 0, 0, E + F + 2, E⟩) ⟨0, 1⟩
  intro ⟨E, F⟩
  refine ⟨⟨2 * E + 2, F + 1⟩, ?_⟩
  show ⟨(0:ℕ), 0, 0, E + F + 2, E⟩ [fm]⊢⁺ ⟨0, 0, 0, (2 * E + 2) + (F + 1) + 2, 2 * E + 2⟩
  rw [show (2 * E + 2) + (F + 1) + 2 = 2 * E + F + 5 from by ring]
  exact main_trans E F
