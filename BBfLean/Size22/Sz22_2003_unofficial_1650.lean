import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #1650: [77/15, 28/3, 9/22, 5/7, 21/2]

Vector representation:
```
 0 -1 -1  1  1
 2 -1  0  1  0
-1  2  0  0 -1
 0  0  1 -1  0
-1  1  0  1  0
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_1650

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a, b+1, c+1, d, e⟩ => some ⟨a, b, c, d+1, e+1⟩
  | ⟨a, b+1, c, d, e⟩ => some ⟨a+2, b, c, d+1, e⟩
  | ⟨a+1, b, c, d, e+1⟩ => some ⟨a, b+2, c, d, e⟩
  | ⟨a, b, c, d+1, e⟩ => some ⟨a, b, c+1, d, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b+1, c, d+1, e⟩
  | _ => none

theorem r4_chain : ∀ k a c, ⟨a, 0, c, k, 0⟩ [fm]⊢* ⟨a, 0, c + k, 0, 0⟩ := by
  intro k; induction' k with k ih <;> intro a c
  · exists 0
  · rw [show c + (k + 1) = (c + k) + 1 from by omega]
    step fm; apply stepStar_trans (ih a (c + 1)); ring_nf; finish

theorem r1r1r3_loop : ∀ k, ∀ X C D E,
    ⟨X + k, 2, C + 2 * k, D, E⟩ [fm]⊢* ⟨X, 2, C, D + 2 * k, E + k⟩ := by
  intro k; induction' k with k ih <;> intro X C D E
  · exists 0
  · rw [show X + (k + 1) = (X + k) + 1 from by omega,
        show C + 2 * (k + 1) = (C + 2 * k) + 1 + 1 from by omega]
    step fm
    rw [show C + 2 * k + 1 = (C + 2 * k) + 1 from by omega]
    step fm
    rw [show (X + k) + 1 = X + k + 1 from rfl,
        show E + 2 = (E + 1) + 1 from by omega]
    step fm
    apply stepStar_trans (ih X C (D + 2) (E + 1)); ring_nf; finish

theorem r3r2r2_tail : ∀ K, ∀ A D,
    ⟨A + 1, 0, 0, D, K + 1⟩ [fm]⊢* ⟨A + 3 * K + 4, 0, 0, D + 2 * K + 2, 0⟩ := by
  intro K; induction' K with K ih <;> intro A D
  · step fm; step fm; step fm; finish
  · rw [show (K : ℕ) + 1 + 1 = (K + 1) + 1 from by omega]
    step fm; step fm; step fm
    apply stepStar_trans (ih (A + 3) (D + 2)); ring_nf; finish

theorem main_trans (n B : ℕ) :
    ⟨n + 2 * B + 2, 0, 0, 2 * n + 2 * B + 2, 0⟩ [fm]⊢⁺
    ⟨3 * n + 4 * B + 5, 0, 0, 4 * n + 4 * B + 6, 0⟩ := by
  have phase1 : ⟨n + 2 * B + 2, 0, 0, 2 * n + 2 * B + 2, 0⟩ [fm]⊢*
      ⟨n + 2 * B + 2, 0, 2 * n + 2 * B + 2, 0, 0⟩ := by
    have h := r4_chain (2 * n + 2 * B + 2) (n + 2 * B + 2) 0; simp at h; exact h
  have phase2 : ⟨n + 2 * B + 2, 0, 2 * n + 2 * B + 2, 0, 0⟩ [fm]⊢⁺
      ⟨n + 2 * B, 2, 2 * n + 2 * B + 1, 2, 0⟩ := by
    rw [show n + 2 * B + 2 = (n + 2 * B + 1) + 1 from by omega,
        show 2 * n + 2 * B + 2 = (2 * n + 2 * B + 1) + 1 from by omega]
    step fm
    rw [show 2 * n + 2 * B + 1 = (2 * n + 2 * B) + 1 from by omega]
    step fm
    rw [show n + 2 * B + 1 = (n + 2 * B) + 1 from by omega]
    step fm; finish
  have phase3 : ⟨n + 2 * B, 2, 2 * n + 2 * B + 1, 2, 0⟩ [fm]⊢*
      ⟨B, 2, 1, 2 * n + 2 * B + 2, n + B⟩ := by
    rw [show n + 2 * B = B + (n + B) from by omega,
        show 2 * n + 2 * B + 1 = 1 + 2 * (n + B) from by omega]
    have h := r1r1r3_loop (n + B) B 1 2 0
    rw [show 2 + 2 * (n + B) = 2 * n + 2 * B + 2 from by ring,
        show 0 + (n + B) = n + B from by omega] at h
    exact h
  have phase4 : ⟨B, 2, 1, 2 * n + 2 * B + 2, n + B⟩ [fm]⊢*
      ⟨B + 2, 0, 0, 2 * n + 2 * B + 4, n + B + 1⟩ := by
    rw [show 1 = 0 + 1 from rfl]
    step fm
    step fm
    rw [show B + 2 = B + 2 from rfl]
    finish
  have phase5 : ⟨B + 2, 0, 0, 2 * n + 2 * B + 4, n + B + 1⟩ [fm]⊢*
      ⟨3 * n + 4 * B + 5, 0, 0, 4 * n + 4 * B + 6, 0⟩ := by
    rw [show B + 2 = (B + 1) + 1 from by omega,
        show n + B + 1 = (n + B) + 1 from by omega]
    apply stepStar_trans (r3r2r2_tail (n + B) (B + 1) (2 * n + 2 * B + 4))
    ring_nf; finish
  exact stepPlus_stepStar_stepPlus
    (stepPlus_stepStar_stepPlus
      (stepStar_stepPlus_stepPlus phase1 phase2)
      phase3)
    (stepStar_trans phase4 phase5)

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨2, 0, 0, 2, 0⟩) (by execute fm 2)
  apply progress_nonhalt_simple (fm := fm) (A := ℕ × ℕ)
    (fun p ↦ ⟨p.1 + 2 * p.2 + 2, 0, 0, 2 * p.1 + 2 * p.2 + 2, 0⟩) ⟨0, 0⟩
  intro ⟨n, B⟩
  refine ⟨⟨n + 1, n + 2 * B + 1⟩, ?_⟩
  show ⟨n + 2 * B + 2, 0, 0, 2 * n + 2 * B + 2, 0⟩ [fm]⊢⁺
    ⟨(n + 1) + 2 * (n + 2 * B + 1) + 2, 0, 0, 2 * (n + 1) + 2 * (n + 2 * B + 1) + 2, 0⟩
  rw [show (n + 1) + 2 * (n + 2 * B + 1) + 2 = 3 * n + 4 * B + 5 from by ring,
      show 2 * (n + 1) + 2 * (n + 2 * B + 1) + 2 = 4 * n + 4 * B + 6 from by ring]
  exact main_trans n B

end Sz22_2003_unofficial_1650
