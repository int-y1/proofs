import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #1788: [9/10, 44/21, 49/2, 25/11, 3/7]

Vector representation:
```
-1  2 -1  0  0
 2 -1  0 -1  1
-1  0  0  2  0
 0  0  2  0 -1
 0  1  0 -1  0
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_1788

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a+1, b, c+1, d, e⟩ => some ⟨a, b+2, c, d, e⟩
  | ⟨a, b+1, c, d+1, e⟩ => some ⟨a+2, b, c, d, e+1⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b, c, d+2, e⟩
  | ⟨a, b, c, d, e+1⟩ => some ⟨a, b, c+2, d, e⟩
  | ⟨a, b, c, d+1, e⟩ => some ⟨a, b+1, c, d, e⟩
  | _ => none

theorem r3_drain : ∀ k d e, ⟨k, 0, 0, d, e⟩ [fm]⊢* ⟨0, 0, 0, d + 2 * k, e⟩ := by
  intro k; induction' k with k ih <;> intro d e
  · exists 0
  · step fm; apply stepStar_trans (ih (d + 2) e); ring_nf; finish

theorem r4_drain : ∀ k c d, ⟨0, 0, c, d, k⟩ [fm]⊢* ⟨0, 0, c + 2 * k, d, 0⟩ := by
  intro k; induction' k with k ih <;> intro c d
  · exists 0
  · step fm; apply stepStar_trans (ih (c + 2) d); ring_nf; finish

theorem phases_123 (a e : ℕ) : ⟨a + 1, 0, 0, 0, e⟩ [fm]⊢⁺ ⟨0, 1, 2 * e, 2 * a + 1, 0⟩ := by
  step fm
  apply stepStar_trans (r3_drain a 2 e)
  apply stepStar_trans (r4_drain e 0 (2 + 2 * a))
  rw [show 2 + 2 * a = (2 * a + 1) + 1 from by ring]
  exact step_stepStar (by simp [fm])

theorem r2r1r1_chain : ∀ k b c d e, ⟨0, b + 1, c + 2 * k, d + k, e⟩ [fm]⊢*
    ⟨0, b + 3 * k + 1, c, d, e + k⟩ := by
  intro k; induction' k with k ih <;> intro b c d e
  · exists 0
  · rw [show c + 2 * (k + 1) = (c + 2 * k + 1) + 1 from by ring,
        show d + (k + 1) = (d + k) + 1 from by ring]
    step fm; step fm
    rw [show c + 2 * k + 1 = (c + 2 * k) + 1 from by ring]; step fm
    rw [show b + 2 + 2 = (b + 3) + 1 from by ring]
    apply stepStar_trans (ih (b + 3) c d (e + 1)); ring_nf; finish

theorem r2_chain : ∀ k a b d e, ⟨a, b + k, 0, d + k, e⟩ [fm]⊢* ⟨a + 2 * k, b, 0, d, e + k⟩ := by
  intro k; induction' k with k ih <;> intro a b d e
  · exists 0
  · rw [show b + (k + 1) = (b + k) + 1 from by ring,
        show d + (k + 1) = (d + k) + 1 from by ring]
    step fm; apply stepStar_trans (ih (a + 2) b d (e + 1)); ring_nf; finish

theorem r3r2r2_chain : ∀ k a b e, ⟨a + 1, b + 2 * k, 0, 0, e⟩ [fm]⊢*
    ⟨a + 3 * k + 1, b, 0, 0, e + 2 * k⟩ := by
  intro k; induction' k with k ih <;> intro a b e
  · exists 0
  · rw [show b + 2 * (k + 1) = (b + 2 * k + 1) + 1 from by ring]
    step fm; step fm
    rw [show b + 2 * k + 1 = (b + 2 * k) + 1 from by ring]; step fm
    rw [show a + 2 + 2 = (a + 3) + 1 from by ring]
    apply stepStar_trans (ih (a + 3) b (e + 2)); ring_nf; finish

theorem main_trans (ha : 2 * a ≥ e) (hae : a ≤ 2 * e) :
    ⟨a + 1, 0, 0, 0, e⟩ [fm]⊢⁺ ⟨a + 4 * e + 2, 0, 0, 0, 4 * e + 1⟩ := by
  -- Introduce D = 2a+1-e and F = 2e-a to avoid ℕ subtraction
  obtain ⟨D, hD⟩ : ∃ D, e + D + 1 = 2 * a + 1 := ⟨2 * a - e, by omega⟩
  obtain ⟨F, hF⟩ : ∃ F, a + F = 2 * e := ⟨2 * e - a, by omega⟩
  -- So e = 2a-D, a = 2e-F. And D+1 = 2a+1-e, F = 2e-a.
  -- D+F+1 = (2a+1-e-1) + (2e-a) = a. Hmm no: D = 2a-e, F = 2e-a. D+F = a+e-e = a? No.
  -- D = 2a-e, D+1 = 2a+1-e. F = 2e-a. D+1+F = 2a+1-e+2e-a = a+1. So D+F = a. Also e = 2a-D, from D+1 = 2a+1-e.
  -- Phases 1-3
  apply stepPlus_stepStar_stepPlus (phases_123 a e)
  -- at (0, 1, 2e, 2a+1, 0)
  -- Phase 4: R2-R1-R1 x e: (0, 1, 2e, D+1+e, 0) where D+1 = 2a+1-e
  rw [show 2 * a + 1 = (D + 1) + e from by omega]
  rw [show (1 : ℕ) = 0 + 1 from by ring,
      show 2 * e = 0 + 2 * e from by ring]
  apply stepStar_trans (r2r1r1_chain e 0 0 (D + 1) 0)
  -- at (0, 3e+1, 0, D+1, e)
  simp only [Nat.zero_add]
  -- Phase 5: R2 x (D+1)
  have h5 := r2_chain (D + 1) 0 (2 * F) 0 e
  simp only [Nat.zero_add] at h5
  rw [show 3 * e + 1 = 2 * F + (D + 1) from by omega]
  apply stepStar_trans h5
  -- at (2*(D+1), 2F, 0, 0, e+(D+1))
  rw [show 2 * (D + 1) = (2 * D + 1) + 1 from by omega,
      show e + (D + 1) = 2 * a + 1 from by omega,
      show 2 * F = 0 + 2 * F from by ring]
  -- Phase 6: R3-R2-R2 x F
  apply stepStar_trans (r3r2r2_chain F (2 * D + 1) 0 (2 * a + 1))
  rw [show 2 * D + 1 + 3 * F + 1 = a + 4 * e + 2 from by omega,
      show 2 * a + 1 + 2 * F = 4 * e + 1 from by omega]
  finish

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨1, 0, 0, 0, 0⟩) (by execute fm 0)
  apply progress_nonhalt (fm := fm)
    (P := fun q ↦ ∃ a e, q = ⟨a + 1, 0, 0, 0, e⟩ ∧ 2 * a ≥ e ∧ a ≤ 2 * e)
  · intro c ⟨a, e, hq, ha, hae⟩; subst hq
    exact ⟨⟨a + 4 * e + 2, 0, 0, 0, 4 * e + 1⟩,
      ⟨a + 4 * e + 1, 4 * e + 1, by ring_nf, by omega, by omega⟩,
      main_trans ha hae⟩
  · exact ⟨0, 0, rfl, by omega, by omega⟩
