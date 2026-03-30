import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #1147: [5/6, 44/35, 539/2, 3/11, 55/7]

Vector representation:
```
-1 -1  1  0  0
 2  0 -1 -1  1
-1  0  0  2  1
 0  1  0  0 -1
 0  0  1 -1  1
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_1147

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a+1, b+1, c, d, e⟩ => some ⟨a, b, c+1, d, e⟩
  | ⟨a, b, c+1, d+1, e⟩ => some ⟨a+2, b, c, d, e+1⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b, c, d+2, e+1⟩
  | ⟨a, b, c, d, e+1⟩ => some ⟨a, b+1, c, d, e⟩
  | ⟨a, b, c, d+1, e⟩ => some ⟨a, b, c+1, d, e+1⟩
  | _ => none

theorem e_to_b : ∀ k b d, ⟨0, b, 0, d, k⟩ [fm]⊢* ⟨0, b + k, 0, d, 0⟩ := by
  intro k; induction' k with k ih <;> intro b d
  · simp; exists 0
  · step fm
    apply stepStar_trans (ih (b + 1) d)
    ring_nf; finish

theorem r3_drain : ∀ k d e, ⟨k, 0, 0, d, e⟩ [fm]⊢* ⟨0, 0, 0, d + 2 * k, e + k⟩ := by
  intro k; induction' k with k ih <;> intro d e
  · exists 0
  · step fm
    apply stepStar_trans (ih (d + 2) (e + 1))
    ring_nf; finish

theorem r2_chain : ∀ k a c d e, ⟨a, 0, c + k, d + k, e⟩ [fm]⊢* ⟨a + 2 * k, 0, c, d, e + k⟩ := by
  intro k; induction' k with k ih <;> intro a c d e
  · exists 0
  · rw [show c + (k + 1) = (c + k) + 1 from by ring,
        show d + (k + 1) = (d + k) + 1 from by ring]
    step fm
    apply stepStar_trans (ih (a + 2) c d (e + 1))
    ring_nf; finish

theorem interleaved : ∀ k c d, ⟨0, 2 * k, c + 1, d + k, c + 1⟩ [fm]⊢*
    ⟨0, 0, c + k + 1, d, c + k + 1⟩ := by
  intro k; induction' k with k ih <;> intro c d
  · exists 0
  · rw [show 2 * (k + 1) = 2 * k + 1 + 1 from by ring,
        show d + (k + 1) = (d + k) + 1 from by ring]
    step fm; step fm; step fm
    apply stepStar_trans (ih (c + 1) d)
    ring_nf; finish

theorem r3r2_combined : ∀ C a e, ⟨a + 1, 0, C + 1, 0, e⟩ [fm]⊢*
    ⟨0, 0, 0, 2 * a + 3 * C + 5, e + a + 3 * C + 4⟩ := by
  intro C; induction' C using Nat.strongRecOn with C ihC; intro a e
  rcases C with _ | _ | C
  · step fm; step fm
    apply stepStar_trans (r3_drain (a + 2) 1 (e + 2))
    ring_nf; finish
  · step fm; step fm; step fm
    apply stepStar_trans (r3_drain (a + 4) 0 (e + 3))
    ring_nf; finish
  · step fm; step fm; step fm
    rw [show a + 4 = (a + 3) + 1 from by ring]
    apply stepStar_trans (ihC C (by omega) (a + 3) (e + 3))
    ring_nf; finish

-- Phases 4+5+6: from after R1×2 to final result
theorem phases456 (F g : ℕ) (hF : F ≥ 3) (hgF : g + 2 ≤ F) :
    ⟨0, 2 * F - 2, 2, F + g, 2⟩ [fm]⊢* ⟨0, 0, 0, 3 * F + 4 + g, 4 * F + 4⟩ := by
  -- Phase 4: interleaved with k=F-1, c=1, d=g+1
  rw [show 2 * F - 2 = 2 * (F - 1) from by omega,
      show (2 : ℕ) = 1 + 1 from by ring,
      show F + g = (g + 1) + (F - 1) from by omega]
  apply stepStar_trans (interleaved (F - 1) 1 (g + 1))
  -- Goal: (0, 0, 1+(F-1)+1, g+1, 1+(F-1)+1) →* target
  -- Phase 5: r2_chain with k=g+1
  have hFg : 1 + (F - 1) + 1 = F + 1 := by omega
  rw [hFg]
  have h5 : ⟨0, 0, F + 1, g + 1, F + 1⟩ [fm]⊢*
      ⟨2 * g + 2, 0, F - g, 0, F + g + 2⟩ := by
    have h5a := r2_chain (g + 1) 0 (F - g) 0 (F + 1)
    rw [show (F - g) + (g + 1) = F + 1 from by omega,
        show 0 + (g + 1) = g + 1 from by ring,
        show 0 + 2 * (g + 1) = 2 * g + 2 from by ring,
        show F + 1 + (g + 1) = F + g + 2 from by ring] at h5a
    exact h5a
  apply stepStar_trans h5
  -- Phase 6: r3r2_combined
  rw [show 2 * g + 2 = (2 * g + 1) + 1 from by ring,
      show F - g = (F - g - 1) + 1 from by omega]
  apply stepStar_trans (r3r2_combined (F - g - 1) (2 * g + 1) (F + g + 2))
  rw [show 2 * (2 * g + 1) + 3 * (F - g - 1) + 5 = 3 * F + 4 + g from by omega,
      show F + g + 2 + (2 * g + 1) + 3 * (F - g - 1) + 4 = 4 * F + 4 from by omega]
  finish

theorem main_even (F g : ℕ) (hF : F ≥ 3) (hgF : g + 2 ≤ F) :
    ⟨0, 0, 0, F + 2 + g, 2 * F⟩ [fm]⊢⁺ ⟨0, 0, 0, 3 * F + 4 + g, 4 * F + 4⟩ := by
  -- Phase 1: e_to_b
  apply stepStar_stepPlus_stepPlus (e_to_b (2 * F) 0 (F + 2 + g))
  rw [show 0 + 2 * F = 2 * F from by ring]
  -- Phase 2: R5 + R2 (produces ⊢⁺ then ⊢*)
  rw [show F + 2 + g = (F + g) + 1 + 1 from by ring]
  step fm; step fm
  -- Phase 3: R1 × 2
  rw [show 2 * F = (2 * F - 2) + 1 + 1 from by omega]
  step fm; step fm
  -- Now goal is ⊢*. Apply phases456.
  exact phases456 F g hF hgF

theorem main_e1 (d : ℕ) : ⟨0, 0, 0, d + 2, 1⟩ [fm]⊢⁺ ⟨0, 0, 0, d + 5, 6⟩ := by
  -- R4, R5, R2, R1 → (1, 0, 1, d, 2)
  step fm; step fm; step fm; step fm
  rcases d with _ | d
  · -- d = 0: R3, R2, R3, R3
    step fm; step fm; step fm; step fm; finish
  · -- d ≥ 1: (1, 0, 1, d+1, 2) → R2 → (3, 0, 0, d, 3) → R3 drain
    step fm
    -- Now goal is ⊢* from (3, 0, 0, d, 3)
    apply stepStar_trans (r3_drain 3 d 3)
    rw [show d + 2 * 3 = d + 1 + 5 from by ring,
        show 3 + 3 = 6 from by ring]
    finish

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨0, 0, 0, 5, 6⟩) (by execute fm 9)
  apply progress_nonhalt (fm := fm)
    (P := fun q ↦ ∃ D E, q = ⟨0, 0, 0, D, E⟩ ∧ D ≥ 5 ∧ E ≥ 6 ∧ Even E ∧ D ≤ E ∧ 2 * D ≥ E + 4)
  · intro c ⟨D, E, hq, hD, hE, hEven, hDE, h2D⟩; subst hq
    obtain ⟨F, rfl⟩ := hEven
    rw [show F + F = 2 * F from by ring] at *
    obtain ⟨g, rfl⟩ : ∃ g, D = F + 2 + g := ⟨D - F - 2, by omega⟩
    refine ⟨⟨0, 0, 0, 3 * F + 4 + g, 4 * F + 4⟩,
      ⟨3 * F + 4 + g, 4 * F + 4, rfl, by omega, by omega, ⟨2 * F + 2, by ring⟩, by omega, by omega⟩,
      main_even F g (by omega) (by omega)⟩
  · exact ⟨5, 6, rfl, by omega, by omega, ⟨3, by ring⟩, by omega, by omega⟩
