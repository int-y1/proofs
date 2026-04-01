import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #1281: [56/15, 21/22, 35/2, 11/7, 3/11]

Vector representation:
```
 3 -1 -1  1  0
-1  1  0  1 -1
-1  0  1  1  0
 0  0  0 -1  1
 0  1  0  0 -1
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_1281

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a, b+1, c+1, d, e⟩ => some ⟨a+3, b, c, d+1, e⟩
  | ⟨a+1, b, c, d, e+1⟩ => some ⟨a, b+1, c, d+1, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b, c+1, d+1, e⟩
  | ⟨a, b, c, d+1, e⟩ => some ⟨a, b, c, d, e+1⟩
  | ⟨a, b, c, d, e+1⟩ => some ⟨a, b+1, c, d, e⟩
  | _ => none

-- R4 repeated: transfer d to e
theorem d_to_e : ∀ k c d e, ⟨(0 : ℕ), 0, c, d + k, e⟩ [fm]⊢* ⟨(0 : ℕ), 0, c, d, e + k⟩ := by
  intro k; induction' k with k ih <;> intro c d e
  · exists 0
  · rw [show d + (k + 1) = (d + k) + 1 from by ring]
    step fm
    apply stepStar_trans (ih c d (e + 1))
    ring_nf; finish

-- R1+R2 interleaved chain: k rounds
theorem r1r2_chain : ∀ k, ∀ a c D e,
    ⟨a, 1, c + k, D, e + k⟩ [fm]⊢* ⟨a + 2 * k, 1, c, D + 2 * k, e⟩ := by
  intro k; induction' k with k ih <;> intro a c D e
  · simp; exists 0
  · rw [show c + (k + 1) = (c + k) + 1 from by ring,
        show e + (k + 1) = (e + k) + 1 from by ring]
    step fm; step fm
    apply stepStar_trans (ih (a + 2) c (D + 2) e)
    ring_nf; finish

-- R2 drain: with c=0, R2 fires repeatedly
theorem r2_drain : ∀ k, ∀ a b D e,
    ⟨a + k, b, 0, D, (e : ℕ) + k⟩ [fm]⊢* ⟨a, b + k, 0, D + k, e⟩ := by
  intro k; induction' k with k ih <;> intro a b D e
  · exists 0
  · rw [show a + (k + 1) = (a + k) + 1 from by ring,
        show e + (k + 1) = (e + k) + 1 from by ring]
    step fm
    apply stepStar_trans (ih a (b + 1) (D + 1) e)
    ring_nf; finish

-- R3+R1 chain: k rounds
theorem r3r1_chain : ∀ k, ∀ a b D,
    ⟨a + 1, b + k, 0, D, (0 : ℕ)⟩ [fm]⊢* ⟨a + 1 + 2 * k, b, 0, D + 2 * k, 0⟩ := by
  intro k; induction' k with k ih <;> intro a b D
  · simp; exists 0
  · rw [show b + (k + 1) = (b + k) + 1 from by ring]
    step fm; step fm
    apply stepStar_trans (ih (a + 2) b (D + 2))
    ring_nf; finish

-- R3 drain: transfer a to c and d
theorem r3_drain : ∀ k, ∀ c D,
    ⟨k, 0, c, D, (0 : ℕ)⟩ [fm]⊢* ⟨0, 0, c + k, D + k, 0⟩ := by
  intro k; induction' k with k ih <;> intro c D
  · exists 0
  · rw [show k + 1 = k + 1 from rfl]
    step fm
    apply stepStar_trans (ih (c + 1) (D + 1))
    ring_nf; finish

-- Main transition: (0, 0, c, c+1+g, 0) ⊢⁺ (0, 0, 2c+g+2, 4c+4g+4, 0)
-- where m + g + 1 = 2c (ensures 2c > g for ℕ arithmetic)
theorem main_trans (c g m : ℕ) (hm : m + g + 1 = 2 * c) :
    ⟨(0 : ℕ), 0, c, c + 1 + g, 0⟩ [fm]⊢⁺ ⟨(0 : ℕ), 0, 2 * c + g + 2, 4 * c + 4 * g + 4, 0⟩ := by
  -- Phase 1: R4
  have h1 : (⟨0, 0, c, c + 1 + g, 0⟩ : Q) [fm]⊢* ⟨0, 0, c, 0, c + 1 + g⟩ := by
    have := d_to_e (c + 1 + g) c 0 0; convert this using 2; ring_nf
  -- Phase 2: R5
  have h2 : (⟨0, 0, c, 0, c + 1 + g⟩ : Q) [fm]⊢ ⟨0, 1, c, 0, c + g⟩ := by
    rw [show c + 1 + g = (c + g) + 1 from by ring]; simp [fm]
  -- Phase 3: R1+R2 chain
  have h3 : (⟨0, 1, c, 0, c + g⟩ : Q) [fm]⊢* ⟨2 * c, 1, 0, 2 * c, g⟩ := by
    have := r1r2_chain c 0 0 0 g; convert this using 2; ring_nf
  -- Phase 4: R2 drain
  have h4 : (⟨2 * c, 1, 0, 2 * c, g⟩ : Q) [fm]⊢* ⟨m + 1, g + 1, 0, 2 * c + g, 0⟩ := by
    have h := r2_drain g (m + 1) 1 (2 * c) 0
    rw [show m + 1 + g = 2 * c from by omega,
        show 0 + g = g from by ring,
        show 1 + g = g + 1 from by ring] at h
    exact h
  -- Phase 5: R3+R1 chain
  have h5 : (⟨m + 1, g + 1, 0, 2 * c + g, 0⟩ : Q) [fm]⊢*
      ⟨2 * c + g + 2, 0, 0, 2 * c + 3 * g + 2, 0⟩ := by
    have h := r3r1_chain (g + 1) m 0 (2 * c + g)
    rw [show m + 1 + 2 * (g + 1) = 2 * c + g + 2 from by omega,
        show 2 * c + g + 2 * (g + 1) = 2 * c + 3 * g + 2 from by ring,
        show 0 + (g + 1) = g + 1 from by ring] at h
    exact h
  -- Phase 6: R3 drain
  have h6 : (⟨2 * c + g + 2, 0, 0, 2 * c + 3 * g + 2, 0⟩ : Q) [fm]⊢*
      ⟨0, 0, 2 * c + g + 2, 4 * c + 4 * g + 4, 0⟩ := by
    have := r3_drain (2 * c + g + 2) 0 (2 * c + 3 * g + 2); convert this using 2; ring_nf
  -- Compose: ⊢* + ⊢ + ⊢* + ⊢* + ⊢* + ⊢* = ⊢⁺
  exact stepStar_stepPlus_stepPlus h1
    (step_stepStar_stepPlus h2
      (stepStar_trans h3 (stepStar_trans h4 (stepStar_trans h5 h6))))

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨0, 0, 3, 4, 0⟩) (by execute fm 7)
  apply progress_nonhalt (fm := fm)
    (P := fun q ↦ ∃ c d, q = ⟨0, 0, c, d, 0⟩ ∧ d ≥ c + 1 ∧ 3 * c ≥ d)
  · intro q ⟨c, d, hq, hd, h3c⟩; subst hq
    have ⟨g, hg⟩ : ∃ g, d = c + 1 + g := ⟨d - c - 1, by omega⟩
    have ⟨m, hm⟩ : ∃ m, m + g + 1 = 2 * c := ⟨2 * c - g - 1, by omega⟩
    refine ⟨_, ⟨2 * c + g + 2, 4 * c + 4 * g + 4, rfl, by omega, by omega⟩, ?_⟩
    rw [hg]
    exact main_trans c g m hm
  · exact ⟨3, 4, rfl, by omega, by omega⟩

end Sz22_2003_unofficial_1281
