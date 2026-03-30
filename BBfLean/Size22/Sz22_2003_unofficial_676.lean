import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #676: [35/6, 3/385, 4/5, 121/2, 15/11]

Vector representation:
```
-1 -1  1  1  0
 0  1 -1 -1 -1
 2  0 -1  0  0
-1  0  0  0  2
 0  1  1  0 -1
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_676

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a+1, b+1, c, d, e⟩ => some ⟨a, b, c+1, d+1, e⟩
  | ⟨a, b, c+1, d+1, e+1⟩ => some ⟨a, b+1, c, d, e⟩
  | ⟨a, b, c+1, d, e⟩ => some ⟨a+2, b, c, d, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b, c, d, e+2⟩
  | ⟨a, b, c, d, e+1⟩ => some ⟨a, b+1, c+1, d, e⟩
  | _ => none

-- R4 chain: (a+k, 0, 0, d, e) →* (a, 0, 0, d, e+2*k)
theorem r4_chain : ∀ k, ⟨a + k, 0, 0, d, e⟩ [fm]⊢* ⟨a, 0, 0, d, e + 2 * k⟩ := by
  intro k; induction' k with k ih generalizing a e
  · ring_nf; finish
  · rw [show a + (k + 1) = (a + k) + 1 from by ring]
    step fm
    apply stepStar_trans (ih (a := a) (e := e + 2))
    ring_nf; finish

-- R5/R2 chain: (0, b, 0, d+k, e+2*k) →* (0, b+2*k, 0, d, e)
theorem r5r2_chain : ∀ k, ∀ b, ⟨0, b, 0, d + k, e + 2 * k⟩ [fm]⊢* ⟨0, b + 2 * k, 0, d, e⟩ := by
  intro k; induction' k with k ih <;> intro b
  · ring_nf; finish
  · rw [show d + (k + 1) = (d + k) + 1 from by ring,
        show e + 2 * (k + 1) = (e + 2 * k) + 2 from by ring]
    step fm
    step fm
    apply stepStar_trans (ih (b := b + 2))
    ring_nf; finish

-- R3 chain: (a, 0, k, d, 0) →* (a+2*k, 0, 0, d, 0)
theorem r3_chain : ∀ k, ⟨a, 0, k, d, 0⟩ [fm]⊢* ⟨a + 2 * k, 0, 0, d, 0⟩ := by
  intro k; induction' k with k ih generalizing a
  · ring_nf; finish
  · rw [show (k : ℕ) + 1 = k + 1 from rfl]
    step fm
    apply stepStar_trans (ih (a := a + 2))
    ring_nf; finish

-- R3/R1/R1 chain: (0, 2*k, c+1, d, 0) →* (0, 0, c+k+1, d+2*k, 0)
theorem r3r1r1_chain : ∀ k, ∀ c d, ⟨0, 2 * k, c + 1, d, 0⟩ [fm]⊢* ⟨0, 0, c + k + 1, d + 2 * k, 0⟩ := by
  intro k; induction' k with k ih <;> intro c d
  · ring_nf; finish
  · rw [show 2 * (k + 1) = (2 * k) + 2 from by ring]
    step fm; step fm; step fm
    apply stepStar_trans (ih (c := c + 1) (d := d + 2))
    ring_nf; finish

-- Full cycle: (d+2, 0, 0, d+1, 0) ⊢⁺ (2*d+4, 0, 0, 2*d+3, 0)
theorem main_trans (d : ℕ) : ⟨d + 2, 0, 0, d + 1, 0⟩ [fm]⊢⁺ ⟨2 * d + 4, 0, 0, 2 * d + 3, 0⟩ := by
  -- Phase A: R4 chain
  have hA : ⟨d + 2, 0, 0, d + 1, 0⟩ [fm]⊢* ⟨0, 0, 0, d + 1, 2 * d + 4⟩ := by
    have := r4_chain (d + 2) (a := 0) (d := d + 1) (e := 0)
    rw [show 0 + (d + 2) = d + 2 from by ring,
        show 0 + 2 * (d + 2) = 2 * d + 4 from by ring] at this
    exact this
  -- Phase B: R5/R2 chain
  have hB : ⟨0, 0, 0, d + 1, 2 * d + 4⟩ [fm]⊢* ⟨0, 2 * d + 2, 0, 0, 2⟩ := by
    have := r5r2_chain (d + 1) (b := 0) (d := 0) (e := 2)
    rw [show 0 + (d + 1) = d + 1 from by ring,
        show 2 + 2 * (d + 1) = 2 * d + 4 from by ring,
        show 0 + 2 * (d + 1) = 2 * d + 2 from by ring] at this
    exact this
  -- Phase C: 5 steps (R5, R3, R1, R1, R2)
  have hC : ⟨0, 2 * d + 2, 0, 0, 2⟩ [fm]⊢* ⟨0, 2 * d + 2, 1, 1, 0⟩ := by
    step fm; step fm; step fm; step fm; step fm
    ring_nf; finish
  -- Phase D: R3/R1/R1 chain
  have hD : ⟨0, 2 * d + 2, 1, 1, 0⟩ [fm]⊢* ⟨0, 0, d + 2, 2 * d + 3, 0⟩ := by
    have := r3r1r1_chain (d + 1) (c := 0) (d := 1)
    rw [show 0 + 1 = 1 from by ring,
        show 2 * (d + 1) = 2 * d + 2 from by ring,
        show 0 + (d + 1) + 1 = d + 2 from by ring,
        show 1 + (2 * d + 2) = 2 * d + 3 from by ring] at this
    exact this
  -- Phase E: R3 chain
  have hE : ⟨0, 0, d + 2, 2 * d + 3, 0⟩ [fm]⊢* ⟨2 * d + 4, 0, 0, 2 * d + 3, 0⟩ := by
    have := r3_chain (d + 2) (a := 0) (d := 2 * d + 3)
    rw [show 0 + 2 * (d + 2) = 2 * d + 4 from by ring] at this
    exact this
  -- Compose: get ⊢⁺ via the last phase having different start/end
  apply stepStar_stepPlus_stepPlus (stepStar_trans hA (stepStar_trans hB (stepStar_trans hC hD)))
  exact stepStar_stepPlus hE (by intro h; simp [Q] at h)

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨2, 0, 0, 1, 0⟩)
  · execute fm 7
  apply progress_nonhalt_simple (fm := fm) (A := ℕ)
    (fun d ↦ ⟨d + 2, 0, 0, d + 1, 0⟩) 0
  intro d; exact ⟨2 * d + 2, main_trans d⟩

end Sz22_2003_unofficial_676
