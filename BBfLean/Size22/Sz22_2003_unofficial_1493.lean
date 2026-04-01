import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #1493: [7/15, 9/154, 275/7, 4/5, 7/2]

Vector representation:
```
 0 -1 -1  1  0
-1  2  0 -1 -1
 0  0  2 -1  1
 2  0 -1  0  0
-1  0  0  1  0
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_1493

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a, b+1, c+1, d, e⟩ => some ⟨a, b, c, d+1, e⟩
  | ⟨a+1, b, c, d+1, e+1⟩ => some ⟨a, b+2, c, d, e⟩
  | ⟨a, b, c, d+1, e⟩ => some ⟨a, b, c+2, d, e+1⟩
  | ⟨a, b, c+1, d, e⟩ => some ⟨a+2, b, c, d, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b, c, d+1, e⟩
  | _ => none

-- R4 chain: (a, 0, c+k, 0, e) →* (a+2*k, 0, c, 0, e)
theorem r4_chain : ∀ k a c e, ⟨a, 0, c + k, 0, e⟩ [fm]⊢* ⟨a + 2 * k, 0, c, 0, e⟩ := by
  intro k; induction' k with k ih <;> intro a c e
  · exists 0
  · rw [show c + (k + 1) = (c + k) + 1 from by ring]
    step fm
    apply stepStar_trans (ih (a + 2) c e)
    ring_nf; finish

-- R5+R2 chain: (2*k+2, b, 0, 0, k) →* (2, b+2*k, 0, 0, 0)
theorem r5r2_chain : ∀ k b, ⟨2 * k + 2, b, 0, 0, k⟩ [fm]⊢* ⟨2, b + 2 * k, 0, 0, 0⟩ := by
  intro k; induction' k with k ih <;> intro b
  · exists 0
  · rw [show 2 * (k + 1) + 2 = (2 * k + 2) + 2 from by ring]
    step fm; step fm
    apply stepStar_trans (ih (b + 2))
    ring_nf; finish

-- Bridge: (2, b+2, 0, 0, 0) →* (0, b+2, 0, 1, 0)
theorem bridge (b : ℕ) : ⟨2, b + 2, 0, 0, 0⟩ [fm]⊢* ⟨0, b + 2, 0, 1, 0⟩ := by
  apply stepStar_trans
    (step_stepStar (show fm ⟨2, b + 2, 0, 0, 0⟩ = some ⟨1, b + 2, 0, 1, 0⟩ from by simp [fm]))
  apply stepStar_trans
    (step_stepStar (show fm ⟨1, b + 2, 0, 1, 0⟩ = some ⟨1, b + 2, 2, 0, 1⟩ from by simp [fm]))
  rw [show b + 2 = (b + 1) + 1 from by ring]
  apply stepStar_trans
    (step_stepStar (show fm ⟨1, (b + 1) + 1, 2, 0, 1⟩ = some ⟨1, b + 1, 1, 1, 1⟩ from by simp [fm]))
  apply stepStar_trans
    (step_stepStar (show fm ⟨1, b + 1, 1, 1, 1⟩ = some ⟨1, b, 0, 2, 1⟩ from by simp [fm]))
  apply stepStar_trans
    (step_stepStar (show fm ⟨1, b, 0, 2, 1⟩ = some ⟨0, b + 2, 0, 1, 0⟩ from by simp [fm]))
  exists 0

-- R3+R1+R1 drain: (0, 2*(k+1), 0, d+1, e) →* (0, 0, 0, d+k+2, e+k+1)
theorem r3r1r1_drain : ∀ k d e, ⟨0, 2 * (k + 1), 0, d + 1, e⟩ [fm]⊢* ⟨0, 0, 0, d + k + 2, e + k + 1⟩ := by
  intro k; induction' k with k ih <;> intro d e
  · step fm; step fm; step fm; ring_nf; finish
  · rw [show 2 * (k + 1 + 1) = (2 * (k + 1) + 1) + 1 from by ring]
    step fm
    rw [show 2 * (k + 1) + 1 = (2 * (k + 1)) + 1 from by ring]
    step fm
    step fm
    rw [show d + 2 = (d + 1) + 1 from by ring]
    apply stepStar_trans (ih (d + 1) (e + 1))
    ring_nf; finish

-- R3 chain: (0, 0, c, d+k, e) →* (0, 0, c+2*k, d, e+k)
theorem r3_chain : ∀ k c d e, ⟨0, 0, c, d + k, e⟩ [fm]⊢* ⟨0, 0, c + 2 * k, d, e + k⟩ := by
  intro k; induction' k with k ih <;> intro c d e
  · exists 0
  · rw [show d + (k + 1) = (d + k) + 1 from by ring]
    step fm
    apply stepStar_trans (ih (c + 2) d (e + 1))
    ring_nf; finish

-- Main transition: (0, 0, c+2, 0, c+1) →⁺ (0, 0, 2*c+4, 0, 2*c+3)
theorem main_trans (c : ℕ) :
    ⟨(0 : ℕ), 0, c + 2, 0, c + 1⟩ [fm]⊢⁺ ⟨(0 : ℕ), 0, 2 * c + 4, 0, 2 * c + 3⟩ := by
  -- Phase 1: R4 chain (c+2 steps).
  have h1 : ⟨(0 : ℕ), 0, c + 2, 0, c + 1⟩ [fm]⊢⁺ ⟨2 * c + 4, 0, 0, 0, c + 1⟩ := by
    rw [show c + 2 = 0 + (c + 2) from by ring]
    step fm
    apply stepStar_trans (r4_chain (c + 1) 2 0 _)
    ring_nf; finish
  -- Phase 2: R5+R2 chain (c+1 rounds).
  have h2 : ⟨2 * c + 4, 0, 0, 0, c + 1⟩ [fm]⊢* ⟨2, 2 * c + 2, 0, 0, 0⟩ := by
    rw [show 2 * c + 4 = 2 * (c + 1) + 2 from by ring]
    apply stepStar_trans (r5r2_chain (c + 1) 0)
    ring_nf; finish
  -- Phase 3: Bridge (5 steps).
  have h3 : ⟨2, 2 * c + 2, 0, 0, 0⟩ [fm]⊢* ⟨0, 2 * c + 2, 0, 1, 0⟩ := by
    exact bridge (2 * c)
  -- Phase 4: R3+R1+R1 drain (c+1 rounds).
  have h4 : ⟨(0 : ℕ), 2 * c + 2, 0, 1, 0⟩ [fm]⊢* ⟨0, 0, 0, c + 2, c + 1⟩ := by
    rw [show 2 * c + 2 = 2 * (c + 1) from by ring,
        show (1 : ℕ) = 0 + 1 from by ring]
    apply stepStar_trans (r3r1r1_drain c 0 0)
    ring_nf; finish
  -- Phase 5: R3 chain (c+2 steps).
  have h5 : ⟨(0 : ℕ), 0, 0, c + 2, c + 1⟩ [fm]⊢* ⟨0, 0, 2 * c + 4, 0, 2 * c + 3⟩ := by
    rw [show c + 2 = 0 + (c + 2) from by ring]
    apply stepStar_trans (r3_chain (c + 2) 0 0 (c + 1))
    ring_nf; finish
  exact stepPlus_stepStar_stepPlus h1
    (stepStar_trans h2 (stepStar_trans h3 (stepStar_trans h4 h5)))

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨0, 0, 2, 0, 1⟩)
  · execute fm 2
  apply progress_nonhalt_simple (fm := fm) (A := ℕ)
    (fun c ↦ ⟨0, 0, c + 2, 0, c + 1⟩) 0
  intro c
  exact ⟨2 * c + 2, main_trans c⟩

end Sz22_2003_unofficial_1493
