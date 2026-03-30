import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #665: [35/6, 28/55, 121/2, 3/7, 14/11]

Vector representation:
```
-1 -1  1  1  0
 2  0 -1  1 -1
-1  0  0  0  2
 0  1  0 -1  0
 1  0  0  1 -1
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_665

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a+1, b+1, c, d, e⟩ => some ⟨a, b, c+1, d+1, e⟩
  | ⟨a, b, c+1, d, e+1⟩ => some ⟨a+2, b, c, d+1, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b, c, d, e+2⟩
  | ⟨a, b, c, d+1, e⟩ => some ⟨a, b+1, c, d, e⟩
  | ⟨a, b, c, d, e+1⟩ => some ⟨a+1, b, c, d+1, e⟩
  | _ => none

-- R4 repeated: move d to b.
theorem d_to_b : ∀ k, ⟨0, b, 0, d + k, e⟩ [fm]⊢* ⟨0, b + k, 0, d, e⟩ := by
  intro k; induction' k with k ih generalizing b d
  · exists 0
  · rw [show d + (k + 1) = (d + k) + 1 from by ring]
    step fm
    apply stepStar_trans (ih (b := b + 1) (d := d))
    ring_nf; finish

-- R3 repeated: drain a to e.
theorem r3_drain : ∀ k, ⟨a + k, 0, 0, d, e⟩ [fm]⊢* ⟨a, 0, 0, d, e + 2 * k⟩ := by
  intro k; induction' k with k ih generalizing a e
  · exists 0
  · rw [show a + (k + 1) = (a + k) + 1 from by ring]
    step fm
    apply stepStar_trans (ih (a := a) (e := e + 2))
    ring_nf; finish

-- R2 repeated: drain c when b=0.
theorem r2_drain : ∀ k, ∀ a c d e,
    ⟨a, 0, c + k, d, e + k⟩ [fm]⊢* ⟨a + 2 * k, 0, c, d + k, e⟩ := by
  intro k; induction' k with k ih <;> intro a c d e
  · exists 0
  · rw [show c + (k + 1) = (c + k) + 1 from by ring,
        show e + (k + 1) = (e + k) + 1 from by ring]
    step fm
    apply stepStar_trans (ih (a + 2) c (d + 1) e)
    ring_nf; finish

-- R2 drain starting from c=0: (a, 0, k, d, e+k) →* (a+2k, 0, 0, d+k, e).
theorem r2_drain_full (k : ℕ) : ⟨a, 0, k, d, e + k⟩ [fm]⊢* ⟨a + 2 * k, 0, 0, d + k, e⟩ := by
  have h := r2_drain k a 0 d e
  simp only [Nat.zero_add] at h
  exact h

-- The spiral phase: (0, B, c+1, d, B+c+2) →* (B+2*c+2, 0, 0, d+2*B+c+1, 1).
-- Proved by strong induction on B.
theorem spiral : ∀ B, ∀ c d, ⟨0, B, c + 1, d, B + c + 2⟩ [fm]⊢*
    ⟨B + 2 * c + 2, 0, 0, d + 2 * B + c + 1, 1⟩ := by
  intro B; induction' B using Nat.strongRecOn with B ih
  rcases B with _ | _ | B
  · -- B = 0: R2 drain (c+1) times.
    intro c d
    rw [show (0 : ℕ) + c + 2 = 1 + (c + 1) from by omega]
    have h := r2_drain_full (c + 1) (a := 0) (d := d) (e := 1)
    rw [show (0 : ℕ) + 2 * (c + 1) = 0 + 2 * c + 2 from by ring,
        show d + (c + 1) = d + 2 * 0 + c + 1 from by ring] at h
    exact h
  · -- B = 1: R2, R1, then R2 drain.
    intro c d
    rw [show (0 : ℕ) + 1 + c + 2 = c + 2 + 1 from by ring]
    step fm  -- R2
    step fm  -- R1
    rw [show c + 2 = 1 + (c + 1) from by omega]
    have h := r2_drain_full (c + 1) (a := 1) (d := d + 1 + 1) (e := 1)
    rw [show 1 + 2 * (c + 1) = 0 + 1 + 2 * c + 2 from by ring,
        show d + 1 + 1 + (c + 1) = d + 2 * (0 + 1) + c + 1 from by ring] at h
    exact h
  · -- B + 2: R2, R1, R1, then IH with B, c+1, d+3.
    intro c d
    rw [show B + 1 + 1 + c + 2 = B + (c + 1) + 2 + 1 from by ring]
    step fm  -- R2
    step fm  -- R1
    step fm  -- R1
    rw [show c + 2 = (c + 1) + 1 from by ring]
    have h := ih B (by omega) (c + 1) (d + 1 + 1 + 1)
    rw [show B + 2 * (c + 1) + 2 = B + 1 + 1 + 2 * c + 2 from by ring,
        show d + 1 + 1 + 1 + 2 * B + (c + 1) + 1 = d + 2 * (B + 1 + 1) + c + 1 from by ring] at h
    exact h

-- Full transition: (0, 0, 0, d+1, d+3) ⊢⁺ (0, 0, 0, 2*d+3, 2*d+5).
theorem main_trans : ⟨0, 0, 0, d + 1, d + 3⟩ [fm]⊢⁺ ⟨0, 0, 0, 2 * d + 3, 2 * d + 5⟩ := by
  -- Phase 1: d_to_b
  apply stepStar_stepPlus_stepPlus
  · rw [show (d + 1 : ℕ) = 0 + (d + 1) from by ring]
    exact d_to_b (d + 1) (b := 0) (d := 0) (e := d + 3)
  rw [show (0 : ℕ) + (d + 1) = d + 1 from by ring]
  -- Phase 2: R5, then R1
  step fm
  step fm
  -- Phase 3: spiral
  rw [show (1 : ℕ) = 0 + 1 from by ring,
      show d + 2 = d + 0 + 2 from by ring]
  apply stepStar_trans (spiral d 0 2)
  -- Phase 4: R3 drain
  rw [show d + 2 * 0 + 2 = 0 + (d + 2) from by ring,
      show 2 + 2 * d + 0 + 1 = 2 * d + 3 from by ring]
  apply stepStar_trans (r3_drain (d + 2) (a := 0) (d := 2 * d + 3) (e := 1))
  ring_nf; finish

-- Transition for d=0.
theorem d0_trans : ⟨0, 0, 0, 0, 2⟩ [fm]⊢⁺ ⟨0, 0, 0, 1, 3⟩ := by
  execute fm 2

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨0, 0, 0, 0, 2⟩) (by execute fm 1)
  apply progress_nonhalt_simple (fm := fm) (A := ℕ)
    (fun d ↦ ⟨0, 0, 0, d, d + 2⟩) 0
  intro d
  rcases d with _ | d
  · exact ⟨1, d0_trans⟩
  · exact ⟨2 * d + 3, by
      rw [show d + 1 + 2 = d + 3 from by ring,
          show 2 * d + 3 + 2 = 2 * d + 5 from by ring]
      exact main_trans⟩

end Sz22_2003_unofficial_665
