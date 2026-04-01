import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #1192: [5/6, 49/2, 484/35, 3/11, 5/7]

Vector representation:
```
-1 -1  1  0  0
-1  0  0  2  0
 2  0 -1 -1  2
 0  1  0  0 -1
 0  0  1 -1  0
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_1192

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a+1, b+1, c, d, e⟩ => some ⟨a, b, c+1, d, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b, c, d+2, e⟩
  | ⟨a, b, c+1, d+1, e⟩ => some ⟨a+2, b, c, d, e+2⟩
  | ⟨a, b, c, d, e+1⟩ => some ⟨a, b+1, c, d, e⟩
  | ⟨a, b, c, d+1, e⟩ => some ⟨a, b, c+1, d, e⟩
  | _ => none

-- R4 repeated: move e to b.
theorem e_to_b : ∀ k, ∀ b d, ⟨(0 : ℕ), b, 0, d, e + k⟩ [fm]⊢* ⟨(0 : ℕ), b + k, 0, d, e⟩ := by
  intro k; induction' k with k ih <;> intro b d
  · exists 0
  · rw [show e + (k + 1) = (e + k) + 1 from by ring]
    step fm
    apply stepStar_trans (ih (b + 1) d)
    ring_nf; finish

-- (R3, R1, R1) chain: b decreases by 2, c increases by 1, d decreases by 1, e increases by 2 per round.
theorem r3r1r1 : ∀ K, ∀ c d e, ⟨(0 : ℕ), 2 * K, c + 1, d + K + 1, e⟩ [fm]⊢* ⟨(0 : ℕ), 0, c + 1 + K, d + 1, e + 2 * K⟩ := by
  intro K; induction' K with K ih <;> intro c d e
  · exists 0
  · rw [show 2 * (K + 1) = (2 * K + 1) + 1 from by ring,
        show d + (K + 1) + 1 = (d + K + 1) + 1 from by ring]
    step fm
    step fm
    step fm
    apply stepStar_trans (ih (c + 1) d (e + 2))
    ring_nf; finish

-- (R3, R2, R2) chain: c decreases by 1, d increases by 3, e increases by 2 per round.
theorem r3r2r2 : ∀ K, ∀ c d e, ⟨(0 : ℕ), 0, c + K, d + K, e⟩ [fm]⊢* ⟨(0 : ℕ), 0, c, d + 4 * K, e + 2 * K⟩ := by
  intro K; induction' K with K ih <;> intro c d e
  · exists 0
  · rw [show c + (K + 1) = (c + K) + 1 from by ring,
        show d + (K + 1) = (d + K) + 1 from by ring]
    step fm
    step fm
    step fm
    rw [show d + K + 4 = (d + 4) + K from by ring]
    apply stepStar_trans (ih c (d + 4) (e + 2))
    ring_nf; finish

-- Full cycle: (0, 0, 0, 2D+2, 2D) →⁺ (0, 0, 0, 4D+4, 4D+2)
theorem main_trans : ⟨(0 : ℕ), 0, 0, 2 * D + 2, 2 * D⟩ [fm]⊢⁺ ⟨(0 : ℕ), 0, 0, 4 * D + 4, 4 * D + 2⟩ := by
  -- Phase 1: e_to_b
  have phase1 : ⟨(0 : ℕ), 0, 0, 2 * D + 2, 2 * D⟩ [fm]⊢* ⟨(0 : ℕ), 2 * D, 0, 2 * D + 2, 0⟩ := by
    have h := e_to_b (e := 0) (2 * D) 0 (2 * D + 2)
    simpa using h
  -- Phase 2: R5
  have phase2 : ⟨(0 : ℕ), 2 * D, 0, 2 * D + 2, 0⟩ [fm]⊢ ⟨(0 : ℕ), 2 * D, 1, 2 * D + 1, 0⟩ := by
    simp [fm]
  -- Phase 3: r3r1r1 with K=D, c=0, d=D, e=0
  have phase3 : ⟨(0 : ℕ), 2 * D, 1, 2 * D + 1, 0⟩ [fm]⊢* ⟨(0 : ℕ), 0, D + 1, D + 1, 2 * D⟩ := by
    have h := r3r1r1 D 0 D 0
    simp only [Nat.zero_add] at h
    rw [show (2 * D + 1 : ℕ) = D + D + 1 from by omega,
        show (D + 1 : ℕ) = 1 + D from by omega] at *
    exact h
  -- Phase 4: r3r2r2 with K=D+1, c=0, d=0, e=2D
  have phase4 : ⟨(0 : ℕ), 0, D + 1, D + 1, 2 * D⟩ [fm]⊢* ⟨(0 : ℕ), 0, 0, 4 * D + 4, 4 * D + 2⟩ := by
    have h := r3r2r2 (D + 1) 0 0 (2 * D)
    simp only [Nat.zero_add] at h
    rw [show (4 * (D + 1) : ℕ) = 4 * D + 4 from by ring,
        show (2 * D + 2 * (D + 1) : ℕ) = 4 * D + 2 from by ring] at h
    exact h
  exact stepStar_stepPlus_stepPlus phase1
    (step_stepStar_stepPlus phase2 (stepStar_trans phase3 phase4))

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨0, 0, 0, 2, 0⟩)
  · execute fm 1
  apply progress_nonhalt_simple (fm := fm) (A := ℕ)
    (fun D ↦ ⟨0, 0, 0, 2 * D + 2, 2 * D⟩) 0
  intro D; exists D + D + 1
  have h := main_trans (D := D)
  -- goal: ⊢ (0,0,0,2*D+2,2*D) ⊢⁺ (0,0,0,2*(D+D+1)+2,2*(D+D+1))
  -- h:    ⊢ (0,0,0,2*D+2,2*D) ⊢⁺ (0,0,0,4*D+4,4*D+2)
  -- 2*(D+D+1)+2 = 4*D+4, 2*(D+D+1) = 4*D+2
  rw [show 2 * (D + D + 1) + 2 = 4 * D + 4 from by ring,
      show 2 * (D + D + 1) = 4 * D + 2 from by ring]
  exact h

end Sz22_2003_unofficial_1192
