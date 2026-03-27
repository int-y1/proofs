import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #182: [1/6, 125/3, 3/385, 28/5, 33/2]

Vector representation:
```
-1 -1  0  0  0
 0 -1  3  0  0
 0  1 -1 -1 -1
 2  0 -1  1  0
-1  1  0  0  1
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_182

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a+1, b+1, c, d, e⟩ => some ⟨a, b, c, d, e⟩
  | ⟨a, b+1, c, d, e⟩ => some ⟨a, b, c+3, d, e⟩
  | ⟨a, b, c+1, d+1, e+1⟩ => some ⟨a, b+1, c, d, e⟩
  | ⟨a, b, c+1, d, e⟩ => some ⟨a+2, b, c, d+1, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b+1, c, d, e+1⟩
  | _ => none

-- R3,R2 loop: (0, 0, c+1, d+k, e+k) ->* (0, 0, c+1+2k, d, e)
theorem r3r2_loop : ∀ k c d e,
    ⟨0, 0, c + 1, d + k, e + k⟩ [fm]⊢* ⟨(0 : ℕ), 0, c + 1 + 2 * k, d, e⟩ := by
  intro k; induction k with
  | zero => intro c d e; simp; exists 0
  | succ k ih =>
    intro c d e
    rw [show d + (k + 1) = (d + k) + 1 from by ring,
        show e + (k + 1) = (e + k) + 1 from by ring]
    step fm
    step fm
    apply stepStar_trans (ih _ _ _)
    ring_nf; finish

-- R4 loop: (a, 0, c+k, d, 0) ->* (a+2k, 0, c, d+k, 0)
theorem r4_loop : ∀ k a c d,
    ⟨a, 0, c + k, d, 0⟩ [fm]⊢* ⟨a + 2 * k, (0 : ℕ), c, d + k, 0⟩ := by
  intro k; induction k with
  | zero => intro a c d; simp; exists 0
  | succ k ih =>
    intro a c d
    rw [show c + (k + 1) = (c + k) + 1 from by ring]
    step fm
    apply stepStar_trans (ih _ _ _)
    ring_nf; finish

-- Drain: (a+2k, 0, 0, d, e) ->* (a, 0, 0, d, e+k) via R5,R1 pairs
theorem drain : ∀ k a d e,
    ⟨a + 2 * k, 0, 0, d, e⟩ [fm]⊢* ⟨a, (0 : ℕ), 0, d, e + k⟩ := by
  intro k; induction k with
  | zero => intro a d e; simp; exists 0
  | succ k ih =>
    intro a d e
    rw [show a + 2 * (k + 1) = (a + 2 * k) + 1 + 1 from by ring]
    step fm
    step fm
    apply stepStar_trans (ih _ _ _)
    ring_nf; finish

-- Main transition: (1, 0, 0, d+1, d+1) ⊢⁺ (1, 0, 0, 2d+3, 2d+3)
theorem main_trans (d : ℕ) :
    ⟨1, 0, 0, d + 1, d + 1⟩ [fm]⊢⁺ ⟨1, (0 : ℕ), 0, 2 * d + 3, 2 * d + 3⟩ := by
  -- Phase 1: R5: (1,0,0,d+1,d+1) -> (0,1,0,d+1,d+2)
  apply step_stepStar_stepPlus (c₂ := ⟨0, 1, 0, d + 1, d + 2⟩)
  · rfl
  -- Phase 2: R2: (0,1,0,d+1,d+2) -> (0,0,3,d+1,d+2)
  apply stepStar_trans (c₂ := ⟨0, 0, 3, d + 1, d + 2⟩)
  · step fm; finish
  -- Phase 3: R3,R2 loop (d+1 iterations): (0,0,3,d+1,d+2) -> (0,0,2d+5,0,1)
  apply stepStar_trans (c₂ := ⟨0, 0, 2 * d + 5, 0, 1⟩)
  · rw [show (3 : ℕ) = 2 + 1 from by ring,
        show d + 2 = 1 + (d + 1) from by ring]
    have h := r3r2_loop (d + 1) 2 0 1
    simp only [Nat.zero_add] at h
    rw [show 2 + 1 + 2 * (d + 1) = 2 * d + 5 from by ring] at h
    exact h
  -- Phase 4: R4: (0,0,2d+5,0,1) -> (2,0,2d+4,1,1)
  apply stepStar_trans (c₂ := ⟨2, 0, 2 * d + 4, 1, 1⟩)
  · rw [show 2 * d + 5 = (2 * d + 4) + 1 from by ring]
    step fm; finish
  -- Phase 5: R3: (2,0,2d+4,1,1) -> (2,1,2d+3,0,0)
  apply stepStar_trans (c₂ := ⟨2, 1, 2 * d + 3, 0, 0⟩)
  · rw [show 2 * d + 4 = (2 * d + 3) + 1 from by ring,
        show (1 : ℕ) = 0 + 1 from by ring]
    step fm; finish
  -- Phase 6: R1: (2,1,2d+3,0,0) -> (1,0,2d+3,0,0)
  apply stepStar_trans (c₂ := ⟨1, 0, 2 * d + 3, 0, 0⟩)
  · rw [show (2 : ℕ) = 1 + 1 from by ring,
        show (1 : ℕ) = 0 + 1 from by ring]
    step fm; finish
  -- Phase 7: R4 loop (2d+3 times): (1,0,2d+3,0,0) -> (4d+7,0,0,2d+3,0)
  apply stepStar_trans (c₂ := ⟨4 * d + 7, 0, 0, 2 * d + 3, 0⟩)
  · have h := r4_loop (2 * d + 3) 1 0 0
    simp only [Nat.zero_add] at h
    rw [show 1 + 2 * (2 * d + 3) = 4 * d + 7 from by ring] at h
    exact h
  -- Phase 8: Drain (2d+3 pairs): (4d+7,0,0,2d+3,0) -> (1,0,0,2d+3,2d+3)
  · rw [show 4 * d + 7 = 1 + 2 * (2 * d + 3) from by ring]
    have h := drain (2 * d + 3) 1 (2 * d + 3) 0
    simp only [Nat.zero_add] at h
    exact h

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨1, 0, 0, 1, 1⟩) (by execute fm 8)
  apply progress_nonhalt (fm := fm)
    (P := fun c ↦ ∃ d : ℕ, c = ⟨1, 0, 0, d + 1, d + 1⟩)
  · intro c ⟨d, hc⟩
    refine ⟨⟨1, 0, 0, 2 * d + 3, 2 * d + 3⟩, ⟨2 * d + 2, ?_⟩, ?_⟩
    · ring_nf
    · rw [hc]; exact main_trans d
  · exact ⟨0, by ring_nf⟩

end Sz22_2003_unofficial_182
