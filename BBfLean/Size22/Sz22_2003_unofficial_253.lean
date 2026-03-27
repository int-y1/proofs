import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #253: [14/15, 1/154, 9/2, 121/3, 50/11]

Vector representation:
```
 1 -1 -1  1  0
-1  0  0 -1 -1
-1  2  0  0  0
 0 -1  0  0  2
 1  0  2  0 -1
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_253

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a, b+1, c+1, d, e⟩ => some ⟨a+1, b, c, d+1, e⟩
  | ⟨a+1, b, c, d+1, e+1⟩ => some ⟨a, b, c, d, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b+2, c, d, e⟩
  | ⟨a, b+1, c, d, e⟩ => some ⟨a, b, c, d, e+2⟩
  | ⟨a, b, c, d, e+1⟩ => some ⟨a+1, b, c+2, d, e⟩
  | _ => none

-- R3 chain: a -> b
theorem a_to_b : ∀ k a b d, ⟨a+k, b, 0, d, 0⟩ [fm]⊢* ⟨a, b+2*k, 0, d, 0⟩ := by
  intro k; induction k with
  | zero => intro a b d; exists 0
  | succ k ih =>
    intro a b d
    rw [show a + (k + 1) = (a + k) + 1 from by ring]
    step fm
    apply stepStar_trans (ih _ _ _)
    ring_nf; finish

-- R4 chain: b -> e
theorem b_to_e : ∀ k b d e, ⟨0, b+k, 0, d, e⟩ [fm]⊢* ⟨(0 : ℕ), b, 0, d, e+2*k⟩ := by
  intro k; induction k with
  | zero => intro b d e; exists 0
  | succ k ih =>
    intro b d e
    rw [show b + (k + 1) = (b + k) + 1 from by ring]
    step fm
    apply stepStar_trans (ih _ _ _)
    ring_nf; finish

-- (R5, R2) chain: d,e -> c
theorem de_to_c : ∀ k c d e, ⟨0, 0, c, d+k, e+2*k⟩ [fm]⊢* ⟨(0 : ℕ), 0, c+2*k, d, e⟩ := by
  intro k; induction k with
  | zero => intro c d e; exists 0
  | succ k ih =>
    intro c d e
    rw [show d + (k + 1) = d + k + 1 from by ring,
        show e + 2 * (k + 1) = (e + 2 * k) + 1 + 1 from by ring]
    step fm
    step fm
    apply stepStar_trans (ih _ _ _)
    ring_nf; finish

-- Tail: (0, 0, C, 0, 4) ->* (2, 0, C, 2, 0)
theorem tail (C : ℕ) : ⟨0, 0, C, 0, 4⟩ [fm]⊢* ⟨(2 : ℕ), 0, C, 2, 0⟩ := by
  step fm
  step fm
  rw [show C + 2 = (C + 1) + 1 from by ring]
  step fm
  step fm
  step fm
  step fm
  step fm
  step fm
  rw [show C + 2 = (C + 1) + 1 from by ring]
  step fm
  step fm
  finish

-- Fold: (R3, R1, R1) chain
theorem fold : ∀ k a c d, ⟨a+1, 0, c+2*k, d, 0⟩ [fm]⊢* ⟨a+1+k, 0, c, d+2*k, 0⟩ := by
  intro k; induction k with
  | zero => intro a c d; simp; exists 0
  | succ k ih =>
    intro a c d
    rw [show c + 2 * (k + 1) = (c + 2 * k + 1) + 1 from by ring]
    step fm
    rw [show c + 2 * k + 1 + 1 = (c + 2 * k) + 1 + 1 from by ring]
    step fm
    rw [show c + 2 * k + 1 = (c + 2 * k) + 1 from by ring]
    step fm
    rw [show a + 1 + 1 = (a + 1) + 1 from by ring]
    apply stepStar_trans (ih _ _ _)
    ring_nf; finish

-- Main transition
theorem main_trans (n : ℕ) : ⟨n+2, 0, 0, 2*n+2, 0⟩ [fm]⊢⁺ ⟨2*n+4, 0, 0, 4*n+6, 0⟩ := by
  -- Phase 1: first R3 step (gives stepPlus)
  rw [show n + 2 = (n + 1) + 1 from by ring]
  apply step_stepStar_stepPlus
  · show fm ⟨(n + 1) + 1, 0, 0, 2 * n + 2, 0⟩ = some ⟨n + 1, 2, 0, 2 * n + 2, 0⟩
    simp [fm]
  -- Remaining a_to_b: (n+1, 2, 0, 2n+2, 0) ->* (0, 2n+4, 0, 2n+2, 0)
  apply stepStar_trans (c₂ := ⟨0, 2*n+4, 0, 2*n+2, 0⟩)
  · have h := a_to_b (n+1) 0 2 (2*n+2)
    simp only [Nat.zero_add] at h
    rw [show 2 + 2 * (n + 1) = 2 * n + 4 from by ring] at h
    exact h
  -- Phase 2: b_to_e
  apply stepStar_trans (c₂ := ⟨0, 0, 0, 2*n+2, 4*n+8⟩)
  · have h := b_to_e (2*n+4) 0 (2*n+2) 0
    simp only [Nat.zero_add] at h
    rw [show 2 * (2 * n + 4) = 4 * n + 8 from by ring] at h
    exact h
  -- Phase 3: de_to_c
  apply stepStar_trans (c₂ := ⟨0, 0, 4*n+4, 0, 4⟩)
  · have h := de_to_c (2*n+2) 0 0 4
    simp only [Nat.zero_add] at h
    rw [show 4 + 2 * (2 * n + 2) = 4 * n + 8 from by ring,
        show 2 * (2 * n + 2) = 4 * n + 4 from by ring] at h
    exact h
  -- Phase 4: tail
  apply stepStar_trans (c₂ := ⟨2, 0, 4*n+4, 2, 0⟩)
  · exact tail (4*n+4)
  -- Phase 5: fold
  · have h := fold (2*n+2) 1 0 2
    simp only [Nat.zero_add] at h
    rw [show (1 : ℕ) + 1 = 2 from by ring,
        show 1 + 1 + (2 * n + 2) = 2 * n + 4 from by ring,
        show 2 * (2 * n + 2) = 4 * n + 4 from by ring,
        show 2 + (4 * n + 4) = 4 * n + 6 from by ring] at h
    exact h

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨2, 0, 0, 2, 0⟩) (by execute fm 13)
  apply progress_nonhalt_simple (fm := fm) (A := ℕ)
    (fun n ↦ ⟨n+2, 0, 0, 2*n+2, 0⟩) 0
  intro n
  refine ⟨2*n+2, ?_⟩
  show ⟨n+2, 0, 0, 2*n+2, 0⟩ [fm]⊢⁺ ⟨(2*n+2)+2, 0, 0, 2*(2*n+2)+2, 0⟩
  rw [show (2 * n + 2) + 2 = 2 * n + 4 from by ring,
      show 2 * (2 * n + 2) + 2 = 4 * n + 6 from by ring]
  exact main_trans n

end Sz22_2003_unofficial_253
