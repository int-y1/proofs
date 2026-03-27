import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #227: [11/105, 1/22, 27/11, 20/3, 77/2]

Vector representation:
```
 0 -1 -1 -1  1
-1  0  0  0 -1
 0  3  0  0 -1
 2 -1  1  0  0
-1  0  0  1  1
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_227

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a, b+1, c+1, d+1, e⟩ => some ⟨a, b, c, d, e+1⟩
  | ⟨a+1, b, c, d, e+1⟩ => some ⟨a, b, c, d, e⟩
  | ⟨a, b, c, d, e+1⟩ => some ⟨a, b+3, c, d, e⟩
  | ⟨a, b+1, c, d, e⟩ => some ⟨a+2, b, c+1, d, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b, c, d+1, e+1⟩
  | _ => none

-- R1 chain: drain min(b,c,d) via rule 1
theorem r1_chain : ∀ k b c d e, ⟨0, b+k, c+k, d+k, e⟩ [fm]⊢* ⟨0, b, c, d, e+k⟩ := by
  intro k; induction k with
  | zero => intro b c d e; exists 0
  | succ k ih =>
    intro b c d e
    rw [show b + (k + 1) = (b + k) + 1 from by ring,
        show c + (k + 1) = (c + k) + 1 from by ring,
        show d + (k + 1) = (d + k) + 1 from by ring]
    step fm
    apply stepStar_trans (ih _ _ _ _)
    ring_nf; finish

-- R3 chain: convert e to b (when a=0, c=0)
theorem r3_chain : ∀ k b d e, ⟨0, b, 0, d, e+k⟩ [fm]⊢* ⟨0, b+3*k, 0, d, e⟩ := by
  intro k; induction k with
  | zero => intro b d e; exists 0
  | succ k ih =>
    intro b d e
    rw [show e + (k + 1) = (e + k) + 1 from by ring]
    step fm
    apply stepStar_trans (ih _ _ _)
    ring_nf; finish

-- R4 chain: convert b to a,c (when d=0, e=0)
theorem r4_chain : ∀ k a b c, ⟨a, b+k, c, 0, 0⟩ [fm]⊢* ⟨a+2*k, b, c+k, 0, 0⟩ := by
  intro k; induction k with
  | zero => intro a b c; exists 0
  | succ k ih =>
    intro a b c
    rw [show b + (k + 1) = (b + k) + 1 from by ring]
    step fm
    apply stepStar_trans (ih _ _ _)
    ring_nf; finish

-- R5/R2 chain: convert a to d (when b=0, e=0)
theorem r5r2_chain : ∀ k a c d, ⟨a+2*k, 0, c, d, 0⟩ [fm]⊢* ⟨a, 0, c, d+k, 0⟩ := by
  intro k; induction k with
  | zero => intro a c d; exists 0
  | succ k ih =>
    intro a c d
    rw [show a + 2 * (k + 1) = (a + 2 * k) + 1 + 1 from by ring]
    step fm; step fm
    apply stepStar_trans (ih _ _ _)
    ring_nf; finish

-- Drain: R1/R3 cycle drains c,d to 0,1, preserving b + 2c + 3e
theorem drain : ∀ c, ∀ b e, ⟨0, b+1, c, c+1, e⟩ [fm]⊢* ⟨0, b+2*c+3*e+1, 0, 1, 0⟩ := by
  intro c; induction c with
  | zero =>
    intro b e
    have h := r3_chain e (b+1) 1 0
    rw [show 0 + e = e from by ring,
        show b + 1 + 3 * e = b + 2 * 0 + 3 * e + 1 from by ring] at h
    exact h
  | succ c ih =>
    intro b e
    rw [show c + 1 + 1 = (c + 1) + 1 from rfl]
    step fm
    rcases b with _ | b
    · -- b = 0: R3 step, then IH
      step fm
      have h := ih 2 e
      rw [show 2 + 2 * c + 3 * e + 1 = 0 + 2 * (c + 1) + 3 * e + 1 from by ring] at h
      exact h
    · -- b >= 1: directly apply IH
      have h := ih b (e + 1)
      rw [show b + 2 * c + 3 * (e + 1) + 1 = (b + 1) + 2 * (c + 1) + 3 * e + 1 from by ring] at h
      exact h

-- Phase 2: from (0, 2n+3, 0, 1, 0) to (4n+3, 0, 2n+1, 0, 0)
theorem phase2 (n : ℕ) : ⟨0, 2*n+3, 0, 1, 0⟩ [fm]⊢* ⟨4*n+3, 0, 2*n+1, 0, 0⟩ := by
  -- R4: (2, 2n+2, 1, 1, 0)
  -- R1: (2, 2n+1, 0, 0, 1)
  -- R2: (1, 2n+1, 0, 0, 0)
  -- R4 x (2n+1): (4n+3, 0, 2n+1, 0, 0)
  rw [show 2 * n + 3 = (2 * n + 1) + 1 + 1 from by ring]
  step fm; step fm; step fm
  have h := r4_chain (2*n+1) 1 0 0
  rw [show 1 + 2 * (2 * n + 1) = 4 * n + 3 from by ring,
      show 0 + (2 * n + 1) = 2 * n + 1 from by ring] at h
  exact h

-- Main transition: (1, 0, n, n, 0) ->+ (1, 0, 2n+1, 2n+1, 0)
theorem main_trans (n : ℕ) : ⟨1, 0, n, n, 0⟩ [fm]⊢⁺ ⟨1, 0, 2*n+1, 2*n+1, 0⟩ := by
  -- R5: (0, 0, n, n+1, 1)
  apply step_stepStar_stepPlus
  · show fm ⟨1, 0, n, n, 0⟩ = some ⟨0, 0, n, n+1, 1⟩; simp [fm]
  -- R3: (0, 3, n, n+1, 0)
  step fm
  -- Drain: (0, 3, n, n+1, 0) ->* (0, 2n+3, 0, 1, 0)
  apply stepStar_trans (c₂ := ⟨0, 2*n+3, 0, 1, 0⟩)
  · have h := drain n 2 0
    rw [show 2 + 2 * n + 3 * 0 + 1 = 2 * n + 3 from by ring] at h
    exact h
  -- Phase 2: (0, 2n+3, 0, 1, 0) ->* (4n+3, 0, 2n+1, 0, 0)
  apply stepStar_trans (phase2 n)
  -- R5/R2 chain: (4n+3, 0, 2n+1, 0, 0) ->* (1, 0, 2n+1, 2n+1, 0)
  have h := r5r2_chain (2*n+1) 1 (2*n+1) 0
  rw [show 1 + 2 * (2 * n + 1) = 4 * n + 3 from by ring,
      show 0 + (2 * n + 1) = 2 * n + 1 from by ring] at h
  exact h

theorem nonhalt : ¬halts fm c₀ := by
  apply progress_nonhalt_simple (fm := fm) (A := ℕ) (fun n ↦ ⟨1, 0, n, n, 0⟩) 0
  intro n
  exact ⟨2*n+1, main_trans n⟩

end Sz22_2003_unofficial_227
