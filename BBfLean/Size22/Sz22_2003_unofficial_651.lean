import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #651: [35/6, 143/2, 8/55, 3/7, 15/13]

Vector representation:
```
-1 -1  1  1  0  0
-1  0  0  0  1  1
 3  0 -1  0 -1  0
 0  1  0 -1  0  0
 0  1  1  0  0 -1
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_651

def Q := ℕ × ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a+1, b+1, c, d, e, f⟩ => some ⟨a, b, c+1, d+1, e, f⟩
  | ⟨a+1, b, c, d, e, f⟩ => some ⟨a, b, c, d, e+1, f+1⟩
  | ⟨a, b, c+1, d, e+1, f⟩ => some ⟨a+3, b, c, d, e, f⟩
  | ⟨a, b, c, d+1, e, f⟩ => some ⟨a, b+1, c, d, e, f⟩
  | ⟨a, b, c, d, e, f+1⟩ => some ⟨a, b+1, c+1, d, e, f⟩
  | _ => none

-- R4 repeated: move d to b.
theorem d_to_b : ∀ k b d e f, ⟨0, b, 0, d + k, e, f⟩ [fm]⊢* ⟨0, b + k, 0, d, e, f⟩ := by
  intro k; induction' k with k ih
  · intro b d e f; exists 0
  · intro b d e f
    rw [Nat.add_succ d k]
    step fm
    apply stepStar_trans (ih (b + 1) d e f)
    ring_nf; finish

-- R3+R2x3 drain: each round consumes one c and one e, producing net +2 e and +3 f.
theorem drain : ∀ k D e f, ⟨0, 0, k, D, e + k, f⟩ [fm]⊢* ⟨0, 0, 0, D, e + 3 * k, f + 3 * k⟩ := by
  intro k; induction' k with k ih
  · intro D e f; exists 0
  · intro D e f
    rw [show e + (k + 1) = (e + k) + 1 from by ring]
    step fm
    step fm; step fm; step fm
    rw [show e + k + 1 + 1 + 1 = (e + 3) + k from by ring,
        show f + 1 + 1 + 1 = f + 3 from by ring]
    apply stepStar_trans (ih D (e + 3) (f + 3))
    ring_nf; finish

-- Process general: by strong induction on b.
-- From (3, b, c, D, e+b+c, f) reaches (0, 0, 0, D+b, e+2b+3c+3, f+2b+3c+3).
-- We universally quantify c, D, e, f inside the induction.
theorem process : ∀ b c D e f,
    ⟨3, b, c, D, e + b + c, f⟩ [fm]⊢* ⟨0, 0, 0, D + b, e + 2 * b + 3 * c + 3, f + 2 * b + 3 * c + 3⟩ := by
  intro b
  induction b using Nat.strongRecOn with
  | _ b ih =>
  intro c D e f
  match b with
  | 0 =>
    step fm; step fm; step fm
    rw [show e + 0 + c + 1 + 1 + 1 = (e + 3) + c from by ring,
        show f + 1 + 1 + 1 = f + 3 from by ring]
    apply stepStar_trans (drain c D (e + 3) (f + 3))
    ring_nf; finish
  | 1 =>
    step fm -- R1
    step fm; step fm -- R2 x 2
    rw [show e + 1 + c + 1 + 1 = (e + 2) + (c + 1) from by ring,
        show f + 1 + 1 = f + 2 from by ring]
    apply stepStar_trans (drain (c + 1) (D + 1) (e + 2) (f + 2))
    ring_nf; finish
  | 2 =>
    step fm; step fm -- R1 x 2
    step fm -- R2
    rw [show e + 2 + c + 1 = (e + 1) + (c + 2) from by ring]
    apply stepStar_trans (drain (c + 2) (D + 2) (e + 1) (f + 1))
    ring_nf; finish
  | b + 3 =>
    -- Rewrite e component to expose +1 for R3 step
    rw [show e + (b + 3) + c = (e + (b + 2) + c) + 1 from by ring]
    step fm; step fm; step fm -- R1 x 3
    -- After R1 x 3: (0, b, c+3, D+3, (e+b+2+c)+1, f)
    -- R3 fires since c+3 = (c+2)+1 >= 1 and (e+b+2+c)+1 = (e+b+2+c)+1 has +1
    step fm -- R3
    -- After R3: (3, b, c+2, D+3, e+b+2+c, f)
    show ⟨3, b, c + 1 + 1, D + 1 + 1 + 1, e + (b + 2) + c, f⟩ [fm]⊢* _
    rw [show c + 1 + 1 = c + 2 from by ring,
        show D + 1 + 1 + 1 = D + 3 from by ring,
        show e + (b + 2) + c = e + b + (c + 2) from by ring]
    apply stepStar_trans (ih b (by omega) (c + 2) (D + 3) e f)
    ring_nf; finish

-- Main transition: one full cycle from canonical state to next.
theorem main_transition (d e f : ℕ) :
    ⟨0, 0, 0, d + 1, e + d + 3, f + 1⟩ [fm]⊢⁺ ⟨0, 0, 0, d + 2, e + 2 * d + 7, f + 2 * d + 7⟩ := by
  -- Phase 1: R4 x (d+1) to move d to b
  rw [show (d + 1 : ℕ) = 0 + (d + 1) from by ring]
  apply stepStar_stepPlus_stepPlus
  · exact d_to_b (d + 1) 0 0 (e + d + 3) (f + 1)
  · simp only [Nat.zero_add]
    -- State: (0, d+1, 0, 0, e+d+3, f+1)
    -- R5: (0, d+2, 1, 0, e+d+3, f)
    rw [show (f + 1 : ℕ) = f + 1 from rfl]
    step fm
    -- R3: need 1 >= 1 and (e+d+3) >= 1. Rewrite e+d+3 = (e+d+2)+1
    rw [show e + d + 3 = (e + d + 2) + 1 from by ring]
    step fm
    -- State: (3, d+2, 0, 0, e+d+2, f)
    rw [show e + d + 2 = e + (d + 2) + 0 from by ring]
    apply stepStar_trans (process (d + 2) 0 0 e f)
    ring_nf; finish

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨0, 0, 0, 1, 4, 5⟩)
  · execute fm 10
  · apply progress_nonhalt_simple (fm := fm) (A := ℕ × ℕ × ℕ)
      (fun p ↦ ⟨0, 0, 0, p.1 + 1, p.2.1 + p.1 + 3, p.2.2 + 1⟩) ⟨0, 1, 4⟩
    intro ⟨d, e, f⟩
    refine ⟨⟨d + 1, e + d + 3, f + 2 * d + 6⟩, ?_⟩
    simp only []
    rw [show d + 1 + 1 = d + 2 from by ring,
        show e + d + 3 + (d + 1) + 3 = e + 2 * d + 7 from by ring,
        show f + 2 * d + 6 + 1 = f + 2 * d + 7 from by ring]
    exact main_transition d e f

end Sz22_2003_unofficial_651
