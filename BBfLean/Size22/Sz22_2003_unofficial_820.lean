import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #820: [35/6, 8/55, 121/2, 3/7, 15/11]

Vector representation:
```
-1 -1  1  1  0
 3  0 -1  0 -1
-1  0  0  0  2
 0  1  0 -1  0
 0  1  1  0 -1
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_820

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a+1, b+1, c, d, e⟩ => some ⟨a, b, c+1, d+1, e⟩
  | ⟨a, b, c+1, d, e+1⟩ => some ⟨a+3, b, c, d, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b, c, d, e+2⟩
  | ⟨a, b, c, d+1, e⟩ => some ⟨a, b+1, c, d, e⟩
  | ⟨a, b, c, d, e+1⟩ => some ⟨a, b+1, c+1, d, e⟩
  | _ => none

-- R3 chain: drain a into e (with b=0, c=0).
theorem r3_chain : ∀ k d e, ⟨k, 0, 0, d, e⟩ [fm]⊢* ⟨0, 0, 0, d, e + 2 * k⟩ := by
  intro k; induction' k with k ih <;> intro d e
  · exists 0
  · step fm
    apply stepStar_trans (ih d (e + 2))
    ring_nf; finish

-- R4 chain: drain d into b.
theorem r4_chain : ∀ k b e, ⟨0, b, 0, k, e⟩ [fm]⊢* ⟨0, b + k, 0, 0, e⟩ := by
  intro k; induction' k with k ih <;> intro b e
  · exists 0
  · step fm
    apply stepStar_trans (ih (b + 1) e)
    ring_nf; finish

-- R1 chain: fire R1 k times.
theorem r1_chain : ∀ k a b c d e, ⟨a + k, b + k, c, d, e⟩ [fm]⊢* ⟨a, b, c + k, d + k, e⟩ := by
  intro k; induction' k with k ih <;> intro a b c d e
  · exists 0
  · rw [show a + (k + 1) = (a + k) + 1 from by ring,
        show b + (k + 1) = (b + k) + 1 from by ring]
    step fm
    apply stepStar_trans (ih a b (c + 1) (d + 1) e)
    ring_nf; finish

-- R2 step with b=0: single R2 application, splitting on a to reduce the match.
theorem r2_step (a c d e : ℕ) :
    fm ⟨a, 0, c + 1, d, e + 1⟩ = some ⟨a + 3, 0, c, d, e⟩ := by
  rcases a with _ | a <;> rfl

-- R2 chain: fire R2 k times (with b=0).
theorem r2_chain : ∀ k a d f, ⟨a, 0, k, d, f + k⟩ [fm]⊢* ⟨a + 3 * k, 0, 0, d, f⟩ := by
  intro k; induction' k with k ih <;> intro a d f
  · exists 0
  · apply stepStar_trans (step_stepStar (r2_step a k d (f + k)))
    apply stepStar_trans (ih (a + 3) d f)
    ring_nf; finish

-- R2 step with a=0 and general b.
theorem r2_step_a0 (b c d e : ℕ) :
    fm ⟨0, b, c + 1, d, e + 1⟩ = some ⟨3, b, c, d, e⟩ := by
  rfl

-- Spiral: from (3, b, c, d, f+b+c) reach (2b+3c+3, 0, 0, d+b, f).
theorem spiral : ∀ b c d f,
    ⟨3, b, c, d, f + b + c⟩ [fm]⊢* ⟨2 * b + 3 * c + 3, 0, 0, d + b, f⟩ := by
  intro b; induction' b using Nat.strongRecOn with b ih
  intro c d f
  rcases b with _ | _ | _ | _ | b
  · -- b = 0
    rw [show f + 0 + c = f + c from by ring]
    apply stepStar_trans (r2_chain c 3 d f)
    ring_nf; finish
  · -- b = 1
    rw [show (3 : ℕ) = 2 + 1 from by ring, show (1 : ℕ) = 0 + 1 from by ring,
        show f + 1 + c = f + (c + 1) from by ring]
    apply stepStar_trans (r1_chain 1 2 0 c d (f + (c + 1)))
    apply stepStar_trans (r2_chain (c + 1) 2 (d + 1) f)
    ring_nf; finish
  · -- b = 2
    rw [show (3 : ℕ) = 1 + 2 from by ring, show (2 : ℕ) = 0 + 2 from by ring,
        show f + 2 + c = f + (c + 2) from by ring]
    apply stepStar_trans (r1_chain 2 1 0 c d (f + (c + 2)))
    apply stepStar_trans (r2_chain (c + 2) 1 (d + 2) f)
    ring_nf; finish
  · -- b = 3
    rw [show (3 : ℕ) = 0 + 3 from by ring, show (3 : ℕ) = 0 + 3 from by ring,
        show f + 3 + c = f + (c + 3) from by ring]
    apply stepStar_trans (r1_chain 3 0 0 c d (f + (c + 3)))
    apply stepStar_trans (r2_chain (c + 3) 0 (d + 3) f)
    ring_nf; finish
  · -- b + 4: R1 x 3, then R2 x 1 (with a=0), then IH on b+1
    rw [show (3 : ℕ) = 0 + 3 from by ring,
        show b + 4 = (b + 1) + 3 from by ring,
        show f + (b + 4) + c = f + (c + 3) + (b + 1) from by ring]
    apply stepStar_trans (r1_chain 3 0 (b + 1) c d (f + (c + 3) + (b + 1)))
    -- state: (0, b+1, c+3, d+3, f+(c+3)+(b+1))
    rw [show f + (c + 3) + (b + 1) = (f + (b + 1) + (c + 2)) + 1 from by ring]
    apply stepStar_trans (step_stepStar (r2_step_a0 (b + 1) (c + 2) (d + 3) (f + (b + 1) + (c + 2))))
    -- state: (3, b+1, c+2, d+3, f+(b+1)+(c+2))
    apply stepStar_trans (ih (b + 1) (by omega) (c + 2) (d + 3) f)
    ring_nf; finish

-- Main transition: from canonical state to next canonical state.
theorem main_transition (d e : ℕ) :
    ⟨2 * d + 3, 0, 0, d, e⟩ [fm]⊢⁺ ⟨2 * d + 5, 0, 0, d + 1, e + 3 * d + 3⟩ := by
  step fm
  -- After R3: (2*d+2, 0, 0, d, e+2)
  apply stepStar_trans (r3_chain (2 * d + 2) d (e + 2))
  rw [show e + 2 + 2 * (2 * d + 2) = e + 4 * d + 6 from by ring]
  apply stepStar_trans (r4_chain d 0 (e + 4 * d + 6))
  -- After R4: (0, d, 0, 0, e+4*d+6)
  rw [show 0 + d = d from by ring,
      show e + 4 * d + 6 = (e + 4 * d + 5) + 1 from by ring]
  step fm
  -- After R5: (0, d+1, 1, 0, e+4*d+5)
  rw [show e + 4 * d + 5 = (e + 4 * d + 4) + 1 from by ring,
      show (1 : ℕ) = 0 + 1 from by ring]
  step fm
  -- After R2: (3, d+1, 0, 0, e+4*d+4)
  rw [show e + 4 * d + 4 = (e + 3 * d + 3) + (d + 1) + 0 from by ring]
  apply stepStar_trans (spiral (d + 1) 0 0 (e + 3 * d + 3))
  ring_nf; finish

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨7, 0, 0, 2, 5⟩)
  · execute fm 17
  apply progress_nonhalt_simple (fm := fm) (A := ℕ × ℕ)
    (fun ⟨d, e⟩ ↦ ⟨2 * d + 3, 0, 0, d, e⟩) ⟨2, 5⟩
  intro ⟨d, e⟩; exact ⟨⟨d + 1, e + 3 * d + 3⟩, main_transition d e⟩

end Sz22_2003_unofficial_820
