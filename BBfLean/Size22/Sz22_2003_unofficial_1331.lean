import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #1331: [63/10, 2/33, 121/2, 5/7, 63/11]

Vector representation:
```
-1  2 -1  1  0
 1 -1  0  0 -1
-1  0  0  0  2
 0  0  1 -1  0
 0  2  0  1 -1
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_1331

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a+1, b, c+1, d, e⟩ => some ⟨a, b+2, c, d+1, e⟩
  | ⟨a, b+1, c, d, e+1⟩ => some ⟨a+1, b, c, d, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b, c, d, e+2⟩
  | ⟨a, b, c, d+1, e⟩ => some ⟨a, b, c+1, d, e⟩
  | ⟨a, b, c, d, e+1⟩ => some ⟨a, b+2, c, d+1, e⟩
  | _ => none

-- R4 chain: move d to c (with a=0, b=0).
theorem d_to_c : ∀ k c d e, ⟨0, 0, c, d + k, e⟩ [fm]⊢* ⟨0, 0, c + k, d, e⟩ := by
  intro k; induction' k with k ih <;> intro c d e
  · exists 0
  · rw [Nat.add_succ d k]; step fm
    apply stepStar_trans (ih (c + 1) d e); ring_nf; finish

-- R3 chain: drain a to e (with b=0, c=0).
theorem r3_chain : ∀ a D e, ⟨a, 0, 0, D, e⟩ [fm]⊢* ⟨0, 0, 0, D, e + 2 * a⟩ := by
  intro a; induction' a with a ih <;> intro D e
  · exists 0
  · step fm
    apply stepStar_trans (ih D (e + 2)); ring_nf; finish

-- R1+R2 interleaved chain: (1, b, k, D, k) →* (1, b+k, 0, D+k, 0)
theorem r1r2_chain : ∀ k b D, ⟨1, b, k, D, k⟩ [fm]⊢* ⟨1, b + k, 0, D + k, 0⟩ := by
  intro k; induction' k with k ih <;> intro b D
  · exists 0
  · rw [show (k + 1 : ℕ) = k + 1 from rfl]
    step fm  -- R1: (0, b+2, k, D+1, k+1)
    step fm  -- R2: (1, b+1, k, D+1, k)
    apply stepStar_trans (ih (b + 1) (D + 1)); ring_nf; finish

-- Spiral: (0, 0, d, 0, d+2) →* (0, d+1, 0, d+1, 2)
theorem spiral (d : ℕ) : ⟨0, 0, d, 0, d + 2⟩ [fm]⊢* ⟨0, d + 1, 0, d + 1, 2⟩ := by
  step fm  -- R5: (0, 2, d, 1, d+1)
  step fm  -- R2: (1, 1, d, 1, d)
  apply stepStar_trans (r1r2_chain d 1 1)
  -- now at (1, d+1, 0, d+1, 0)
  step fm  -- R3: (0, d+1, 0, d+1, 2)
  ring_nf; finish

-- General drain: (a, b, 0, D, 2) →* (0, 0, 0, D, 2*a + b + 2)
-- By strong induction on b: for b+2, do R2,R2,R3 to get (a+1, b, 0, D, 2), apply IH.
theorem drain_gen : ∀ b, ∀ a D, ⟨a, b, 0, D, 2⟩ [fm]⊢* ⟨0, 0, 0, D, 2 * a + b + 2⟩ := by
  intro b; induction' b using Nat.strongRecOn with b ih
  rcases b with _ | _ | b
  · -- b = 0
    intro a D
    apply stepStar_trans (r3_chain a D 2)
    ring_nf; finish
  · -- b = 1
    intro a D
    step fm  -- R2: (a+1, 0, 0, D, 1)
    apply stepStar_trans (r3_chain (a + 1) D 1)
    ring_nf; finish
  · -- b + 2
    intro a D
    step fm  -- R2: (a+1, b+1, 0, D, 1)
    step fm  -- R2: (a+2, b, 0, D, 0)
    step fm  -- R3: (a+1, b, 0, D, 2)
    apply stepStar_trans (ih b (by omega) (a + 1) D)
    ring_nf; finish

-- Combined spiral + drain: (0, 0, d, 0, d+2) →* (0, 0, 0, d+1, d+3)
theorem spiral_drain (d : ℕ) :
    ⟨0, 0, d, 0, d + 2⟩ [fm]⊢⁺ ⟨0, 0, 0, d + 1, d + 3⟩ := by
  step fm  -- R5: (0, 2, d, 1, d+1)
  step fm  -- R2: (1, 1, d, 1, d)
  apply stepStar_trans (r1r2_chain d 1 1)
  -- now at (1, 1+d, 0, 1+d, 0)
  show ⟨1, 1 + d, 0, 1 + d, 0⟩ [fm]⊢* ⟨0, 0, 0, d + 1, d + 3⟩
  step fm  -- R3: (0, 1+d, 0, 1+d, 2)
  show ⟨0, 1 + d, 0, 1 + d, 2⟩ [fm]⊢* ⟨0, 0, 0, d + 1, d + 3⟩
  rw [show 1 + d = d + 1 from by ring]
  apply stepStar_trans (drain_gen (d + 1) 0 (d + 1))
  ring_nf; finish

-- Main transition: (0, 0, 0, d, d+2) ⊢⁺ (0, 0, 0, d+1, d+3)
theorem main_trans (d : ℕ) : ⟨0, 0, 0, d, d + 2⟩ [fm]⊢⁺ ⟨0, 0, 0, d + 1, d + 3⟩ := by
  apply stepStar_stepPlus_stepPlus
  · show ⟨0, 0, 0, d, d + 2⟩ [fm]⊢* ⟨0, 0, d, 0, d + 2⟩
    have h := d_to_c d 0 0 (d + 2)
    simp at h; exact h
  · exact spiral_drain d

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨0, 0, 0, 0, 2⟩)
  · execute fm 1
  apply progress_nonhalt_simple (fm := fm) (A := ℕ)
    (fun d ↦ ⟨0, 0, 0, d, d + 2⟩) 0
  intro d; exact ⟨d + 1, main_trans d⟩

end Sz22_2003_unofficial_1331
