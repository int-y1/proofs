import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #1128: [5/6, 44/35, 49/2, 1/5, 3/11, 5/7]

Vector representation:
```
-1 -1  1  0  0
 2  0 -1 -1  1
-1  0  0  2  0
 0  0 -1  0  0
 0  1  0  0 -1
 0  0  1 -1  0
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_1128

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a+1, b+1, c, d, e⟩ => some ⟨a, b, c+1, d, e⟩
  | ⟨a, b, c+1, d+1, e⟩ => some ⟨a+2, b, c, d, e+1⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b, c, d+2, e⟩
  | ⟨a, b, c+1, d, e⟩ => some ⟨a, b, c, d, e⟩
  | ⟨a, b, c, d, e+1⟩ => some ⟨a, b+1, c, d, e⟩
  | ⟨a, b, c, d+1, e⟩ => some ⟨a, b, c+1, d, e⟩
  | _ => none

theorem r3_drain : ∀ a, ∀ d e, ⟨a, 0, 0, d, e⟩ [fm]⊢* ⟨0, 0, 0, d + 2 * a, e⟩ := by
  intro a; induction' a with a ih <;> intro d e
  · exists 0
  · step fm
    apply stepStar_trans (ih (d + 2) e)
    ring_nf; finish

theorem r5_drain : ∀ e, ∀ b D, ⟨0, b, 0, D, e⟩ [fm]⊢* ⟨0, b + e, 0, D, 0⟩ := by
  intro e; induction' e with e ih <;> intro b D
  · exists 0
  · step fm
    apply stepStar_trans (ih (b + 1) D)
    ring_nf; finish

theorem r2_chain : ∀ c, ∀ a D e, ⟨a, 0, c, D + c, e⟩ [fm]⊢* ⟨a + 2 * c, 0, 0, D, e + c⟩ := by
  intro c; induction' c with c ih <;> intro a D e
  · exists 0
  · rw [show D + (c + 1) = (D + c) + 1 from by ring]
    step fm
    apply stepStar_trans (ih (a + 2) D (e + 1))
    ring_nf; finish

-- Spiral core: (0, b, c+1, D+b+c+1, e) →* (b+2*(c+1), 0, 0, D, e+b+c+1)
-- Proved by strong induction on b with base cases b=0 (r2_chain) and b=1.
theorem spiral_core : ∀ b, ∀ c D e,
    ⟨0, b, c + 1, D + b + c + 1, e⟩ [fm]⊢* ⟨b + 2 * (c + 1), 0, 0, D, e + b + c + 1⟩ := by
  intro b; induction' b using Nat.strongRecOn with b ih; intro c D e
  rcases b with _ | _ | b
  · -- b = 0: just r2_chain
    rw [show D + 0 + c + 1 = D + (c + 1) from by ring]
    apply stepStar_trans (r2_chain (c + 1) 0 D e)
    ring_nf; finish
  · -- b = 1: R2, R1, then r2_chain
    rw [show D + 1 + c + 1 = (D + c + 1) + 1 from by ring]
    step fm  -- R2: (2, 1, c, D+c+1, e+1)
    step fm  -- R1: (1, 0, c+1, D+c+1, e+1)
    rw [show D + c + 1 = D + (c + 1) from by ring]
    apply stepStar_trans (r2_chain (c + 1) 1 D (e + 1))
    ring_nf; finish
  · -- b+2: round then recurse
    rw [show D + (b + 2) + c + 1 = (D + b + c + 1) + 2 from by ring]
    -- round: (0, b+2, c+1, (D+b+c+1)+2, e) →* (0, b, c+2, D+b+c+2, e+1)
    step fm  -- R2: (2, b+2, c, D+b+c+1+1, e+1)
    step fm  -- R1: (1, b+1, c+1, D+b+c+2, e+1)
    step fm  -- R1: (0, b, c+2, D+b+c+2, e+1)
    -- Now (0, b, c+2, D+b+c+2, e+1) = (0, b, (c+1)+1, D+b+(c+1)+1, e+1)
    rw [show c + 2 = (c + 1) + 1 from by ring,
        show D + b + c + 2 = D + b + (c + 1) + 1 from by ring]
    apply stepStar_trans (ih b (by omega) (c + 1) D (e + 1))
    ring_nf; finish

-- Full spiral: (0, e, 1, D+e+1, 0) →* (e+2, 0, 0, D, e+1)
theorem spiral : ∀ e D,
    ⟨0, e, 1, D + e + 1, 0⟩ [fm]⊢* ⟨e + 2, 0, 0, D, e + 1⟩ := by
  intro e D
  rw [show (1 : ℕ) = 0 + 1 from by ring,
      show D + e + 1 = D + e + 0 + 1 from by ring,
      show (0 : ℕ) = 0 from rfl]
  apply stepStar_trans (spiral_core e 0 D 0)
  ring_nf; finish

theorem main_trans : ∀ e d,
    ⟨e + 1, 0, 0, d, e⟩ [fm]⊢⁺ ⟨e + 2, 0, 0, d + e, e + 1⟩ := by
  intro e d
  apply step_stepStar_stepPlus
  · show fm ⟨e + 1, 0, 0, d, e⟩ = some ⟨e, 0, 0, d + 2, e⟩
    simp [fm]
  apply stepStar_trans (r3_drain e (d + 2) e)
  apply stepStar_trans (r5_drain e 0 (d + 2 + 2 * e))
  rw [show (0 : ℕ) + e = e from by ring,
      show d + 2 + 2 * e = (d + e) + e + 1 + 1 from by ring]
  step fm
  exact spiral e (d + e)

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨1, 0, 0, 0, 0⟩)
  · exists 0
  apply progress_nonhalt_simple (fm := fm) (A := ℕ × ℕ)
    (fun ⟨e, d⟩ ↦ ⟨e + 1, 0, 0, d, e⟩) ⟨0, 0⟩
  intro ⟨e, d⟩; exists ⟨e + 1, d + e⟩; exact main_trans e d
