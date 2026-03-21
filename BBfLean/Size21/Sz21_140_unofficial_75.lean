import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz21_140_unofficial #75: [4/15, 33/14, 65/2, 7/11, 33/13]

Vector representation:
```
 2 -1 -1  0  0  0
-1  1  0 -1  1  0
-1  0  1  0  0  1
 0  0  0  1 -1  0
 0  1  0  0  1 -1
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz21_140_unofficial_75

def Q := ℕ × ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a, b+1, c+1, d, e, f⟩ => some ⟨a+2, b, c, d, e, f⟩
  | ⟨a+1, b, c, d+1, e, f⟩ => some ⟨a, b+1, c, d, e+1, f⟩
  | ⟨a+1, b, c, d, e, f⟩ => some ⟨a, b, c+1, d, e, f+1⟩
  | ⟨a, b, c, d, e+1, f⟩ => some ⟨a, b, c, d+1, e, f⟩
  | ⟨a, b, c, d, e, f+1⟩ => some ⟨a, b+1, c, d, e+1, f⟩
  | _ => none

-- R3 repeated: (a+k, 0, c, 0, e, f) →* (a, 0, c+k, 0, e, f+k)
-- When b=0, d=0, R3 fires: (a+1, 0, c, 0, e, f) → (a, 0, c+1, 0, e, f+1)
theorem r3_chain : ∀ k, ∀ a c e f, ⟨a+k, 0, c, 0, e, f⟩ [fm]⊢* ⟨a, 0, c+k, 0, e, f+k⟩ := by
  intro k; induction' k with k ih <;> intro a c e f
  · exists 0
  rw [← Nat.add_assoc]
  step fm
  apply stepStar_trans (ih _ _ _ _)
  ring_nf; finish

-- R4 repeated: (0, 0, c, d, e+k, f) →* (0, 0, c, d+k, e, f)
theorem r4_chain : ∀ k, ∀ c d e f, ⟨0, 0, c, d, e+k, f⟩ [fm]⊢* ⟨0, 0, c, d+k, e, f⟩ := by
  intro k; induction' k with k ih <;> intro c d e f
  · exists 0
  rw [show e + (k + 1) = (e + k) + 1 from by omega]
  step fm
  apply stepStar_trans (ih c (d + 1) e f)
  ring_nf; finish

-- R1+R2 chain: k rounds
-- (a, 1, c+k+1, d+k, e, g) →* (a+k, 1, c+1, d, e+k, g)
theorem r1r2_chain : ∀ k, ∀ a c d e g, ⟨a, 1, c+k+1, d+k, e, g⟩ [fm]⊢* ⟨a+k, 1, c+1, d, e+k, g⟩ := by
  intro k; induction' k with k ih <;> intro a c d e g
  · exists 0
  -- State: (a, 1, c+(k+1)+1, d+(k+1), e, g)
  -- = (a, 0+1, (c+k+1)+1, (d+k)+1, e, g)
  -- R1 fires: (a+2, 0, c+k+1, (d+k)+1, e, g)
  -- = (a+2, 0, c+k+1, (d+k)+1, e, g) where a+2 ≥ 1 and (d+k)+1 ≥ 1
  -- R2 fires: (a+1, 0+1, c+k+1, d+k, e+1, g)
  rw [show c + (k + 1) + 1 = (c + k + 1) + 1 from by omega,
      show d + (k + 1) = (d + k) + 1 from by omega]
  step fm
  step fm
  apply stepStar_trans (ih (a + 1) c d (e + 1) g)
  ring_nf; finish

-- Main transition: (n+1, 0, 0, 0, n, f) ⊢⁺ (n+2, 0, 0, 0, n+1, f+n)
theorem main_trans (n f : ℕ) : ⟨n+1, 0, 0, 0, n, f⟩ [fm]⊢⁺ ⟨n+2, 0, 0, 0, n+1, f+n⟩ := by
  -- Phase 1: R3 × (n+1): (n+1, 0, 0, 0, n, f) →* (0, 0, n+1, 0, n, f+n+1)
  apply stepStar_stepPlus_stepPlus (c₂ := ⟨0, 0, n+1, 0, n, f+n+1⟩)
  · have h := r3_chain (n+1) 0 0 n f
    simp only [Nat.zero_add] at h; exact h
  -- Phase 2: R4 × n: (0, 0, n+1, 0, n, f+n+1) →* (0, 0, n+1, n, 0, f+n+1)
  apply stepStar_stepPlus_stepPlus (c₂ := ⟨0, 0, n+1, n, 0, f+n+1⟩)
  · have h := r4_chain n (n+1) 0 0 (f+n+1)
    simp only [Nat.zero_add] at h; exact h
  -- Phase 3: R5 step: (0, 0, n+1, n, 0, f+n+1) → (0, 1, n+1, n, 1, f+n)
  -- Note: f+n+1 = (f+n)+1
  rw [show f + n + 1 = (f + n) + 1 from by omega]
  apply step_stepStar_stepPlus (c₂ := ⟨0, 1, n+1, n, 1, f+n⟩)
  · show fm ⟨0, 0, n+1, n, 0, (f+n)+1⟩ = some ⟨0, 1, n+1, n, 1, f+n⟩; simp [fm]
  -- Phase 4+5: R1R2 chain + final R1
  rcases n with _ | n
  · -- n=0: (0, 1, 1, 0, 1, f) → R1 → (2, 0, 0, 0, 1, f)
    step fm; finish
  · -- n≥1: state is (0, 1, n+2, n+1, 1, f+(n+1))
    -- R1R2 chain with k=n: (0, 1, 0+n+1+1, 0+n+1, 1, f+(n+1)) →* (0+n+1, 1, 0+1, 0, 1+n+1, f+(n+1))
    -- = (0, 1, n+2, n+1, 1, f+(n+1)) →* (n+1, 1, 1, 0, n+2, f+(n+1))
    apply stepStar_trans (c₂ := ⟨n+1, 1, 1, 0, n+2, f+(n+1)⟩)
    · have h := r1r2_chain (n+1) 0 0 0 1 (f+(n+1))
      simp only [Nat.zero_add] at h
      rw [show 1 + (n + 1) = n + 2 from by omega] at h; exact h
    -- Final R1: (n+1, 0+1, 0+1, 0, n+2, f+(n+1)) → (n+1+2, 0, 0, 0, n+2, f+(n+1))
    step fm
    ring_nf; finish

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨1, 0, 0, 0, 0, 0⟩) (by exists 0)
  apply progress_nonhalt_simple (fm := fm) (A := ℕ × ℕ)
    (fun ⟨n, f⟩ ↦ ⟨n+1, 0, 0, 0, n, f⟩) ⟨0, 0⟩
  intro ⟨n, f⟩; exact ⟨⟨n+1, f+n⟩, main_trans n f⟩
