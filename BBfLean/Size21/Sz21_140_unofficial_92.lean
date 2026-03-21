import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz21_140_unofficial #92: [5/6, 77/2, 52/35, 3/13, 65/11]

Vector representation:
```
-1 -1  1  0  0  0
-1  0  0  1  1  0
 2  0 -1 -1  0  1
 0  1  0  0  0 -1
 0  0  1  0 -1  1
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz21_140_unofficial_92

def Q := ℕ × ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a+1, b+1, c, d, e, f⟩ => some ⟨a, b, c+1, d, e, f⟩
  | ⟨a+1, b, c, d, e, f⟩ => some ⟨a, b, c, d+1, e+1, f⟩
  | ⟨a, b, c+1, d+1, e, f⟩ => some ⟨a+2, b, c, d, e, f+1⟩
  | ⟨a, b, c, d, e, f+1⟩ => some ⟨a, b+1, c, d, e, f⟩
  | ⟨a, b, c, d, e+1, f⟩ => some ⟨a, b, c+1, d, e, f+1⟩
  | _ => none

-- Phase 1: R4 repeated: f → b (when a=0, c=0)
theorem f_to_b : ∀ k, ∀ b d e, ⟨0, b, 0, d, e, k⟩ [fm]⊢* ⟨0, b+k, 0, d, e, 0⟩ := by
  intro k; induction' k with k ih <;> intro b d e
  · exists 0
  rw [show b + (k + 1) = (b + k) + 1 from by ring]
  step fm
  apply stepStar_trans (ih _ _ _)
  ring_nf; finish

-- Phase 3: (R3, R1, R1) chain
-- Chain of k rounds: (0, b+2k, c+1, d+k, e, f) →* (0, b, c+1+k, d, e, f+k)
theorem r3r1r1_chain : ∀ k, ∀ b c d e f, ⟨0, b+2*k, c+1, d+k, e, f⟩ [fm]⊢* ⟨0, b, c+1+k, d, e, f+k⟩ := by
  intro k; induction' k with k ih <;> intro b c d e f
  · exists 0
  rw [show b + 2 * (k + 1) = (b + 2 * k) + 2 from by ring,
      show d + (k + 1) = (d + k) + 1 from by ring]
  rw [show (b + 2 * k) + 2 = ((b + 2 * k) + 1) + 1 from by ring]
  step fm  -- R3
  step fm  -- R1
  step fm  -- R1
  rw [show c + 2 = (c + 1) + 1 from by ring]
  apply stepStar_trans (ih b (c + 1) d e (f + 1))
  ring_nf; finish

-- Phase 5: (R2, R2, R3) chain (when b=0)
-- Chain of k rounds: (2, 0, c+k, d, e, f) →* (2, 0, c, d+k, e+2*k, f+k)
theorem r2r2r3_chain : ∀ k, ∀ c d e f, ⟨2, 0, c+k, d, e, f⟩ [fm]⊢* ⟨2, 0, c, d+k, e+2*k, f+k⟩ := by
  intro k; induction' k with k ih <;> intro c d e f
  · exists 0
  rw [show c + (k + 1) = (c + k) + 1 from by ring]
  step fm  -- R2
  step fm  -- R2
  rw [show d + 2 = (d + 1) + 1 from by ring]
  step fm  -- R3
  apply stepStar_trans (ih c (d + 1) (e + 2) (f + 1))
  ring_nf; finish

-- Main transition: C(n) = (0,0,0,n+1,n*n+1,2*n) ⊢⁺ C(n+1)
theorem main_trans (n : ℕ) : ⟨0, 0, 0, n+1, n*n+1, 2*n⟩ [fm]⊢⁺ ⟨0, 0, 0, n+2, (n+1)*(n+1)+1, 2*(n+1)⟩ := by
  -- Phase 1: R4 x 2n: → (0,2n,0,n+1,n²+1,0)
  apply stepStar_stepPlus_stepPlus (c₂ := ⟨0, 2*n, 0, n+1, n*n+1, 0⟩)
  · have h := @f_to_b (2*n) 0 (n+1) (n*n+1)
    simp only [Nat.zero_add] at h; exact h
  -- Phase 2: R5 once: → (0,2n,1,n+1,n²,1)  [this gives stepPlus]
  -- Phases 3-6 all as stepStar after this
  apply step_stepStar_stepPlus (c₂ := ⟨0, 2*n, 1, n+1, n*n, 1⟩)
  · show fm ⟨0, 2*n, 0, n+1, n*n+1, 0⟩ = some ⟨0, 2*n, 1, n+1, n*n, 1⟩
    simp [fm]
  -- Phase 3: (R3,R1,R1) x n: → (0,0,n+1,1,n²,n+1)
  apply stepStar_trans (c₂ := ⟨0, 0, n+1, 1, n*n, n+1⟩)
  · have h := @r3r1r1_chain n 0 0 1 (n*n) 1
    simp only [Nat.zero_add] at h
    rw [show 1 + n = n + 1 from by ring] at h
    exact h
  -- Phase 4: R3 once: → (2,0,n,0,n²,n+2)
  apply stepStar_trans (c₂ := ⟨2, 0, n, 0, n*n, n+2⟩)
  · apply step_stepStar
    show fm ⟨0, 0, n+1, 1, n*n, n+1⟩ = some ⟨2, 0, n, 0, n*n, n+2⟩
    simp [fm]
  -- Phase 5: (R2,R2,R3) x n: → (2,0,0,n,n²+2n,2n+2)
  apply stepStar_trans (c₂ := ⟨2, 0, 0, n, n*n+2*n, 2*n+2⟩)
  · have h := @r2r2r3_chain n 0 0 (n*n) (n+2)
    simp only [Nat.zero_add] at h
    refine stepStar_trans h ?_
    ring_nf; finish
  -- Phase 6: R2 twice: → (0,0,0,n+2,(n+1)²+1,2(n+1))
  step fm
  step fm
  ring_nf; finish

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨0, 0, 0, 1, 1, 0⟩) (by execute fm 1)
  apply progress_nonhalt_simple (fm := fm) (A := ℕ) (fun n ↦ ⟨0, 0, 0, n+1, n*n+1, 2*n⟩) 0
  intro n; exact ⟨n+1, main_trans n⟩
