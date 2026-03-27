import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #143: [1/45, 22/35, 65/2, 147/13, 5/121]

Vector representation:
```
 0 -2 -1  0  0  0
 1  0 -1 -1  1  0
-1  0  1  0  0  1
 0  1  0  2  0 -1
 0  0  1  0 -2  0
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_143

def Q := ℕ × ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a, b+2, c+1, d, e, f⟩ => some ⟨a, b, c, d, e, f⟩
  | ⟨a, b, c+1, d+1, e, f⟩ => some ⟨a+1, b, c, d, e+1, f⟩
  | ⟨a+1, b, c, d, e, f⟩ => some ⟨a, b, c+1, d, e, f+1⟩
  | ⟨a, b, c, d, e, f+1⟩ => some ⟨a, b+1, c, d+2, e, f⟩
  | ⟨a, b, c, d, e+2, f⟩ => some ⟨a, b, c+1, d, e, f⟩
  | _ => none

-- R2/R3 chain: each pair consumes 1 from d, adds 1 to e and f
theorem r2r3_chain : ∀ k d e f, ⟨(0 : ℕ), 1, 1, d+k, e, f⟩ [fm]⊢* ⟨(0 : ℕ), 1, 1, d, e+k, f+k⟩ := by
  intro k; induction' k with k ih <;> intro d e f
  · finish
  · rw [show d + (k+1) = (d+k) + 1 from by ring]
    step fm; step fm
    apply stepStar_trans (ih d (e+1) (f+1))
    ring_nf; finish

-- R4 chain: converts f to b and d
theorem r4_chain : ∀ k b d e f, ⟨(0 : ℕ), b, 0, d, e, f+k⟩ [fm]⊢* ⟨(0 : ℕ), b+k, 0, d+2*k, e, f⟩ := by
  intro k; induction' k with k ih <;> intro b d e f
  · finish
  · rw [show f + (k+1) = (f+k) + 1 from by ring]
    step fm
    apply stepStar_trans (ih (b+1) (d+2) e f)
    ring_nf; finish

-- R5/R1 chain: each pair consumes 2 from e and 2 from b
theorem r5r1_chain : ∀ k b d e, ⟨(0 : ℕ), b+2*k, 0, d, e+2*k, (0 : ℕ)⟩ [fm]⊢* ⟨(0 : ℕ), b, 0, d, e, (0 : ℕ)⟩ := by
  intro k; induction' k with k ih <;> intro b d e
  · finish
  · rw [show b + 2*(k+1) = (b+2) + 2*k from by ring,
         show e + 2*(k+1) = (e+2) + 2*k from by ring]
    apply stepStar_trans (ih (b+2) d (e+2))
    step fm; step fm; finish

-- Tail of cycle: from (0,0,0,2,E,F) →* (0,1,1,2*F+2,0,0)
-- Uses R4 chain then R5/R1 chain then final R5.
theorem tail_phase : ∀ n, ⟨(0 : ℕ), 0, 0, 2, 2*n+2, 2*n+1⟩ [fm]⊢* ⟨(0 : ℕ), 1, 1, 4*n+4, 0, (0 : ℕ)⟩ := by
  intro n
  -- R4 chain: f=2*n+1 steps
  rw [show (2*n+1 : ℕ) = 0 + (2*n+1) from by ring]
  apply stepStar_trans (r4_chain (2*n+1) 0 2 (2*n+2) 0)
  -- Now at (0, 2*n+1, 0, 2+2*(2*n+1), 2*n+2, 0) = (0, 2*n+1, 0, 4*n+4, 2*n+2, 0)
  rw [show 0+(2*n+1) = 1+2*n from by ring,
      show 2*n+2 = 2+2*n from by ring,
      show 2+2*(2*n+1) = 4*n+4 from by ring]
  apply stepStar_trans (r5r1_chain n 1 (4*n+4) 2)
  -- Now at (0, 1, 0, 4*n+4, 2, 0)
  step fm; finish

-- Full cycle
theorem main_trans (n : ℕ) : ⟨(0 : ℕ), 1, 1, 2*(n+1), 0, (0 : ℕ)⟩ [fm]⊢⁺ ⟨(0 : ℕ), 1, 1, 4*(n+1), 0, (0 : ℕ)⟩ := by
  -- Phase 1: R2/R3 chain 2*(n+1) times
  rw [show 2*(n+1) = 0 + 2*(n+1) from by ring]
  apply stepStar_stepPlus_stepPlus (r2r3_chain (2*(n+1)) 0 0 0)
  simp only [Nat.zero_add]
  -- Now at (0, 1, 1, 0, 2*(n+1), 2*(n+1))
  -- R4 step: (0,1,1,0,2*(n+1), (2*(n+1)-1)+1) → (0,2,1,2,2*(n+1),2*(n+1)-1)
  rw [show 2*(n+1) = (2*n+1) + 1 from by ring]
  step fm
  -- After R4: (0, 2, 1, 2, (2*n+1)+1, 2*n+1)
  -- R1 step: b=2≥2, c=1≥1
  step fm
  -- After R1: (0, 0, 0, 2, (2*n+1)+1, 2*n+1)
  -- Now use tail_phase
  show ⟨(0 : ℕ), 0, 0, 2, 2*n+2, 2*n+1⟩ [fm]⊢* ⟨(0 : ℕ), 1, 1, 4*(n+1), 0, (0 : ℕ)⟩
  rw [show 4*(n+1) = 4*n+4 from by ring]
  exact tail_phase n

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨0, 1, 1, 2, 0, 0⟩)
  · execute fm 2
  apply progress_nonhalt_simple (A := ℕ) (C := fun n ↦ (⟨0, 1, 1, 2*(n+1), 0, 0⟩ : Q)) (i₀ := 0)
  intro n
  exact ⟨2*n+1, by rw [show 2*(2*n+1+1) = 4*(n+1) from by ring]; exact main_trans n⟩

end Sz22_2003_unofficial_143
