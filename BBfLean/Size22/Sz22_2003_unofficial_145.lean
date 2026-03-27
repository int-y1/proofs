import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #145: [1/45, 22/35, 715/2, 21/11, 5/39]

Vector representation:
```
 0 -2 -1  0  0  0
 1  0 -1 -1  1  0
-1  0  1  0  1  1
 0  1  0  1 -1  0
 0 -1  1  0  0 -1
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_145

def Q := ℕ × ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a, b+2, c+1, d, e, f⟩ => some ⟨a, b, c, d, e, f⟩
  | ⟨a, b, c+1, d+1, e, f⟩ => some ⟨a+1, b, c, d, e+1, f⟩
  | ⟨a+1, b, c, d, e, f⟩ => some ⟨a, b, c+1, d, e+1, f+1⟩
  | ⟨a, b, c, d, e+1, f⟩ => some ⟨a, b+1, c, d+1, e, f⟩
  | ⟨a, b+1, c, d, e, f+1⟩ => some ⟨a, b, c+1, d, e, f⟩
  | _ => none

/-- R3+R2 loop: each pair sends d down by 1, e up by 2, f up by 1. -/
theorem r3r2_loop : ∀ k, ∀ e f,
    ⟨1, 0, 0, k, e, f⟩ [fm]⊢* ⟨1, 0, 0, 0, e + 2 * k, f + k⟩ := by
  intro k; induction' k with k ih <;> intro e f
  · ring_nf; finish
  step fm; step fm
  apply stepStar_trans (ih (e + 2) (f + 1))
  ring_nf; finish

/-- R4 drain: convert e into b and d, with c=0. -/
theorem r4_drain : ∀ k, ∀ b d f,
    ⟨0, b, 0, d, k, f⟩ [fm]⊢* ⟨0, b + k, 0, d + k, 0, f⟩ := by
  intro k; induction' k with k ih <;> intro b d f
  · finish
  step fm
  apply stepStar_trans (ih (b + 1) (d + 1) f)
  ring_nf; finish

/-- R5+R1 loop: each pair reduces b by 3 and f by 1. -/
theorem r5r1_loop : ∀ k, ∀ d f,
    ⟨0, 3 * k + 1, 0, d, 0, k + f⟩ [fm]⊢* ⟨0, 1, 0, d, 0, f⟩ := by
  intro k; induction' k with k ih <;> intro d f
  · ring_nf; finish
  rw [show 3 * (k + 1) + 1 = (3 * k + 1 + 2) + 1 from by ring,
      show (k + 1) + f = k + f + 1 from by ring]
  step fm; step fm
  exact ih d f

/-- Main transition: (1, 0, 0, 0, 3*(n+1), 2*(n+1)) ⊢⁺ (1, 0, 0, 0, 3*(2*n+3), 2*(2*n+3)). -/
theorem main_step : ∀ n,
    ⟨1, 0, 0, 0, 3 * (n + 1), 2 * (n + 1)⟩ [fm]⊢⁺
    ⟨1, 0, 0, 0, 3 * (2 * n + 3), 2 * (2 * n + 3)⟩ := by
  intro n
  -- Phase 1: 6 fixed steps
  -- R3: (0, 0, 1, 0, 3n+4, 2n+3)
  -- R4: (0, 1, 1, 1, 3n+3, 2n+3)  [c=1,d=1 but b<2 so R1 no; R2 fires]
  -- R2: (1, 1, 0, 0, 3n+4, 2n+3)
  -- R3: (0, 1, 1, 0, 3n+5, 2n+4)
  -- R4: (0, 2, 1, 1, 3n+4, 2n+4)  [b=2,c=1 so R1 fires]
  -- R1: (0, 0, 0, 1, 3n+4, 2n+4)
  rw [show 3 * (n + 1) = n + n + n + 3 from by ring,
      show 2 * (n + 1) = n + n + 2 from by ring]
  step fm; step fm; step fm; step fm; step fm; step fm
  -- Now at (0, 0, 0, 1, 3n+4, 2n+4) = (0, 0, 0, 1, 3*(n+1)+1, 2*(n+1)+2)
  -- Phase 2: R4 drain with k=3*(n+1)+1, b=0, d=1
  rw [show n + n + n + 4 = 3 * n + 4 from by ring,
      show n + n + 4 = 2 * n + 4 from by ring]
  apply stepStar_trans (r4_drain (3 * n + 4) 0 1 (2 * n + 4))
  -- Now at (0, 3n+4, 0, 3n+5, 0, 2n+4)
  -- Phase 3: R5+R1 loop with k=n+1 pairs
  -- b = 3n+4 = 3*(n+1)+1, f = 2n+4 = (n+1)+n+3
  rw [show 0 + (3 * n + 4) = 3 * (n + 1) + 1 from by ring,
      show 1 + (3 * n + 4) = 3 * n + 5 from by ring,
      show 2 * n + 4 = (n + 1) + (n + 3) from by ring]
  apply stepStar_trans (r5r1_loop (n + 1) (3 * n + 5) (n + 3))
  -- Now at (0, 1, 0, 3n+5, 0, n+3)
  -- R5: (0, 0, 1, 3n+5, 0, n+2)
  -- R2: (1, 0, 0, 3n+4, 1, n+2)
  rw [show n + 3 = (n + 2) + 1 from by ring]
  step fm; step fm
  -- Phase 4: R3+R2 loop with k=3n+4
  apply stepStar_trans (r3r2_loop (3 * n + 4) 1 (n + 2))
  -- Now at (1, 0, 0, 0, 1+2*(3n+4), (n+2)+(3n+4)) = (1, 0, 0, 0, 6n+9, 4n+6)
  -- = (1, 0, 0, 0, 3*(2n+3), 2*(2n+3))
  ring_nf; finish

theorem nonhalt : ¬halts fm c₀ := by
  -- Bootstrap: c₀ = (1,0,0,0,0,0) ->* (1,0,0,0,3,2) in 11 steps
  apply stepStar_not_halts_not_halts (c₂ := ⟨1, 0, 0, 0, 3, 2⟩)
  · execute fm 11
  -- Use progress_nonhalt_simple with C(n) = (1, 0, 0, 0, 3*(n+1), 2*(n+1))
  apply progress_nonhalt_simple (fm := fm) (A := ℕ)
    (C := fun n ↦ ⟨1, 0, 0, 0, 3 * (n + 1), 2 * (n + 1)⟩) (i₀ := 0)
  intro n
  exact ⟨2 * n + 2, main_step n⟩

end Sz22_2003_unofficial_145
