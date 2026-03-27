import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #73: [1/18, 22/35, 845/2, 21/13, 2/33]

Vector representation:
```
-1 -2  0  0  0  0
 1  0 -1 -1  1  0
-1  0  1  0  0  2
 0  1  0  1  0 -1
 1 -1  0  0 -1  0
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_73

def Q := ℕ × ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a+1, b+2, c, d, e, f⟩ => some ⟨a, b, c, d, e, f⟩
  | ⟨a, b, c+1, d+1, e, f⟩ => some ⟨a+1, b, c, d, e+1, f⟩
  | ⟨a+1, b, c, d, e, f⟩ => some ⟨a, b, c+1, d, e, f+2⟩
  | ⟨a, b, c, d, e, f+1⟩ => some ⟨a, b+1, c, d+1, e, f⟩
  | ⟨a, b+1, c, d, e+1, f⟩ => some ⟨a+1, b, c, d, e, f⟩
  | _ => none

-- Phase 1: R4 chain: (0,b,0,d,e,f) -> (0,b+f,0,d+f,e,0)
theorem r4_chain : ∀ k, ∀ b d e, ⟨0, b, 0, d, e, k⟩ [fm]⊢* ⟨0, b+k, 0, d+k, e, 0⟩ := by
  intro k; induction' k with k h <;> intro b d e
  · simp; exists 0
  rw [show (k + 1 : ℕ) = k + 1 from rfl]
  step fm
  apply stepStar_trans (h (b+1) (d+1) e)
  ring_nf; finish

-- Phase 2: R5+R1 drain: (0, 3k+2, 0, D, e+k+1, 0) ->* (1, 1, 0, D, e, 0)
-- Each round: R5 then R1, b decreases by 3, e decreases by 1
theorem r5r1_drain : ∀ k, ∀ D e, ⟨0, 3*k+2, 0, D, e+k+1, 0⟩ [fm]⊢* ⟨1, 1, 0, D, e, 0⟩ := by
  intro k; induction' k with k h <;> intro D e
  · -- k=0: (0,2,0,D,e+1,0) -> R5: (1,1,0,D,e,0)
    step fm; finish
  · rw [show 3 * (k + 1) + 2 = (3 * k + 2) + 3 from by ring,
        show e + (k + 1) + 1 = (e + k + 1) + 1 from by ring]
    step fm; step fm
    exact h D e

-- Phase 3: R2+R3 interleaved chain: (0,1,1,d,e,f) ->* (0,1,1,0,e+d,f+2d)
theorem r2r3_chain : ∀ k, ∀ e f, ⟨0, 1, 1, k, e, f⟩ [fm]⊢* ⟨0, 1, 1, 0, e+k, f+2*k⟩ := by
  intro k; induction' k with k h <;> intro e f
  · simp; exists 0
  · -- (0,1,1,k+1,e,f) -> R2: (1,1,0,k,e+1,f) -> R3: (0,1,1,k,e+1,f+2)
    rw [show (k + 1 : ℕ) = k + 1 from rfl]
    step fm; step fm
    apply stepStar_trans (h (e+1) (f+2))
    ring_nf; finish

-- Main transition: (0,0,0,0,2n+2,3n+2) ⊢⁺ (0,0,0,0,4n+4,6n+5)
theorem main_trans (n : ℕ) :
    ⟨0, 0, 0, 0, 2*n+2, 3*n+2⟩ [fm]⊢⁺ ⟨(0:ℕ), 0, 0, 0, 4*n+4, 6*n+5⟩ := by
  -- Phase 1: R4 chain, f=3n+2 steps: (0,0,0,0,2n+2,3n+2) -> (0,3n+2,0,3n+2,2n+2,0)
  apply stepStar_stepPlus_stepPlus (c₂ := ⟨0, 3*n+2, 0, 3*n+2, 2*n+2, 0⟩)
  · have h := r4_chain (3*n+2) 0 0 (2*n+2)
    simp only [Nat.zero_add] at h; exact h
  -- Phase 2: R5+R1 drain: (0,3n+2,0,3n+2,2n+2,0) -> (1,1,0,3n+2,n+1,0)
  -- k=n, e=n+1: 3*n+2, e+(k+1) = n+1+n+1 = 2n+2
  apply stepStar_stepPlus_stepPlus (c₂ := ⟨1, 1, 0, 3*n+2, n+1, 0⟩)
  · have h := r5r1_drain n (3*n+2) (n+1)
    rw [show n + 1 + n + 1 = 2 * n + 2 from by ring] at h
    exact h
  -- Phase 2b: R3: (1,1,0,3n+2,n+1,0) -> (0,1,1,3n+2,n+1,2)
  apply stepPlus_stepStar_stepPlus
  · exact step_stepPlus (by show fm ⟨1, 1, 0, 3*n+2, n+1, 0⟩ = some ⟨0, 1, 1, 3*n+2, n+1, 2⟩; unfold fm; ring_nf; rfl)
  -- Phase 3: R2+R3 chain, d=3n+2 rounds: (0,1,1,3n+2,n+1,2) -> (0,1,1,0,4n+3,6n+6)
  apply stepStar_trans (c₂ := ⟨0, 1, 1, 0, 4*n+3, 6*n+6⟩)
  · have h := r2r3_chain (3*n+2) (n+1) 2
    rw [show n + 1 + (3 * n + 2) = 4 * n + 3 from by ring,
        show 2 + 2 * (3 * n + 2) = 6 * n + 6 from by ring] at h
    exact h
  -- Tail: (0,1,1,0,4n+3,6n+6) -> R4 -> R2 -> R1 -> (0,0,0,0,4n+4,6n+5)
  execute fm 3

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨0, 0, 0, 0, 2, 2⟩) (by execute fm 7)
  apply progress_nonhalt_simple (fm := fm) (A := ℕ)
    (fun n ↦ ⟨0, 0, 0, 0, 2*(n+1), 3*(n+1)-1⟩) 0
  intro n; exact ⟨2*n+1, by
    show ⟨0, 0, 0, 0, 2*(n+1), 3*(n+1)-1⟩ [fm]⊢⁺ ⟨0, 0, 0, 0, 2*(2*n+1+1), 3*(2*n+1+1)-1⟩
    rw [show 2 * (n + 1) = 2 * n + 2 from by ring,
        show 3 * (n + 1) - 1 = 3 * n + 2 from by omega,
        show 2 * (2 * n + 1 + 1) = 4 * n + 4 from by ring,
        show 3 * (2 * n + 1 + 1) - 1 = 6 * n + 5 from by omega]
    exact main_trans n⟩

end Sz22_2003_unofficial_73
