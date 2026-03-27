import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #533: [28/15, 39/22, 65/2, 11/7, 33/13]

Vector representation:
```
 2 -1 -1  1  0  0
-1  1  0  0 -1  1
-1  0  1  0  0  1
 0  0  0 -1  1  0
 0  1  0  0  1 -1
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_533

def Q := ℕ × ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a, b+1, c+1, d, e, f⟩ => some ⟨a+2, b, c, d+1, e, f⟩
  | ⟨a+1, b, c, d, e+1, f⟩ => some ⟨a, b+1, c, d, e, f+1⟩
  | ⟨a+1, b, c, d, e, f⟩ => some ⟨a, b, c+1, d, e, f+1⟩
  | ⟨a, b, c, d+1, e, f⟩ => some ⟨a, b, c, d, e+1, f⟩
  | ⟨a, b, c, d, e, f+1⟩ => some ⟨a, b+1, c, d, e+1, f⟩
  | _ => none

-- R3 repeated: convert a to c,f (when b=0, e=0)
theorem a_to_cf : ⟨a+k, 0, c, d, 0, f⟩ [fm]⊢* ⟨a, 0, c+k, d, 0, f+k⟩ := by
  have many_step : ∀ k c f, ⟨a+k, 0, c, d, 0, f⟩ [fm]⊢* ⟨a, 0, c+k, d, 0, f+k⟩ := by
    intro k; induction' k with k h <;> intro c f
    · exists 0
    rw [← Nat.add_assoc]
    step fm
    apply stepStar_trans (h _ _)
    ring_nf; finish
  exact many_step k c f

-- R4 repeated: convert d to e (when a=0, b=0, e=0)
theorem d_to_e : ⟨0, 0, c, d+k, 0, f⟩ [fm]⊢* ⟨0, 0, c, d, k, f⟩ := by
  have many_step : ∀ k, ∀ d, ⟨0, 0, c, d+k, 0, f⟩ [fm]⊢* ⟨0, 0, c, d, k, f⟩ := by
    intro k; induction' k with k h <;> intro d
    · exists 0
    rw [show d + (k + 1) = (d + 1) + k from by ring]
    apply stepStar_trans (h _)
    step fm; finish
  exact many_step k d

-- (R2,R1) chain
theorem r2r1_chain : ∀ c, ∀ a d f, ⟨a+1, 0, c+1, d, E+c+1, f⟩ [fm]⊢*
    ⟨a+c+2, 0, 0, d+c+1, E, f+c+1⟩ := by
  intro c; induction' c with c h <;> intro a d f
  · rw [show E + 0 + 1 = E + 1 from by ring]
    step fm; step fm; ring_nf; finish
  rw [show E + (c + 1) + 1 = (E + c + 1) + 1 from by ring]
  rw [show (c + 1) + 1 = (c + 1) + 1 from rfl]
  step fm; step fm
  apply stepStar_trans (h _ _ _)
  ring_nf; finish

-- R2 repeated: drain e (when c=0)
theorem r2_drain : ∀ k, ∀ a b f, ⟨a+k, b, 0, d, k, f⟩ [fm]⊢* ⟨a, b+k, 0, d, 0, f+k⟩ := by
  intro k; induction' k with k h <;> intro a b f
  · exists 0
  rw [show a + (k + 1) = (a + k) + 1 from by ring]
  step fm
  apply stepStar_trans (h _ _ _)
  ring_nf; finish

-- (R3,R1) chain
theorem r3r1_chain : ∀ k, ∀ a d f, ⟨a+1, b+k, 0, d, 0, f⟩ [fm]⊢*
    ⟨a+k+1, b, 0, d+k, 0, f+k⟩ := by
  intro k; induction' k with k h <;> intro a d f
  · exists 0
  rw [show b + (k + 1) = (b + k) + 1 from by ring]
  step fm; step fm
  apply stepStar_trans (h _ _ _)
  ring_nf; finish

-- Full transition from (0, 0, n+2, 0, 2n+2, F) to canonical next state
-- Uses R5, R1, r2r1_chain, r2_drain, R3, R1, r3r1_chain
theorem interleaved (n F : ℕ) :
    ⟨0, 0, n+2, 0, 2*n+2, F+n+2⟩ [fm]⊢⁺
    ⟨n+3, 0, 0, 2*n+4, 0, F+4*n+6⟩ := by
  -- R5
  rw [show n + 2 = (n + 1) + 1 from by ring,
      show F+n+2 = (F+n+1)+1 from by ring]
  apply step_stepStar_stepPlus (by unfold fm; rfl)
  -- R1
  step fm
  -- After R5,R1: (2, 0, n+1, 1, (2*n+2)+1, F+n+1)
  -- = (1+1, 0, n+1, 1, (2*n+2)+1, F+n+1)
  -- (R2,R1) x (n+1): need (a+1, 0, c+1, d, E+c+1, f)
  -- a=1, c=n, d=1, E=n+2, E+c+1 = (n+2)+n+1 = 2n+3
  -- But (2*n+2)+1 = 2n+3 = (n+2)+n+1 ✓
  -- Lean has: (2, 0, n+1, 1, (2*n+2)+1, F+n+1)
  -- which is (1+1, 0, (n+1), 1, (2*n+2)+1, F+n+1)
  -- We need (1+1, 0, n+1, 1, (n+2)+n+1, F+n+1)
  rw [show (2 * n + 2) + 1 = (n + 2) + n + 1 from by ring]
  apply stepStar_trans (@r2r1_chain (n+2) n 1 1 (F+n+1))
  -- After chain: (1+n+2, 0, 0, 1+n+1, n+2, F+n+1+n+1) = (n+3, 0, 0, n+2, n+2, F+2n+2)
  -- R2 x (n+2): drain e
  -- Need: (a+(n+2), b, 0, d, n+2, f)
  -- Lean has: (1+n+2, 0, 0, 1+n+1, n+2, F+n+1+n+1)
  rw [show 1 + n + 2 = 1 + (n + 2) from by ring,
      show 1 + n + 1 = n + 2 from by ring,
      show F + n + 1 + n + 1 = F + 2*n + 2 from by ring]
  apply stepStar_trans (@r2_drain (n+2) (n+2) 1 0 (F+2*n+2))
  -- After drain: (1, 0+(n+2), 0, n+2, 0, F+2n+2+(n+2)) = (1, n+2, 0, n+2, 0, F+3n+4)
  -- R3: (1, n+2, 0, n+2, 0, F+3n+4) → (0, n+2, 1, n+2, 0, F+3n+5)
  -- R1: (0, n+2, 1, n+2, 0, F+3n+5) → (2, n+1, 0, n+3, 0, F+3n+5)
  rw [show (1 : ℕ) = 0 + 1 from by ring,
      show 0 + (n + 2) = (n + 1) + 1 from by ring,
      show F + 2 * n + 2 + (n + 2) = (F + 3*n + 3) + 1 from by ring]
  step fm; step fm
  -- After R3+R1: (0+1+2, n+1, 0, (n+2)+1, 0, (F+3n+3)+1+1)
  -- = (3, n+1, 0, n+3, 0, F+3n+5)
  -- (R3,R1) x (n+1)
  -- Need: (a+1, b+k, 0, d, 0, f) with a=2, b=0, k=n+1
  -- Lean has: (0+1+2, n+1, 0, (n+2)+1, 0, (F+3*n+3)+1+1)
  rw [show (2 : ℕ) = 1 + 1 from by ring,
      show n + 2 + 1 = n + 3 from by ring,
      show F + 3 * n + 3 + 1 + 1 = F + 3*n + 5 from by ring,
      show n + 1 = 0 + (n + 1) from by ring]
  apply stepStar_trans (@r3r1_chain 0 (n+1) 1 (n+3) (F+3*n+5))
  ring_nf; finish

-- Main transition: C(n) →⁺ C(n+1)
theorem main_trans (n : ℕ) : ⟨n+2, 0, 0, 2*n+2, 0, 2*n^2+4*n+2⟩ [fm]⊢⁺
    ⟨n+3, 0, 0, 2*n+4, 0, 2*n^2+8*n+8⟩ := by
  -- Phase 1: R3 x (n+2)
  rw [show n + 2 = 0 + (n + 2) from by ring]
  apply stepStar_stepPlus_stepPlus (@a_to_cf 0 (n+2) 0 (2*n+2) (2*n^2+4*n+2))
  -- Now: (0, 0, 0+(n+2), 2n+2, 0, 2n^2+4n+2+(n+2))
  -- = (0, 0, n+2, 2n+2, 0, 2n^2+5n+4)
  rw [show (0 : ℕ) + (n + 2) = n + 2 from by ring,
      show 2*n^2+4*n+2+(n+2) = 2*n^2+5*n+4 from by ring,
      show 2*n+2 = 0 + (2*n+2) from by ring]
  -- Phase 2: R4 x (2n+2)
  apply stepStar_stepPlus_stepPlus (@d_to_e (n+2) 0 (2*n+2) (2*n^2+5*n+4))
  -- Now: (0, 0, n+2, 0, 2n+2, 2n^2+5n+4)
  -- Use interleaved with F = 2n^2+4n+2 (so F+n+2 = 2n^2+5n+4)
  have h : 2*n^2+5*n+4 = (2*n^2+4*n+2) + n + 2 := by ring
  rw [h]
  have h2 : 2*n^2+8*n+8 = (2*n^2+4*n+2) + 4*n + 6 := by ring
  rw [h2]
  exact interleaved n (2*n^2+4*n+2)

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨2, 0, 0, 2, 0, 2⟩) (by execute fm 6)
  suffices h : ¬halts fm (0+2, 0, 0, 2*0+2, 0, 2*0^2+4*0+2) by exact h
  apply progress_nonhalt_simple (fm := fm) (A := ℕ)
    (fun n ↦ ⟨n+2, 0, 0, 2*n+2, 0, 2*n^2+4*n+2⟩) 0
  intro n; exact ⟨n+1, by
    show ⟨n+2, 0, 0, 2*n+2, 0, 2*n^2+4*n+2⟩ [fm]⊢⁺
      ⟨(n+1)+2, 0, 0, 2*(n+1)+2, 0, 2*(n+1)^2+4*(n+1)+2⟩
    rw [show (n+1)+2 = n+3 from by ring,
        show 2*(n+1)+2 = 2*n+4 from by ring,
        show 2*(n+1)^2+4*(n+1)+2 = 2*n^2+8*n+8 from by ring]
    exact main_trans n⟩

end Sz22_2003_unofficial_533
