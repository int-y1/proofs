import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #1583: [7/45, 6/5, 275/14, 3/11, 35/2]

Vector representation:
```
 0 -2 -1  1  0
 1  1 -1  0  0
-1  0  2 -1  1
 0  1  0  0 -1
-1  0  1  1  0
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_1583

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a, b+2, c+1, d, e⟩ => some ⟨a, b, c, d+1, e⟩
  | ⟨a, b, c+1, d, e⟩ => some ⟨a+1, b+1, c, d, e⟩
  | ⟨a+1, b, c, d+1, e⟩ => some ⟨a, b, c+2, d, e+1⟩
  | ⟨a, b, c, d, e+1⟩ => some ⟨a, b+1, c, d, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b, c+1, d+1, e⟩
  | _ => none

-- R4 chain: transfer e to b.
theorem e_to_b : ∀ k b, ⟨a, b, 0, 0, k⟩ [fm]⊢* ⟨a, b + k, 0, 0, 0⟩ := by
  intro k; induction k with
  | zero => intro b; exists 0
  | succ k ih =>
    intro b
    show ⟨a, b, 0, 0, k + 1⟩ [fm]⊢* ⟨a, b + (k + 1), 0, 0, 0⟩
    step fm
    apply stepStar_trans (ih (b + 1))
    ring_nf; finish

-- R3,R1,R1 drain.
theorem drain : ∀ k, ∀ d e, ⟨k + 1, 4 * k + 2, 0, d + 2, e⟩ [fm]⊢* ⟨0, 0, 1, d + k + 2, e + k + 1⟩ := by
  intro k; induction k with
  | zero =>
    intro d e
    show ⟨0 + 1, 0 + 2, 0, d + 1 + 1, e⟩ [fm]⊢* ⟨0, 0, 1, d + 0 + 2, e + 0 + 1⟩
    step fm; step fm; ring_nf; finish
  | succ k ih =>
    intro d e
    show ⟨(k + 1) + 1, (4 * k + 2) + 4, 0, d + 1 + 1, e⟩ [fm]⊢*
         ⟨0, 0, 1, d + (k + 1) + 2, e + (k + 1) + 1⟩
    step fm; step fm; step fm
    show ⟨k + 1, 4 * k + 2, 0, (d + 1) + 2, e + 1⟩ [fm]⊢*
         ⟨0, 0, 1, d + (k + 1) + 2, e + (k + 1) + 1⟩
    apply stepStar_trans (ih (d + 1) (e + 1))
    ring_nf; finish

-- Main loop: 9-step round reducing d by 1.
theorem main_loop : ∀ D, ∀ j E, ⟨j + 2, 2, 0, D, E⟩ [fm]⊢* ⟨j + D + 2, 2, 0, 0, E + 3 * D⟩ := by
  intro D; induction D with
  | zero => intro j E; exists 0
  | succ D ih =>
    intro j E
    show ⟨j + 1 + 1, 2, 0, D + 1, E⟩ [fm]⊢* ⟨j + (D + 1) + 2, 2, 0, 0, E + 3 * (D + 1)⟩
    step fm; step fm; step fm; step fm; step fm; step fm; step fm; step fm; step fm
    show ⟨(j + 1) + 2, 2, 0, D, E + 3⟩ [fm]⊢* ⟨j + (D + 1) + 2, 2, 0, 0, E + 3 * (D + 1)⟩
    apply stepStar_trans (ih (j + 1) (E + 3))
    ring_nf; finish

-- Main transition: canonical n to canonical n+1.
theorem main_trans (n : ℕ) :
    ⟨n + 2, 2, 0, 0, 4 * n + 2⟩ [fm]⊢⁺ ⟨n + 3, 2, 0, 0, 4 * n + 6⟩ := by
  -- Phase 1: R4 chain
  apply stepStar_stepPlus_stepPlus (e_to_b (4 * n + 2) 2 (a := n + 2))
  rw [show 2 + (4 * n + 2) = 4 * n + 4 from by ring]
  -- Phase 2: R5 (one step to make ⊢⁺)
  show ⟨n + 1 + 1, 4 * n + 4, 0, 0, 0⟩ [fm]⊢⁺ ⟨n + 3, 2, 0, 0, 4 * n + 6⟩
  step fm
  -- Now ⊢*, continue with R1
  step fm
  -- After R5,R1: (n+1, 4n+2, 0, 2, 0)
  -- Need to apply drain with d=0,e=0 but drain expects d+2 form
  -- Current state should be (n+1, 4n+2, 0, 2, 0)
  -- drain n 0 0: (n+1, 4n+2, 0, 0+2, 0) ⊢* (0, 0, 1, 0+n+2, 0+n+1)
  apply stepStar_trans (drain n 0 0)
  rw [show 0 + n + 2 = n + 2 from by ring,
      show 0 + n + 1 = n + 1 from by ring]
  -- 7 opening steps: (0, 0, 1, n+2, n+1) -> (2, 2, 0, n+1, n+3)
  show ⟨0, 0, 0 + 1, n + 1 + 1, n + 1⟩ [fm]⊢* ⟨n + 3, 2, 0, 0, 4 * n + 6⟩
  step fm; step fm; step fm; step fm; step fm; step fm; step fm
  -- Main loop: (2, 2, 0, n+1, n+3) -> (n+3, 2, 0, 0, 4n+6)
  show ⟨0 + 2, 2, 0, n + 1, n + 3⟩ [fm]⊢* ⟨n + 3, 2, 0, 0, 4 * n + 6⟩
  apply stepStar_trans (main_loop (n + 1) 0 (n + 3))
  ring_nf; finish

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨2, 2, 0, 0, 2⟩) (by execute fm 8)
  apply progress_nonhalt_simple (fm := fm) (A := ℕ)
    (fun n ↦ ⟨n + 2, 2, 0, 0, 4 * n + 2⟩) 0
  intro n; exact ⟨n + 1, main_trans n⟩

end Sz22_2003_unofficial_1583
