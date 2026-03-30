import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #882: [4/15, 11/21, 1617/2, 5/77, 3/11]

Vector representation:
```
 2 -1 -1  0  0
 0 -1  0 -1  1
-1  1  0  2  1
 0  0  1 -1 -1
 0  1  0  0 -1
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_882

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a, b+1, c+1, d, e⟩ => some ⟨a+2, b, c, d, e⟩
  | ⟨a, b+1, c, d+1, e⟩ => some ⟨a, b, c, d, e+1⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b+1, c, d+2, e+1⟩
  | ⟨a, b, c, d+1, e+1⟩ => some ⟨a, b, c+1, d, e⟩
  | ⟨a, b, c, d, e+1⟩ => some ⟨a, b+1, c, d, e⟩
  | _ => none

-- R4 repeated: (0, 0, c, d+k, e+k) ⊢* (0, 0, c+k, d, e)
theorem r4_phase : ∀ k, ⟨0, 0, c, d + k, e + k⟩ [fm]⊢* ⟨0, 0, c + k, d, e⟩ := by
  intro k; induction' k with k ih generalizing c d e
  · exists 0
  · rw [show d + (k + 1) = (d + k) + 1 from by ring,
        show e + (k + 1) = (e + k) + 1 from by ring]
    step fm
    apply stepStar_trans (ih (c := c + 1))
    ring_nf; finish

-- R3+R1 interleaved: (a+1, 0, k, d, e) ⊢* (a+1+k, 0, 0, d+2*k, e+k)
theorem r3r1_chain : ∀ k, ⟨a + 1, 0, k, d, e⟩ [fm]⊢* ⟨a + 1 + k, 0, 0, d + 2 * k, e + k⟩ := by
  intro k; induction' k with k ih generalizing a d e
  · exists 0
  · step fm
    step fm
    apply stepStar_trans (ih (a := a + 1) (d := d + 2) (e := e + 1))
    ring_nf; finish

-- R3+R2 drain: (a+k, 0, 0, d, e) ⊢* (a, 0, 0, d+k, e+2*k)
theorem drain : ∀ k, ⟨a + k, 0, 0, d, e⟩ [fm]⊢* ⟨a, 0, 0, d + k, e + 2 * k⟩ := by
  intro k; induction' k with k ih generalizing a d e
  · exists 0
  · rw [show a + (k + 1) = (a + k) + 1 from by ring]
    step fm
    step fm
    apply stepStar_trans (ih (d := d + 1) (e := e + 2))
    ring_nf; finish

-- R5+R1 opening: (0, 0, c+1, 0, f+1) ⊢* (2, 0, c, 0, f)
theorem r5_r1 : ⟨0, 0, c + 1, 0, f + 1⟩ [fm]⊢* ⟨2, 0, c, 0, f⟩ := by
  step fm; step fm; finish

-- Full spiral+drain: (2, 0, c, 0, f) ⊢* (0, 0, 0, 3*c+2, 3*c+f+4)
theorem full_spiral : ⟨2, 0, c, 0, f⟩ [fm]⊢* ⟨0, 0, 0, 3 * c + 2, 3 * c + f + 4⟩ := by
  apply stepStar_trans (r3r1_chain c (a := 1) (d := 0) (e := f))
  rw [show 1 + 1 + c = 0 + (c + 2) from by ring]
  apply stepStar_trans (drain (c + 2) (a := 0) (d := 0 + 2 * c) (e := f + c))
  ring_nf; finish

-- Main transition: (0, 0, 0, d+1, d+f+2) ⊢⁺ (0, 0, 0, 3*d+2, 3*d+f+4)
theorem main_trans : ⟨0, 0, 0, d + 1, d + f + 2⟩ [fm]⊢⁺ ⟨0, 0, 0, 3 * d + 2, 3 * d + f + 4⟩ := by
  -- First R4 step for ⊢⁺
  step fm
  -- Remaining R4 steps: need to match (0, 0, 1, d, f+1+d) with r4_phase
  -- r4_phase expects (0, 0, c, d+k, e+k); here c=1, k=d, so d_base=0, e_base=f+1
  -- but d+k = 0+d which doesn't unify with d
  -- Instead, directly prove the combined R4 phase
  rw [show d + f + 1 = f + 1 + d from by ring]
  have h1 : ⟨0, 0, 1, d, f + 1 + d⟩ [fm]⊢* ⟨0, 0, d + 1, 0, f + 1⟩ := by
    have := r4_phase d (c := 1) (d := 0) (e := f + 1)
    rwa [Nat.zero_add, Nat.add_comm 1 d] at this
  apply stepStar_trans h1
  apply stepStar_trans (r5_r1 (c := d) (f := f))
  exact full_spiral

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨0, 0, 0, 1, 2⟩) (by execute fm 2)
  apply progress_nonhalt_simple (fm := fm) (A := ℕ × ℕ)
    (fun ⟨d, f⟩ ↦ ⟨0, 0, 0, d + 1, d + f + 2⟩) ⟨0, 0⟩
  intro ⟨d, f⟩
  refine ⟨⟨3 * d + 1, f + 1⟩, ?_⟩
  show ⟨0, 0, 0, d + 1, d + f + 2⟩ [fm]⊢⁺ ⟨0, 0, 0, 3 * d + 1 + 1, 3 * d + 1 + (f + 1) + 2⟩
  rw [show 3 * d + 1 + 1 = 3 * d + 2 from by ring,
      show 3 * d + 1 + (f + 1) + 2 = 3 * d + f + 4 from by ring]
  exact main_trans

end Sz22_2003_unofficial_882
