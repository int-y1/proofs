import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #74: [1/18, 286/35, 55/2, 21/11, 2/39]

Vector representation:
```
-1 -2  0  0  0  0
 1  0 -1 -1  1  1
-1  0  1  0  1  0
 0  1  0  1 -1  0
 1 -1  0  0  0 -1
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_74

def Q := ℕ × ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a+1, b+2, c, d, e, f⟩ => some ⟨a, b, c, d, e, f⟩
  | ⟨a, b, c+1, d+1, e, f⟩ => some ⟨a+1, b, c, d, e+1, f+1⟩
  | ⟨a+1, b, c, d, e, f⟩ => some ⟨a, b, c+1, d, e+1, f⟩
  | ⟨a, b, c, d, e+1, f⟩ => some ⟨a, b+1, c, d+1, e, f⟩
  | ⟨a, b+1, c, d, e, f+1⟩ => some ⟨a+1, b, c, d, e, f⟩
  | _ => none

-- R4 chain: transfers e to b and d.
theorem r4_chain : ∀ k, ∀ b d e f,
    ⟨0, b, 0, d, e+k, f⟩ [fm]⊢* ⟨(0:ℕ), b+k, 0, d+k, e, f⟩ := by
  intro k; induction' k with k ih <;> intro b d e f
  · exists 0
  rw [show e + (k + 1) = (e + k) + 1 from by ring]
  step fm
  apply stepStar_trans (ih (b + 1) (d + 1) e f)
  ring_nf; finish

-- R5+R1 drain: each round R5 then R1 reduces b by 3 and f by 1.
theorem r5r1_chain : ∀ k, ∀ D f,
    ⟨0, 3*k+2, 0, D, 0, f+k⟩ [fm]⊢* ⟨(0:ℕ), 2, 0, D, 0, f⟩ := by
  intro k; induction' k with k ih <;> intro D f
  · ring_nf; finish
  -- Goal: (0, 3(k+1)+2, 0, D, 0, f+(k+1)) ⊢* (0, 2, 0, D, 0, f)
  -- R5 needs (a, b+1, c, d, e, f+1): b+1 = 3k+5, f+1 = f+k+1
  rw [show 3 * (k + 1) + 2 = (3 * k + 4) + 1 from by ring,
      show f + (k + 1) = (f + k) + 1 from by ring]
  step fm
  -- Now: (1, 3k+4, 0, D, 0, f+k)
  -- R1 needs (a+1, b+2): a+1=1, b+2=3k+4, so b=3k+2
  rw [show 3 * k + 4 = (3 * k + 2) + 2 from by ring]
  step fm
  -- Now: (0, 3k+2, 0, D, 0, f+k)
  exact ih D f

-- R2+R3 interleaved chain plus final R2.
theorem r2r3_chain : ∀ k, ∀ E F,
    ⟨0, 1, 1, k+1, E, F⟩ [fm]⊢* ⟨(1:ℕ), 1, 0, 0, E+2*k+1, F+k+1⟩ := by
  intro k; induction' k with k ih <;> intro E F
  · step fm; ring_nf; finish
  rw [show (k + 1) + 1 = (k + 1) + 1 from rfl]
  step fm; step fm
  apply stepStar_trans (ih (E + 2) (F + 1))
  ring_nf; finish

-- Main transition: C(k) = (0,0,0,0,3k+2,2k+2) ⊢⁺ C(2k+1) = (0,0,0,0,6k+5,4k+4)
theorem main_trans (k : ℕ) :
    ⟨0, 0, 0, 0, 3*k+2, 2*k+2⟩ [fm]⊢⁺ ⟨(0:ℕ), 0, 0, 0, 6*k+5, 4*k+4⟩ := by
  -- Phase 1: R4 chain. (0,0,0,0,3k+2,2k+2) ⊢* (0,3k+2,0,3k+2,0,2k+2)
  apply stepStar_stepPlus_stepPlus (c₂ := ⟨0, 3*k+2, 0, 3*k+2, 0, 2*k+2⟩)
  · have h := r4_chain (3*k+2) 0 0 0 (2*k+2)
    simp only [Nat.zero_add] at h; exact h
  -- Phase 2: R5+R1 drain. (0,3k+2,0,3k+2,0,2k+2) ⊢* (0,2,0,3k+2,0,k+2)
  apply stepStar_stepPlus_stepPlus (c₂ := ⟨0, 2, 0, 3*k+2, 0, k+2⟩)
  · have h := r5r1_chain k (3*k+2) (k+2)
    rw [show k + 2 + k = 2 * k + 2 from by ring] at h; exact h
  -- Phase 2b: Final R5. (0,2,0,3k+2,0,k+2) -> (1,1,0,3k+2,0,k+1)
  apply stepStar_stepPlus_stepPlus (c₂ := ⟨1, 1, 0, 3*k+2, 0, k+1⟩)
  · step fm; finish
  -- Phase 2c: R3. (1,1,0,3k+2,0,k+1) -> (0,1,1,3k+2,1,k+1)
  apply stepStar_stepPlus_stepPlus (c₂ := ⟨0, 1, 1, 3*k+2, 1, k+1⟩)
  · step fm; finish
  -- Phase 3: R2+R3 chain. (0,1,1,3k+2,1,k+1) ⊢* (1,1,0,0,6k+4,4k+3)
  apply stepStar_stepPlus_stepPlus (c₂ := ⟨1, 1, 0, 0, 6*k+4, 4*k+3⟩)
  · have h := r2r3_chain (3*k+1) 1 (k+1)
    rw [show (3 * k + 1) + 1 = 3 * k + 2 from by ring,
        show 1 + 2 * (3 * k + 1) + 1 = 6 * k + 4 from by ring,
        show (k + 1) + (3 * k + 1) + 1 = 4 * k + 3 from by ring] at h
    exact h
  -- Phase 4: Tail steps R3, R4, R2, R1.
  step fm; step fm; step fm; step fm
  finish

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨0, 0, 0, 0, 2, 2⟩) (by execute fm 7)
  apply progress_nonhalt_simple (fm := fm) (A := ℕ)
    (fun k ↦ ⟨0, 0, 0, 0, 3*k+2, 2*k+2⟩) 0
  intro k
  refine ⟨2*k+1, ?_⟩
  show ⟨0, 0, 0, 0, 3*k+2, 2*k+2⟩ [fm]⊢⁺ ⟨(0:ℕ), 0, 0, 0, 3*(2*k+1)+2, 2*(2*k+1)+2⟩
  rw [show 3*(2*k+1)+2 = 6*k+5 from by ring,
      show 2*(2*k+1)+2 = 4*k+4 from by ring]
  exact main_trans k

end Sz22_2003_unofficial_74
