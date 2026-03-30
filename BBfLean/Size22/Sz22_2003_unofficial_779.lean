import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #779: [35/6, 55/2, 52/77, 3/13, 91/5]

Vector representation:
```
-1 -1  1  1  0  0
-1  0  1  0  1  0
 2  0  0 -1 -1  1
 0  1  0  0  0 -1
 0  0 -1  1  0  1
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_779

def Q := ℕ × ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a+1, b+1, c, d, e, f⟩ => some ⟨a, b, c+1, d+1, e, f⟩
  | ⟨a+1, b, c, d, e, f⟩ => some ⟨a, b, c+1, d, e+1, f⟩
  | ⟨a, b, c, d+1, e+1, f⟩ => some ⟨a+2, b, c, d, e, f+1⟩
  | ⟨a, b, c, d, e, f+1⟩ => some ⟨a, b+1, c, d, e, f⟩
  | ⟨a, b, c+1, d, e, f⟩ => some ⟨a, b, c, d+1, e, f+1⟩
  | _ => none

-- R4 chain: move f to b (when a=0, d=0).
-- (0, b, c, 0, e, j) →* (0, b+j, c, 0, e, 0)
theorem f_to_b : ∀ j, ∀ b, ⟨0, b, c, 0, e, j⟩ [fm]⊢* ⟨0, b + j, c, 0, e, 0⟩ := by
  intro j; induction' j with j ih <;> intro b
  · exists 0
  · step fm
    apply stepStar_trans (ih (b + 1))
    ring_nf; finish

-- R5 then R3.
theorem r5_r3 : ⟨0, b, c + 1, 0, e + 1, 0⟩ [fm]⊢⁺ ⟨2, b, c, 0, e, 2⟩ := by
  step fm; step fm; finish

-- R1,R1,R3 chain: j rounds.
-- (2, 2j, c, d, j, f) →* (2, 0, c+2j, d+j, 0, f+j)
theorem r1r1r3_chain : ∀ j, ∀ c d f,
    ⟨2, 2 * j, c, d, j, f⟩ [fm]⊢* ⟨2, 0, c + 2 * j, d + j, 0, f + j⟩ := by
  intro j; induction' j with j ih <;> intro c d f
  · simp; exists 0
  · rw [show 2 * (j + 1) = 2 * j + 1 + 1 from by ring,
        show (j + 1 : ℕ) = j + 1 from rfl]
    step fm  -- R1: (1, 2j+1, c+1, d+1, j+1, f)
    step fm  -- R1: (0, 2j, c+1+1, d+1+1, j+1, f)
    step fm  -- R3: (2, 2j, c+1+1, d+1, j, f+1)
    apply stepStar_trans (ih (c + 1 + 1) (d + 1) (f + 1))
    ring_nf; finish

-- R2,R2,R3 chain: j rounds.
-- (2, 0, c, j, e, f) →* (2, 0, c+2j, 0, e+j, f+j)
theorem r2r2r3_chain : ∀ j, ∀ c e f,
    ⟨2, 0, c, j, e, f⟩ [fm]⊢* ⟨2, 0, c + 2 * j, 0, e + j, f + j⟩ := by
  intro j; induction' j with j ih <;> intro c e f
  · simp; exists 0
  · step fm  -- R2: (1, 0, c+1, j+1, e+1, f)
    step fm  -- R2: (0, 0, c+1+1, j+1, e+1+1, f)
    step fm  -- R3: (2, 0, c+1+1, j, e+1, f+1)
    apply stepStar_trans (ih (c + 1 + 1) (e + 1) (f + 1))
    ring_nf; finish

-- Final R2,R2.
theorem final_r2r2 : ⟨2, 0, c, 0, e, f⟩ [fm]⊢⁺ ⟨0, 0, c + 2, 0, e + 2, f⟩ := by
  step fm; step fm; finish

-- Main transition: C(k) ⊢⁺ C(k+1)
-- C(k) = (0, 0, 2k^2+3k+2, 0, k+2, 2k+2)
theorem main_transition (k : ℕ) :
    ⟨0, 0, 2 * k ^ 2 + 3 * k + 2, 0, k + 2, 2 * k + 2⟩ [fm]⊢⁺
    ⟨0, 0, 2 * k ^ 2 + 7 * k + 7, 0, k + 3, 2 * k + 4⟩ := by
  -- Phase 1: R4 chain, move f=2k+2 to b
  apply stepStar_stepPlus_stepPlus
  · exact f_to_b (2 * k + 2) 0
  -- State: (0, 2k+2, 2k^2+3k+2, 0, k+2, 0)
  rw [show 0 + (2 * k + 2) = 2 * k + 2 from by ring]
  -- Phase 2: R5+R3
  apply stepPlus_stepStar_stepPlus
  · rw [show 2 * k ^ 2 + 3 * k + 2 = (2 * k ^ 2 + 3 * k + 1) + 1 from by ring,
        show k + 2 = (k + 1) + 1 from by ring]
    exact r5_r3
  -- State: (2, 2k+2, 2k^2+3k+1, 0, k+1, 2)
  -- Phase 3: R1,R1,R3 chain with j = k+1 rounds
  apply stepStar_trans
  · rw [show 2 * k + 2 = 2 * (k + 1) from by ring]
    exact r1r1r3_chain (k + 1) (2 * k ^ 2 + 3 * k + 1) 0 2
  -- State: (2, 0, 2k^2+5k+3, k+1, 0, k+3)
  -- Phase 4: R2,R2,R3 chain with j = k+1 rounds
  apply stepStar_trans
  · rw [show (2 * k ^ 2 + 3 * k + 1) + 2 * (k + 1) = 2 * k ^ 2 + 5 * k + 3 from by ring,
        show 0 + (k + 1) = k + 1 from by ring,
        show 2 + (k + 1) = k + 3 from by ring]
    exact r2r2r3_chain (k + 1) (2 * k ^ 2 + 5 * k + 3) 0 (k + 3)
  -- State: (2, 0, 2k^2+7k+5, 0, k+1, 2k+4)
  -- Phase 5: Final R2,R2
  rw [show (2 * k ^ 2 + 5 * k + 3) + 2 * (k + 1) = 2 * k ^ 2 + 7 * k + 5 from by ring,
      show 0 + (k + 1) = k + 1 from by ring,
      show (k + 3) + (k + 1) = 2 * k + 4 from by ring]
  have h := final_r2r2 (c := 2 * k ^ 2 + 7 * k + 5) (e := k + 1) (f := 2 * k + 4)
  rw [show (2 * k ^ 2 + 7 * k + 5) + 2 = 2 * k ^ 2 + 7 * k + 7 from by ring,
      show (k + 1) + 2 = k + 3 from by ring] at h
  exact stepPlus_stepStar h

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨0, 0, 2, 0, 2, 2⟩)
  · execute fm 5
  apply progress_nonhalt (fm := fm)
    (P := fun q ↦ ∃ k, q = ⟨0, 0, 2 * k ^ 2 + 3 * k + 2, 0, k + 2, 2 * k + 2⟩)
  · intro c ⟨k, hk⟩; subst hk
    exact ⟨⟨0, 0, 2 * (k + 1) ^ 2 + 3 * (k + 1) + 2, 0, (k + 1) + 2, 2 * (k + 1) + 2⟩,
      ⟨k + 1, rfl⟩,
      by rw [show 2 * (k + 1) ^ 2 + 3 * (k + 1) + 2 = 2 * k ^ 2 + 7 * k + 7 from by ring,
            show (k + 1) + 2 = k + 3 from by ring,
            show 2 * (k + 1) + 2 = 2 * k + 4 from by ring]
         exact main_transition k⟩
  · exact ⟨0, rfl⟩
