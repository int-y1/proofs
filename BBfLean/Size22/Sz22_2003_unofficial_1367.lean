import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #1367: [63/10, 4/77, 121/2, 5/3, 10/11]

Vector representation:
```
-1  2 -1  1  0
 2  0  0 -1 -1
-1  0  0  0  2
 0 -1  1  0  0
 1  0  1  0 -1
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_1367

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a+1, b, c+1, d, e⟩ => some ⟨a, b+2, c, d+1, e⟩
  | ⟨a, b, c, d+1, e+1⟩ => some ⟨a+2, b, c, d, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b, c, d, e+2⟩
  | ⟨a, b+1, c, d, e⟩ => some ⟨a, b, c+1, d, e⟩
  | ⟨a, b, c, d, e+1⟩ => some ⟨a+1, b, c+1, d, e⟩
  | _ => none

-- R2 chain: drain d and e simultaneously, adding 2 to a each time.
theorem r2_chain : ∀ j, ∀ a b, ⟨a, b, 0, j, j⟩ [fm]⊢* ⟨a + 2 * j, b, 0, 0, 0⟩ := by
  intro j; induction' j with j ih <;> intro a b
  · exists 0
  · rw [show a + 2 * (j + 1) = (a + 2) + 2 * j from by ring]
    step fm; exact ih (a + 2) b

-- R3 chain: drain a, adding 2 to e each time (c=0 so R1 doesn't fire).
theorem r3_chain : ∀ j, ∀ b e, ⟨j, b, 0, 0, e⟩ [fm]⊢* ⟨0, b, 0, 0, e + 2 * j⟩ := by
  intro j; induction' j with j ih <;> intro b e
  · exists 0
  · step fm
    apply stepStar_trans (ih b (e + 2)); ring_nf; finish

-- R4 chain: drain b into c.
theorem r4_chain : ∀ j, ∀ c e, ⟨0, j, c, 0, e⟩ [fm]⊢* ⟨0, 0, c + j, 0, e⟩ := by
  intro j; induction' j with j ih <;> intro c e
  · exists 0
  · step fm
    apply stepStar_trans (ih (c + 1) e); ring_nf; finish

-- R1+R1+R2 interleaved chain.
theorem r1r2_interleave : ∀ j, ∀ b d e,
    ⟨2, b, 2 * (j + 1), d, e + j⟩ [fm]⊢* ⟨0, b + 4 * (j + 1), 0, d + j + 2, e⟩ := by
  intro j; induction' j with j ih <;> intro b d e
  · step fm; step fm; ring_nf; finish
  · rw [show 2 * (j + 1 + 1) = (2 * (j + 1)) + 2 from by ring,
        show e + (j + 1) = (e + j) + 1 from by ring]
    step fm; step fm; step fm
    apply stepStar_trans (ih (b + 4) (d + 1) e); ring_nf; finish

-- Main transition: (0, 0, 2k+2, 0, 2k+4) ⊢⁺ (0, 0, 4k+6, 0, 4k+8).
theorem main_trans (k : ℕ) :
    ⟨0, 0, 2 * k + 2, 0, 2 * k + 4⟩ [fm]⊢⁺ ⟨0, 0, 4 * k + 6, 0, 4 * k + 8⟩ := by
  -- Phase 1 (R5): e has +1, fires R5
  rw [show 2 * k + 4 = (2 * k + 3) + 1 from by ring]
  step fm
  -- Now goal: (1, 0, 2*k+3, 0, 2*k+3) ⊢* ...
  -- Phase 2 (R1): a=1, c=2k+3 ≥ 1
  rw [show 2 * k + 2 + 1 = (2 * k + 2) + 1 from by ring]
  step fm
  -- Now goal: (0, 2, 2*k+2, 1, 2*k+3) ⊢* ...
  -- Phase 3 (R2): d=1, e=2k+3 ≥ 1
  rw [show (2 * k + 3 : ℕ) = (2 * k + 2) + 1 from by ring]
  step fm
  -- Now goal: (2, 2, 2*k+2, 0, 2*k+2) ⊢* ...
  -- Phase 4: interleave chain
  have h4 := r1r2_interleave k 2 0 (k + 2)
  rw [show (k + 2) + k = 2 * (k + 1) from by ring,
      show 2 + 4 * (k + 1) = 4 * k + 6 from by ring,
      show 0 + k + 2 = k + 2 from by ring] at h4
  rw [show (2 * k + 2 : ℕ) = 2 * (k + 1) from by ring]
  apply stepStar_trans h4
  -- Phase 5: R2 chain
  apply stepStar_trans (r2_chain (k + 2) 0 (4 * k + 6))
  rw [show 0 + 2 * (k + 2) = 2 * k + 4 from by ring]
  -- Phase 6: R3 chain
  apply stepStar_trans (r3_chain (2 * k + 4) (4 * k + 6) 0)
  rw [show 0 + 2 * (2 * k + 4) = 4 * k + 8 from by ring]
  -- Phase 7: R4 chain
  apply stepStar_trans (r4_chain (4 * k + 6) 0 (4 * k + 8))
  ring_nf; finish

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨0, 0, 2, 0, 4⟩) (by execute fm 8)
  apply progress_nonhalt_simple (fm := fm) (A := ℕ)
    (fun k ↦ ⟨0, 0, 2 * k + 2, 0, 2 * k + 4⟩) 0
  intro k
  refine ⟨2 * k + 2, ?_⟩
  have := main_trans k
  rw [show 4 * k + 6 = 2 * (2 * k + 2) + 2 from by ring,
      show 4 * k + 8 = 2 * (2 * k + 2) + 4 from by ring] at this
  exact this

end Sz22_2003_unofficial_1367
