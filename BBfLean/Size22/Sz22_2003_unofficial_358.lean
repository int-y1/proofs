import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #358: [2/15, 297/14, 25/2, 7/11, 22/5]

Vector representation:
```
 1 -1 -1  0  0
-1  3  0 -1  1
-1  0  2  0  0
 0  0  0  1 -1
 1  0 -1  0  1
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_358

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a, b+1, c+1, d, e⟩ => some ⟨a+1, b, c, d, e⟩
  | ⟨a+1, b, c, d+1, e⟩ => some ⟨a, b+3, c, d, e+1⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b, c+2, d, e⟩
  | ⟨a, b, c, d, e+1⟩ => some ⟨a, b, c, d+1, e⟩
  | ⟨a, b, c+1, d, e⟩ => some ⟨a+1, b, c, d, e+1⟩
  | _ => none

-- R2+R1^3: consume one unit of d
theorem consume_d_one : ∀ k c d e,
    ⟨2*k+1, 0, c+3, d+1, e⟩ [fm]⊢* ⟨2*k+3, 0, c, d, e+1⟩ := by
  intro k c d e
  step fm; step fm; step fm; step fm
  ring_nf; finish

-- Iterate consume_d j times
theorem consume_d_iter : ∀ j, ∀ k c d e,
    ⟨2*k+1, 0, c+3*j, d+j, e⟩ [fm]⊢* ⟨2*(k+j)+1, 0, c, d, e+j⟩ := by
  intro j; induction' j with j ih <;> intro k c d e
  · exists 0
  rw [show c + 3 * (j + 1) = (c + 3 * j) + 3 from by ring,
      show d + (j + 1) = (d + j) + 1 from by ring]
  apply stepStar_trans (consume_d_one k (c + 3 * j) (d + j) e)
  rw [show 2 * k + 3 = 2 * (k + 1) + 1 from by ring]
  apply stepStar_trans (ih (k + 1) c d (e + 1))
  rw [show 2 * (k + 1 + j) + 1 = 2 * (k + (j + 1)) + 1 from by ring,
      show e + 1 + j = e + (j + 1) from by ring]
  finish

-- R3 chain: drain a into c
theorem r3_chain : ∀ a, ∀ c e,
    ⟨a, 0, c, 0, e⟩ [fm]⊢* ⟨0, 0, c+2*a, 0, e⟩ := by
  intro a; induction' a with a ih <;> intro c e
  · exists 0
  step fm
  apply stepStar_trans (ih _ _)
  ring_nf; finish

-- R4 chain: convert e to d
theorem r4_chain : ∀ e, ∀ c d,
    ⟨0, 0, c, d, e⟩ [fm]⊢* ⟨0, 0, c, d+e, 0⟩ := by
  intro e; induction' e with e ih <;> intro c d
  · exists 0
  step fm
  apply stepStar_trans (ih _ _)
  ring_nf; finish

-- Main transition: (0, 0, r+3*n+16, n+5, 0) ⊢⁺ (0, 0, r+4*n+22, n+6, 0)
-- Next state: r' = r+n+3, n' = n+1, and r'+3*n'+16 = r+n+3+3n+3+16 = r+4n+22
theorem main_trans (n r : ℕ) :
    ⟨0, 0, r+3*n+16, n+5, 0⟩ [fm]⊢⁺ ⟨0, 0, r+4*n+22, n+6, 0⟩ := by
  -- Phase 0: R5 step
  apply step_stepStar_stepPlus
  · show fm ⟨0, 0, r + 3 * n + 16, n + 5, 0⟩ = some ⟨1, 0, r + 3 * n + 15, n + 5, 1⟩
    simp [fm]
  -- Phase 1: consume_d (n+5) times
  apply stepStar_trans
  · show ⟨1, 0, r + 3 * n + 15, n + 5, 1⟩ [fm]⊢* ⟨2 * n + 11, 0, r, 0, n + 6⟩
    have h := consume_d_iter (n + 5) 0 r 0 1
    simp only [(by ring : r + 3 * (n + 5) = r + 3 * n + 15),
               (by ring : 0 + (n + 5) = n + 5),
               (by ring : 2 * 0 + 1 = 1),
               (by ring : 2 * (n + 5) + 1 = 2 * n + 11),
               (by ring : 1 + (n + 5) = n + 6)] at h
    exact h
  -- Phase 2: R3 chain
  apply stepStar_trans (r3_chain (2 * n + 11) r (n + 6))
  -- Phase 3: R4 chain
  rw [show r + 2 * (2 * n + 11) = r + 4 * n + 22 from by ring]
  apply stepStar_trans (r4_chain (n + 6) (r + 4 * n + 22) 0)
  ring_nf; finish

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨0, 0, 17, 5, 0⟩)
  · execute fm 86
  apply progress_nonhalt (fm := fm)
    (P := fun q ↦ ∃ n r, q = ⟨0, 0, r + 3 * n + 16, n + 5, 0⟩)
  · intro q ⟨n, r, hq⟩; subst hq
    exact ⟨⟨0, 0, r + 4 * n + 22, n + 6, 0⟩,
           ⟨n + 1, r + n + 3, by ring_nf⟩,
           main_trans n r⟩
  · exact ⟨0, 1, by ring_nf⟩

end Sz22_2003_unofficial_358
