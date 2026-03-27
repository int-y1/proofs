import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #423: [27/10, 55/21, 2/3, 7/11, 99/2]

Vector representation:
```
-1  3 -1  0  0
 0 -1  1 -1  1
 1 -1  0  0  0
 0  0  0  1 -1
-1  2  0  0  1
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_423

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a+1, b, c+1, d, e⟩ => some ⟨a, b+3, c, d, e⟩
  | ⟨a, b+1, c, d+1, e⟩ => some ⟨a, b, c+1, d, e+1⟩
  | ⟨a, b+1, c, d, e⟩ => some ⟨a+1, b, c, d, e⟩
  | ⟨a, b, c, d, e+1⟩ => some ⟨a, b, c, d+1, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b+2, c, d, e+1⟩
  | _ => none

-- R2,R1 loop: each pair consumes 1 from a and d, adds 2 to b, adds 1 to e
theorem r2r1_loop : ∀ j, ∀ a b d e,
    ⟨a+j, b+2, 0, d+j, e+1⟩ [fm]⊢* ⟨a, b+2+2*j, 0, d, e+1+j⟩ := by
  intro j; induction' j with j ih <;> intro a b d e
  · exists 0
  rw [show a + (j + 1) = (a + j) + 1 from by ring,
      show d + (j + 1) = (d + j) + 1 from by ring]
  step fm; step fm
  apply stepStar_trans (ih _ _ _ _)
  ring_nf; finish

-- R3 chain: transfer b to a
theorem r3_chain : ∀ j, ∀ a b e,
    ⟨a, b+j, 0, 0, e⟩ [fm]⊢* ⟨a+j, b, 0, 0, e⟩ := by
  intro j; induction' j with j ih <;> intro a b e
  · exists 0
  rw [show b + (j + 1) = (b + j) + 1 from by ring]
  step fm
  apply stepStar_trans (ih _ _ _)
  ring_nf; finish

-- R4 chain: transfer e to d
theorem r4_chain : ∀ j, ∀ a d e,
    ⟨a, 0, 0, d, e+j⟩ [fm]⊢* ⟨a, 0, 0, d+j, e⟩ := by
  intro j; induction' j with j ih <;> intro a d e
  · exists 0
  rw [show e + (j + 1) = (e + j) + 1 from by ring]
  step fm
  apply stepStar_trans (ih _ _ _)
  ring_nf; finish

-- Full cycle: (a+n+2, 0, 0, n+1, 0) ⊢⁺ (a+2*n+4, 0, 0, n+2, 0)
theorem main_trans (a n : ℕ) :
    ⟨a+n+2, 0, 0, n+1, 0⟩ [fm]⊢⁺ ⟨a+2*n+4, 0, 0, n+2, 0⟩ := by
  -- Phase 1: R5 step
  apply step_stepStar_stepPlus
  · show fm ⟨a+n+2, 0, 0, n+1, 0⟩ = some ⟨a+n+1, 2, 0, n+1, 1⟩
    simp [fm]
  -- Phase 2: R2,R1 loop (n+1) times
  apply stepStar_trans
  · have h := r2r1_loop (n+1) a 0 0 0
    simp only [(by ring : 0 + 2 = 2), (by ring : 0 + 1 = 1)] at h
    rw [show a + (n + 1) = a + n + 1 from by ring,
        show 0 + (n + 1) = n + 1 from by ring,
        show 2 + 2 * (n + 1) = 2 * n + 4 from by ring,
        show 1 + (n + 1) = n + 2 from by ring] at h
    exact h
  -- Phase 3: R3 chain (2*n+4) times
  apply stepStar_trans
  · have h := r3_chain (2*n+4) a 0 (n+2)
    rw [show 0 + (2 * n + 4) = 2 * n + 4 from by ring,
        show a + (2 * n + 4) = a + 2 * n + 4 from by ring] at h
    exact h
  -- Phase 4: R4 chain (n+2) times
  have h := r4_chain (n+2) (a+2*n+4) 0 0
  simp only [(by ring : 0 + (n + 2) = n + 2)] at h
  exact h

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨4, 0, 0, 2, 0⟩) (by execute fm 13)
  apply progress_nonhalt_simple (fm := fm) (A := ℕ × ℕ)
    (fun ⟨a, n⟩ ↦ ⟨a + n + 2, 0, 0, n + 1, 0⟩) ⟨1, 1⟩
  intro ⟨a, n⟩
  exact ⟨⟨a + n + 1, n + 1⟩, by
    show ⟨a+n+2, 0, 0, n+1, 0⟩ [fm]⊢⁺ ⟨(a+n+1)+(n+1)+2, 0, 0, (n+1)+1, 0⟩
    have h := main_trans a n
    rw [show a + 2 * n + 4 = (a + n + 1) + (n + 1) + 2 from by ring,
        show n + 2 = (n + 1) + 1 from by ring] at h
    exact h⟩

end Sz22_2003_unofficial_423
