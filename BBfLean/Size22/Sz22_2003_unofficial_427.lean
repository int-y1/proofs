import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #427: [27/10, 55/21, 44/3, 7/11, 3/2]

Vector representation:
```
-1  3 -1  0  0
 0 -1  1 -1  1
 2 -1  0  0  1
 0  0  0  1 -1
-1  1  0  0  0
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_427

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a+1, b, c+1, d, e⟩ => some ⟨a, b+3, c, d, e⟩
  | ⟨a, b+1, c, d+1, e⟩ => some ⟨a, b, c+1, d, e+1⟩
  | ⟨a, b+1, c, d, e⟩ => some ⟨a+2, b, c, d, e+1⟩
  | ⟨a, b, c, d, e+1⟩ => some ⟨a, b, c, d+1, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b+1, c, d, e⟩
  | _ => none

-- (R2,R1) loop: each iteration does R2 then R1, consuming one unit of d and a
-- (a+j, b+1, 0, j, e) →* (a, b+2*j+1, 0, 0, e+j)
theorem r2r1_loop : ∀ j, ∀ a b e,
    ⟨a+j, b+1, 0, j, e⟩ [fm]⊢* ⟨a, b+2*j+1, 0, 0, e+j⟩ := by
  intro j; induction j with
  | zero => intro a b e; exists 0
  | succ j ih =>
    intro a b e
    rw [show a + (j + 1) = (a + j) + 1 from by ring,
        show b + 1 = b + 1 from rfl,
        show j + 1 = j + 1 from rfl]
    -- R2: (a+j+1, b+1, 0, j+1, e) → ((a+j)+1, b, 1, j, e+1)
    -- need b+1 >= 1 ✓ and j+1 >= 1 ✓
    -- But R1 checks a >= 1 and c >= 1 first. Here a+j+1 >= 1 and c=0, so R1 doesn't apply.
    -- R2: match on b+1 and d+1: ⟨(a+j)+1, (b)+1, 0, (j)+1, e⟩ → ⟨(a+j)+1, b, 1, j, e+1⟩
    -- Wait, but R1 pattern is ⟨a'+1, b', c'+1, d', e'⟩. Here c=0 so R1 doesn't match.
    step fm
    -- Now at ((a+j)+1, b, 1, j, e+1)
    -- R1 matches: ⟨(a+j)+1, b, 1, j, e+1⟩ = ⟨(a+j)+1, b, 0+1, j, e+1⟩
    -- → ⟨a+j, b+3, 0, j, e+1⟩
    rw [show (a + j) + 1 = a + j + 1 from by ring]
    step fm
    -- Now at (a+j, b+3, 0, j, e+1)
    -- ih: (a+j, (b+2)+1, 0, j, e+1) →* (a, (b+2)+2*j+1, 0, 0, (e+1)+j)
    apply stepStar_trans (ih a (b+2) (e+1))
    ring_nf; finish

-- R3 chain: consume b, grow a and e
-- (a, j, 0, 0, e) →* (a+2*j, 0, 0, 0, e+j)
theorem r3_chain : ∀ j, ∀ a e,
    ⟨a, j, 0, 0, e⟩ [fm]⊢* ⟨a+2*j, 0, 0, 0, e+j⟩ := by
  intro j; induction j with
  | zero => intro a e; exists 0
  | succ j ih =>
    intro a e
    -- (a, j+1, 0, 0, e): b = j+1 >= 1, d = 0, so R3 applies
    -- R1: need a >= 1 and c >= 1. c=0, so R1 doesn't apply.
    -- R2: need b >= 1 and d >= 1. d=0, so R2 doesn't apply.
    -- R3: ⟨a, (j)+1, 0, 0, e⟩ → ⟨a+2, j, 0, 0, e+1⟩
    rw [show j + 1 = j + 1 from rfl]
    step fm
    apply stepStar_trans (ih (a+2) (e+1))
    ring_nf; finish

-- R4 chain: transfer e to d
-- (a, 0, 0, d, j) →* (a, 0, 0, d+j, 0)
theorem r4_chain : ∀ j, ∀ a d,
    ⟨a, 0, 0, d, j⟩ [fm]⊢* ⟨a, 0, 0, d+j, 0⟩ := by
  intro j; induction j with
  | zero => intro a d; exists 0
  | succ j ih =>
    intro a d
    rw [show j + 1 = j + 1 from rfl]
    step fm
    apply stepStar_trans (ih a (d+1))
    ring_nf; finish

-- Main transition: (a+d+1, 0, 0, d, 0) ⊢⁺ (a+4*d+2, 0, 0, 3*d+1, 0)
theorem main_trans (a d : ℕ) :
    ⟨a+d+1, 0, 0, d, 0⟩ [fm]⊢⁺ ⟨a+4*d+2, 0, 0, 3*d+1, 0⟩ := by
  -- R5: (a+d+1, 0, 0, d, 0) → (a+d, 1, 0, d, 0)
  apply step_stepStar_stepPlus (c₂ := ⟨a+d, 1, 0, d, 0⟩)
  · rw [show a + d + 1 = (a + d) + 1 from by ring]; simp [fm]
  -- Phase 1: r2r1_loop d times
  -- (a+d, 1, 0, d, 0) = (a+d, 0+1, 0, d, 0) →* (a, 0+2*d+1, 0, 0, 0+d) = (a, 2*d+1, 0, 0, d)
  apply stepStar_trans
  · have h := r2r1_loop d a 0 0
    simp only [Nat.zero_add] at h
    exact h
  -- Phase 2: r3_chain (2*d+1) times
  -- (a, 2*d+1, 0, 0, d) →* (a+2*(2*d+1), 0, 0, 0, d+(2*d+1)) = (a+4*d+2, 0, 0, 0, 3*d+1)
  apply stepStar_trans
  · have h := r3_chain (2*d+1) a d
    rw [show a + 2 * (2 * d + 1) = a + 4 * d + 2 from by ring,
        show d + (2 * d + 1) = 3 * d + 1 from by ring] at h
    exact h
  -- Phase 3: r4_chain (3*d+1) times
  -- (a+4*d+2, 0, 0, 0, 3*d+1) →* (a+4*d+2, 0, 0, 3*d+1, 0)
  have h := r4_chain (3*d+1) (a+4*d+2) 0
  simp only [Nat.zero_add] at h
  exact h

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨2, 0, 0, 1, 0⟩) (by execute fm 3)
  -- C(a, d) = (a+d+1, 0, 0, d, 0); start with C(0, 1) = (2, 0, 0, 1, 0)
  -- main_trans: C(a, d) ⊢⁺ C(a+d, 3*d+1)
  apply progress_nonhalt_simple (fm := fm) (A := ℕ × ℕ)
    (fun ⟨a, d⟩ ↦ ⟨a + d + 1, 0, 0, d, 0⟩) ⟨0, 1⟩
  intro ⟨a, d⟩
  refine ⟨⟨a + d, 3 * d + 1⟩, ?_⟩
  show ⟨a + d + 1, 0, 0, d, 0⟩ [fm]⊢⁺ ⟨(a + d) + (3 * d + 1) + 1, 0, 0, 3 * d + 1, 0⟩
  rw [show (a + d) + (3 * d + 1) + 1 = a + 4 * d + 2 from by ring]
  exact main_trans a d

end Sz22_2003_unofficial_427
