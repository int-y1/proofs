import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #1268: [5/6, 99/35, 4/5, 7/11, 275/2]

Vector representation:
```
-1 -1  1  0  0
 0  2 -1 -1  1
 2  0 -1  0  0
 0  0  0  1 -1
-1  0  2  0  1
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_1268

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a+1, b+1, c, d, e⟩ => some ⟨a, b, c+1, d, e⟩
  | ⟨a, b, c+1, d+1, e⟩ => some ⟨a, b+2, c, d, e+1⟩
  | ⟨a, b, c+1, d, e⟩ => some ⟨a+2, b, c, d, e⟩
  | ⟨a, b, c, d, e+1⟩ => some ⟨a, b, c, d+1, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b, c+2, d, e+1⟩
  | _ => none

-- R2/R1/R1 chain: k rounds
theorem r2r1r1_chain : ∀ k a c e, ⟨a + 2 * k, (0 : ℕ), c + 1, k, e⟩ [fm]⊢* ⟨a, (0 : ℕ), c + k + 1, (0 : ℕ), e + k⟩ := by
  intro k; induction' k with k ih <;> intro a c e
  · simp; exists 0
  · -- State: (a + 2*(k+1), 0, c+1, k+1, e)
    -- Need to rewrite to expose successors for step fm
    rw [show a + 2 * (k + 1) = (a + 2 * k) + 2 from by ring]
    -- R2: needs c+1 and d+1 = k+1
    step fm
    -- State: (a+2k+2, 2, c, k, e+1)
    -- R1: needs a+1 and b+1
    rw [show (a + 2 * k) + 2 = ((a + 2 * k) + 1) + 1 from by ring]
    step fm
    -- State: (a+2k+1, 1, c+1, k, e+1)
    step fm
    -- State: (a+2k, 0, c+2, k, e+1)
    rw [show c + 2 = (c + 1) + 1 from by ring]
    apply stepStar_trans (ih a (c + 1) (e + 1))
    rw [show c + 1 + k + 1 = c + (k + 1) + 1 from by ring,
        show e + 1 + k = e + (k + 1) from by ring]
    finish

-- R3 chain: k rounds (b=0, d=0)
theorem r3_chain : ∀ k a c e, ⟨a, (0 : ℕ), c + k, (0 : ℕ), e⟩ [fm]⊢* ⟨a + 2 * k, (0 : ℕ), c, (0 : ℕ), e⟩ := by
  intro k; induction' k with k ih <;> intro a c e
  · exists 0
  · rw [show c + (k + 1) = (c + k) + 1 from by ring]
    step fm
    apply stepStar_trans (ih (a + 2) c e)
    rw [show a + 2 + 2 * k = a + 2 * (k + 1) from by ring]
    finish

-- R4 chain: k rounds (b=0, c=0)
theorem r4_chain : ∀ k a d e, ⟨a, (0 : ℕ), (0 : ℕ), d, e + k⟩ [fm]⊢* ⟨a, (0 : ℕ), (0 : ℕ), d + k, e⟩ := by
  intro k; induction' k with k ih <;> intro a d e
  · exists 0
  · rw [show e + (k + 1) = (e + k) + 1 from by ring]
    step fm
    apply stepStar_trans (ih a (d + 1) e)
    rw [show d + 1 + k = d + (k + 1) from by ring]
    finish

-- Main transition: (3n+1, 0, 0, n, 0) ->+ (3n+4, 0, 0, n+1, 0)
theorem main_transition (n : ℕ) :
    ⟨3 * n + 1, (0 : ℕ), (0 : ℕ), n, (0 : ℕ)⟩ [fm]⊢⁺
    ⟨3 * n + 4, (0 : ℕ), (0 : ℕ), n + 1, (0 : ℕ)⟩ := by
  -- R5: (3n+1, 0, 0, n, 0) -> (3n, 0, 2, n, 1)
  rw [show 3 * n + 1 = (3 * n) + 1 from by ring]
  apply step_stepStar_stepPlus
    (by simp [fm] : (⟨(3 * n) + 1, 0, 0, n, 0⟩ : Q) [fm]⊢ ⟨3 * n, 0, 2, n, 1⟩)
  -- R2/R1/R1 chain: n rounds
  -- State: (3n, 0, 2, n, 1) = (n + 2*n, 0, 1+1, n, 1)
  rw [show 3 * n = n + 2 * n from by ring]
  apply stepStar_trans (r2r1r1_chain n n 1 1)
  -- Result: (n, 0, 1+n+1, 0, 1+n) = (n, 0, n+2, 0, n+1)
  -- R3 chain: n+2 rounds
  rw [show 1 + n + 1 = 0 + (n + 2) from by ring,
      show 1 + n = n + 1 from by ring]
  apply stepStar_trans (r3_chain (n + 2) n 0 (n + 1))
  -- Result: (n + 2*(n+2), 0, 0, 0, n+1) = (3n+4, 0, 0, 0, n+1)
  -- R4 chain: n+1 rounds
  rw [show n + 2 * (n + 2) = 3 * n + 4 from by ring,
      show n + 1 = 0 + (n + 1) from by ring]
  apply stepStar_trans (r4_chain (n + 1) (3 * n + 4) 0 0)
  rw [show 0 + (n + 1) = n + 1 from by ring]
  ring_nf; finish

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨4, 0, 0, 1, 0⟩) (by execute fm 4)
  apply progress_nonhalt_simple (fm := fm) (A := ℕ)
    (fun n ↦ ⟨3 * (n + 1) + 1, 0, 0, n + 1, 0⟩) 0
  intro n
  exists n + 1
  show ⟨3 * (n + 1) + 1, (0 : ℕ), (0 : ℕ), n + 1, (0 : ℕ)⟩ [fm]⊢⁺
       ⟨3 * (n + 2) + 1, (0 : ℕ), (0 : ℕ), n + 2, (0 : ℕ)⟩
  have h := main_transition (n + 1)
  rw [show 3 * (n + 1) + 4 = 3 * (n + 2) + 1 from by ring] at h
  exact h

end Sz22_2003_unofficial_1268
