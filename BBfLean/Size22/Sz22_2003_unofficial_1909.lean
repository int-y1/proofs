import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #1909: [9/35, 8/5, 55/6, 7/11, 55/2]

Vector representation:
```
 0  2 -1 -1  0
 3  0 -1  0  0
-1 -1  1  0  1
 0  0  0  1 -1
-1  0  1  0  1
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_1909

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a, b, c+1, d+1, e⟩ => some ⟨a, b+2, c, d, e⟩
  | ⟨a, b, c+1, d, e⟩ => some ⟨a+3, b, c, d, e⟩
  | ⟨a+1, b+1, c, d, e⟩ => some ⟨a, b, c+1, d, e+1⟩
  | ⟨a, b, c, d, e+1⟩ => some ⟨a, b, c, d+1, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b, c+1, d, e+1⟩
  | _ => none

-- R4 chain: move e to d
theorem e_to_d : ∀ k d, ⟨a, 0, 0, d, e + k⟩ [fm]⊢* ⟨a, 0, 0, d + k, e⟩ := by
  intro k; induction' k with k ih <;> intro d
  · exists 0
  · rw [show e + (k + 1) = (e + k) + 1 from by ring]
    step fm
    apply stepStar_trans (ih (d + 1))
    ring_nf; finish

-- R1+R3 interleaved chain
-- From (a+k+1, b, 1, k+1, e), do k+1 rounds of R1+R3 to get (a, b+k+1, 1, 0, e+k+1)
-- Each round: R1(c≥1,d≥1) then R3(a≥1,b≥1)
theorem r1r3_chain : ∀ k a b e, ⟨a + k + 1, b, 0 + 1, k + 1, e⟩ [fm]⊢* ⟨a, b + k + 1, 0 + 1, 0, e + k + 1⟩ := by
  intro k; induction' k with k ih <;> intro a b e
  · -- k=0: (a+1, b, 1, 1, e) -> R1 -> (a+1, b+2, 0, 0, e) -> R3 -> (a, b+1, 1, 0, e+1)
    step fm
    step fm
    finish
  · -- k+1: (a+k+2, b, 1, k+2, e) -> R1 -> (a+k+2, b+2, 0, k+1, e)
    --                               -> R3 -> (a+k+1, b+1, 1, k+1, e+1)
    -- Then apply IH with a, b+1, e+1
    rw [show a + (k + 1) + 1 = a + k + 1 + 1 from by ring,
        show (k : ℕ) + 1 + 1 = k + 1 + 1 from rfl]
    step fm
    rw [show b + 2 = (b + 1) + 1 from by ring,
        show a + k + 1 + 1 = (a + k) + 1 + 1 from by ring]
    step fm
    rw [show a + k + 1 = a + (k + 1) from by ring]
    apply stepStar_trans (ih a (b + 1) (e + 1))
    ring_nf; finish

-- R3+R2 chain
theorem r3r2_chain : ∀ k a e, ⟨a + 1, k, 0, 0, e⟩ [fm]⊢* ⟨a + 2 * k + 1, 0, 0, 0, e + k⟩ := by
  intro k; induction' k with k ih <;> intro a e
  · exists 0
  · rw [show (k : ℕ) + 1 = k + 1 from rfl,
        show a + 1 = a + 0 + 1 from by ring]
    step fm
    step fm
    apply stepStar_trans (ih (a + 2) (e + 1))
    ring_nf; finish

-- Main transition
theorem main_trans : ⟨e + F + 2, 0, 0, 0, e + 1⟩ [fm]⊢⁺ ⟨2 * e + F + 5, 0, 0, 0, 2 * e + 3⟩ := by
  -- Phase 1: e_to_d: (e+F+2, 0, 0, 0, e+1) ->* (e+F+2, 0, 0, e+1, 0)
  apply stepStar_stepPlus_stepPlus
  · rw [show (e : ℕ) + 1 = 0 + (e + 1) from by ring]
    exact e_to_d (e + 1) 0 (a := e + F + 2) (e := 0)
  -- Phase 2: R5: (e+F+2, 0, 0, e+1, 0) -> ((e+F+1), 0, 1, e+1, 1)
  rw [show (0 : ℕ) + (e + 1) = e + 1 from by ring]
  apply step_stepStar_stepPlus
  · show ⟨(e + F + 1) + 1, 0, 0, e + 1, 0⟩ [fm]⊢ ⟨e + F + 1, 0, 0 + 1, e + 1, 0 + 1⟩
    simp [fm]
  -- Phase 3: R1+R3 chain (e+1 rounds)
  rw [show e + F + 1 = F + e + 1 from by ring,
      show (0 : ℕ) + 1 = 0 + 1 from rfl]
  apply stepStar_trans (r1r3_chain e F 0 1)
  -- Phase 4: R2
  rw [show (0 : ℕ) + e + 1 = e + 1 from by ring,
      show (1 : ℕ) + e + 1 = e + 2 from by ring]
  step fm
  -- Phase 5: R3+R2 chain
  show ⟨F + 2 + 1, e + 1, 0, 0, e + 2⟩ [fm]⊢* _
  apply stepStar_trans (r3r2_chain (e + 1) (F + 2) (e + 2))
  ring_nf; finish

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨3, 0, 0, 0, 1⟩) (by execute fm 2)
  apply progress_nonhalt_simple (fm := fm) (A := ℕ × ℕ)
    (fun ⟨F, e⟩ ↦ ⟨e + F + 2, 0, 0, 0, e + 1⟩) ⟨1, 0⟩
  intro ⟨F, e⟩
  refine ⟨⟨F + 1, 2 * e + 2⟩, ?_⟩
  show ⟨e + F + 2, 0, 0, 0, e + 1⟩ [fm]⊢⁺ ⟨2 * e + 2 + (F + 1) + 2, 0, 0, 0, 2 * e + 2 + 1⟩
  rw [show 2 * e + 2 + (F + 1) + 2 = 2 * e + F + 5 from by ring,
      show 2 * e + 2 + 1 = 2 * e + 3 from by ring]
  exact main_trans
