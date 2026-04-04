import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #1736: [8/15, 33/14, 55/2, 7/11, 3/7]

Vector representation:
```
 3 -1 -1  0  0
-1  1  0 -1  1
-1  0  1  0  1
 0  0  0  1 -1
 0  1  0 -1  0
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_1736

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a, b+1, c+1, d, e⟩ => some ⟨a+3, b, c, d, e⟩
  | ⟨a+1, b, c, d+1, e⟩ => some ⟨a, b+1, c, d, e+1⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b, c+1, d, e+1⟩
  | ⟨a, b, c, d, e+1⟩ => some ⟨a, b, c, d+1, e⟩
  | ⟨a, b, c, d+1, e⟩ => some ⟨a, b+1, c, d, e⟩
  | _ => none

theorem r3_chain : ∀ k a c e, ⟨a + k, 0, c, 0, e⟩ [fm]⊢* ⟨a, 0, c + k, 0, e + k⟩ := by
  intro k; induction' k with k ih <;> intro a c e
  · exists 0
  · rw [show a + (k + 1) = a + k + 1 from by ring]
    step fm; apply stepStar_trans (ih a (c + 1) (e + 1)); ring_nf; finish

theorem r4_chain : ∀ k c d e, ⟨0, 0, c, d, e + k⟩ [fm]⊢* ⟨0, 0, c, d + k, e⟩ := by
  intro k; induction' k with k ih <;> intro c d e
  · exists 0
  · rw [show e + (k + 1) = e + k + 1 from by ring]
    step fm
    rw [show d + (k + 1) = (d + 1) + k from by ring]
    exact ih c (d + 1) e

theorem r2r1_chain : ∀ k A c d E, ⟨A + 1, 0, c + k, d + k, E⟩ [fm]⊢*
    ⟨A + 2 * k + 1, 0, c, d, E + k⟩ := by
  intro k; induction' k with k ih <;> intro A c d E
  · ring_nf; exists 0
  · rw [show c + (k + 1) = c + k + 1 from by ring,
        show d + (k + 1) = d + k + 1 from by ring]
    step fm; step fm
    rw [show A + 2 * (k + 1) + 1 = (A + 2) + 2 * k + 1 from by ring,
        show E + (k + 1) = (E + 1) + k from by ring]
    exact ih (A + 2) c d (E + 1)

theorem r2_drain : ∀ k A b E, ⟨A + k, b, 0, k, E⟩ [fm]⊢* ⟨A, b + k, 0, 0, E + k⟩ := by
  intro k; induction' k with k ih <;> intro A b E
  · exists 0
  · rw [show A + (k + 1) = A + k + 1 from by ring]
    step fm
    rw [show b + (k + 1) = (b + 1) + k from by ring,
        show E + (k + 1) = (E + 1) + k from by ring]
    exact ih A (b + 1) (E + 1)

theorem r3r1_chain : ∀ k A E, ⟨A + 1, k + 1, 0, 0, E⟩ [fm]⊢*
    ⟨A + 2 * k + 3, 0, 0, 0, E + k + 1⟩ := by
  intro k; induction' k with k ih <;> intro A E
  · step fm; step fm; finish
  · step fm; step fm
    rw [show A + 2 * (k + 1) + 3 = (A + 2) + 2 * k + 3 from by ring,
        show E + (k + 1) + 1 = (E + 1) + k + 1 from by ring]
    exact ih (A + 2) (E + 1)

theorem main_trans (n e : ℕ) :
    ⟨e + 2 * n + 1, 0, 0, 0, e⟩ [fm]⊢⁺ ⟨3 * e + 4 * n + 3, 0, 0, 0, 3 * e + 2 * n⟩ := by
  -- Phase 1: first R3 step (provides ⊢⁺)
  rw [show e + 2 * n + 1 = e + 2 * n + 1 from rfl]
  apply step_stepStar_stepPlus
  · show ⟨e + 2 * n + 1, 0, 0, 0, e⟩ [fm]⊢ ⟨e + 2 * n, 0, 1, 0, e + 1⟩
    simp [fm]
  -- R3 chain: remaining e+2n steps
  rw [show e + 2 * n = 0 + (e + 2 * n) from by ring]
  apply stepStar_trans (r3_chain (e + 2 * n) 0 1 (e + 1))
  -- (0, 0, e+2n+1, 0, 2e+2n+1)
  rw [show 1 + (e + 2 * n) = e + 2 * n + 1 from by ring,
      show e + 1 + (e + 2 * n) = 0 + (2 * e + 2 * n + 1) from by ring]
  -- Phase 2: R4 chain
  apply stepStar_trans (r4_chain (2 * e + 2 * n + 1) (e + 2 * n + 1) 0 0)
  rw [show (0 : ℕ) + (2 * e + 2 * n + 1) = 2 * e + 2 * n + 1 from by ring]
  -- R5 + R1
  step fm; step fm
  -- (3, 0, e+2n, 2e+2n, 0)
  show ⟨3, 0, e + 2 * n, 2 * e + 2 * n, 0⟩ [fm]⊢* _
  -- Phase 3: R2+R1 chain (e+2n steps)
  rw [show (3 : ℕ) = 2 + 1 from by ring,
      show e + 2 * n = 0 + (e + 2 * n) from by ring,
      show 2 * e + 2 * n = e + (e + 2 * n) from by ring]
  apply stepStar_trans (r2r1_chain (e + 2 * n) 2 0 e 0)
  -- (2e+4n+3, 0, 0, e, e+2n)
  rw [show 2 + 2 * (e + 2 * n) + 1 = (e + 4 * n + 3) + e from by ring,
      show (0 : ℕ) + (e + 2 * n) = e + 2 * n from by ring]
  -- Phase 4: R2 drain (e steps)
  apply stepStar_trans (r2_drain e (e + 4 * n + 3) 0 (e + 2 * n))
  rw [show (0 : ℕ) + e = e from by ring,
      show e + 2 * n + e = 2 * e + 2 * n from by ring]
  -- (e+4n+3, e, 0, 0, 2e+2n)
  -- Phase 5: R3+R1 chain (e steps)
  rcases e with _ | e
  · -- e = 0: already at target
    ring_nf; finish
  · -- e ≥ 1
    rw [show e + 1 + 4 * n + 3 = (e + 4 * n + 3) + 1 from by ring,
        show 3 * (e + 1) + 4 * n + 3 = (e + 4 * n + 3) + 2 * e + 3 from by ring,
        show 3 * (e + 1) + 2 * n = 2 * (e + 1) + 2 * n + e + 1 from by ring]
    exact r3r1_chain e (e + 4 * n + 3) (2 * (e + 1) + 2 * n)

theorem nonhalt : ¬halts fm c₀ := by
  apply progress_nonhalt_simple (fm := fm) (A := ℕ × ℕ)
    (fun ⟨n, e⟩ ↦ ⟨e + 2 * n + 1, 0, 0, 0, e⟩) ⟨0, 0⟩
  intro ⟨n, e⟩
  refine ⟨⟨n + 1, 3 * e + 2 * n⟩, ?_⟩
  show ⟨e + 2 * n + 1, 0, 0, 0, e⟩ [fm]⊢⁺ ⟨3 * e + 2 * n + 2 * (n + 1) + 1, 0, 0, 0, 3 * e + 2 * n⟩
  rw [show 3 * e + 2 * n + 2 * (n + 1) + 1 = 3 * e + 4 * n + 3 from by ring]
  exact main_trans n e

end Sz22_2003_unofficial_1736
