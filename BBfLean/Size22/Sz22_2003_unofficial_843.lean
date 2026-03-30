import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #843: [36/35, 5/22, 343/2, 11/3, 5/7]

Vector representation:
```
 2  2 -1 -1  0
-1  0  1  0 -1
-1  0  0  3  0
 0 -1  0  0  1
 0  0  1 -1  0
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_843

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a, b, c+1, d+1, e⟩ => some ⟨a+2, b+2, c, d, e⟩
  | ⟨a+1, b, c, d, e+1⟩ => some ⟨a, b, c+1, d, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b, c, d+3, e⟩
  | ⟨a, b+1, c, d, e⟩ => some ⟨a, b, c, d, e+1⟩
  | ⟨a, b, c, d+1, e⟩ => some ⟨a, b, c+1, d, e⟩
  | _ => none

-- R2+R1 interleave: k rounds
-- Each round: R2 (a→a-1, c→c+1, e→e-1) then R1 (a→a+2, b→b+2, c→c-1, d→d-1)
-- Net per round: a→a+1, b→b+2, d→d-1, e→e-1
theorem r2r1_chain : ∀ k, ∀ a b d, ⟨a + 1, b, 0, d + k, k⟩ [fm]⊢* ⟨a + k + 1, b + 2 * k, 0, d, 0⟩ := by
  intro k; induction' k with k ih <;> intro a b d
  · exists 0
  · rw [show d + (k + 1) = (d + k) + 1 from by ring]
    step fm  -- R2
    step fm  -- R1
    rw [show a + 2 = (a + 1) + 1 from by ring]
    apply stepStar_trans (ih (a + 1) (b + 2) d)
    ring_nf; finish

-- R3 chain: convert a to d
theorem r3_chain : ∀ k, ∀ b d, ⟨k, b, 0, d, 0⟩ [fm]⊢* ⟨0, b, 0, d + 3 * k, 0⟩ := by
  intro k; induction' k with k ih <;> intro b d
  · exists 0
  · step fm
    apply stepStar_trans (ih b (d + 3))
    ring_nf; finish

-- R4 chain: convert b to e
theorem r4_chain : ∀ k, ∀ d e, ⟨0, k, 0, d, e⟩ [fm]⊢* ⟨0, 0, 0, d, e + k⟩ := by
  intro k; induction' k with k ih <;> intro d e
  · exists 0
  · step fm
    apply stepStar_trans (ih d (e + 1))
    ring_nf; finish

-- Main transition: (0, 0, 0, e+m+2, e) ⊢⁺ (0, 0, 0, m+3*e+6, 2*e+2)
theorem main_trans (m e : ℕ) : ⟨0, 0, 0, e + m + 2, e⟩ [fm]⊢⁺ ⟨0, 0, 0, m + 3 * e + 6, 2 * e + 2⟩ := by
  -- R5: (0, 0, 1, e+m+1, e)
  rw [show e + m + 2 = (e + m + 1) + 1 from by ring]
  step fm
  -- R1: (2, 2, 0, e+m, e)
  rw [show e + m + 1 = (e + m) + 1 from by ring]
  step fm
  -- After step fm twice, goal should be (2, 2, 0, e+m, e) ⊢* ...
  -- We need to match r2r1_chain: (a+1, b, 0, d+k, k) with a=1, b=2, d=m, k=e
  -- That gives (1+1, 2, 0, m+e, e) = (2, 2, 0, m+e, e)
  -- But our state is (2, 2, 0, e+m, e). Need to commute e+m to m+e.
  rw [show e + m = m + e from by ring]
  apply stepStar_trans (r2r1_chain e 1 2 m)
  -- Now at (1+e+1, 2+2*e, 0, m, 0) = (e+2, 2*e+2, 0, m, 0)
  -- R3 chain: (e+2) rounds
  rw [show 1 + e + 1 = e + 2 from by ring,
      show 2 + 2 * e = 2 * e + 2 from by ring]
  apply stepStar_trans (r3_chain (e + 2) (2 * e + 2) m)
  -- R4 chain: (2*e+2) rounds
  rw [show m + 3 * (e + 2) = m + 3 * e + 6 from by ring]
  apply stepStar_trans (r4_chain (2 * e + 2) (m + 3 * e + 6) 0)
  ring_nf; finish

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨0, 0, 0, 3, 0⟩)
  · execute fm 1
  apply progress_nonhalt (fm := fm)
    (P := fun q ↦ ∃ m e, q = ⟨0, 0, 0, e + m + 2, e⟩)
  · intro c ⟨m, e, hq⟩; subst hq
    refine ⟨⟨0, 0, 0, m + 3 * e + 6, 2 * e + 2⟩, ?_, main_trans m e⟩
    exact ⟨m + e + 2, 2 * e + 2, by ring_nf⟩
  · exact ⟨1, 0, by ring_nf⟩

end Sz22_2003_unofficial_843
