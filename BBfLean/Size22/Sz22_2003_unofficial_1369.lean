import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #1369: [63/10, 4/77, 121/2, 5/3, 35/11]

Vector representation:
```
-1  2 -1  1  0
 2  0  0 -1 -1
-1  0  0  0  2
 0 -1  1  0  0
 0  0  1  1 -1
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_1369

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a+1, b, c+1, d, e⟩ => some ⟨a, b+2, c, d+1, e⟩
  | ⟨a, b, c, d+1, e+1⟩ => some ⟨a+2, b, c, d, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b, c, d, e+2⟩
  | ⟨a, b+1, c, d, e⟩ => some ⟨a, b, c+1, d, e⟩
  | ⟨a, b, c, d, e+1⟩ => some ⟨a, b, c+1, d+1, e⟩
  | _ => none

-- R3 drain: (k, b, 0, 0, e) ⊢* (0, b, 0, 0, e+2*k)
theorem r3_drain : ∀ k b e, ⟨k, b, 0, 0, e⟩ [fm]⊢* ⟨0, b, 0, 0, e + 2 * k⟩ := by
  intro k; induction' k with k ih <;> intro b e
  · exists 0
  · step fm
    apply stepStar_trans (ih b (e + 2))
    ring_nf; finish

-- R4 drain: (0, k, c, 0, e) ⊢* (0, 0, c+k, 0, e)
theorem r4_drain : ∀ k c e, ⟨0, k, c, 0, e⟩ [fm]⊢* ⟨0, 0, c + k, 0, e⟩ := by
  intro k; induction' k with k ih <;> intro c e
  · exists 0
  · step fm
    apply stepStar_trans (ih (c + 1) e)
    ring_nf; finish

-- R1R1R2 interleaved chain:
-- (2, b, 2*k+1, d, e+k) ⊢* (2, b+4*k, 1, d+k, e)
theorem r1r1r2_chain : ∀ k b d e,
    ⟨2, b, 2 * k + 1, d, e + k⟩ [fm]⊢* ⟨2, b + 4 * k, 1, d + k, e⟩ := by
  intro k; induction' k with k ih <;> intro b d e
  · exists 0
  · rw [show 2 * (k + 1) + 1 = (2 * k + 1) + 2 from by ring,
        show e + (k + 1) = (e + k) + 1 from by ring]
    step fm; step fm; step fm
    apply stepStar_trans (ih (b + 4) (d + 1) e)
    ring_nf; finish

-- Combined R2/R3 drain: from (a, b, 0, d, e) to (0, b, 0, 0, 2*a+3*d+e).
-- By mutual induction on d: part 1 handles e >= 1, part 2 handles e = 0 with a >= 1.
theorem drain_combined : ∀ d,
    (∀ a b e, ⟨a, b, 0, d, e + 1⟩ [fm]⊢* ⟨0, b, 0, 0, 2 * a + 3 * d + e + 1⟩) ∧
    (∀ a b, ⟨a + 1, b, 0, d, 0⟩ [fm]⊢* ⟨0, b, 0, 0, 2 * a + 3 * d + 2⟩) := by
  intro d; induction' d with d ih <;> constructor
  · intro a b e
    rw [show 2 * a + 3 * 0 + e + 1 = (e + 1) + 2 * a from by ring]
    exact r3_drain a b (e + 1)
  · intro a b
    rw [show 2 * a + 3 * 0 + 2 = 0 + 2 * (a + 1) from by ring]
    exact r3_drain (a + 1) b 0
  · intro a b e
    rcases e with _ | e'
    · -- e=0: state is (a, b, 0, d+1, 1). R2 -> (a+2, b, 0, d, 0). Use ih.2.
      step fm
      apply stepStar_trans (ih.2 (a + 1) b)
      ring_nf; finish
    · -- e=e'+1: state is (a, b, 0, d+1, e'+2). R2 -> (a+2, b, 0, d, e'+1). Use ih.1.
      rw [show (e' + 1 : ℕ) + 1 = (e' + 1) + 1 from rfl]
      step fm
      apply stepStar_trans (ih.1 (a + 2) b e')
      ring_nf; finish
  · intro a b
    -- state is (a+1, b, 0, d+1, 0). R3 -> (a, b, 0, d+1, 2). R2 -> (a+2, b, 0, d, 1). Use ih.1.
    step fm; step fm
    apply stepStar_trans (ih.1 (a + 2) b 0)
    ring_nf; finish

-- Main transition: (0, 0, 2m+2, 0, 2m+n+5) ⊢⁺ (0, 0, 4m+6, 0, 4m+n+10)
theorem main_trans (m n : ℕ) :
    ⟨0, 0, 2 * m + 2, 0, 2 * m + n + 5⟩ [fm]⊢⁺ ⟨0, 0, 4 * m + 6, 0, 4 * m + n + 10⟩ := by
  -- Phase 1 (R5): (0, 0, 2m+2, 0, 2m+n+5) -> (0, 0, 2m+3, 1, 2m+n+4)
  rw [show 2 * m + n + 5 = (2 * m + n + 4) + 1 from by ring]
  step fm
  -- Phase 2 (R2): (0, 0, 2m+3, 1, 2m+n+4) -> (2, 0, 2m+3, 0, 2m+n+3)
  rw [show 2 * m + n + 4 = (2 * m + n + 3) + 1 from by ring]
  step fm
  -- Phase 3 (R1R1R2 chain, k=m+1): (2, 0, 2m+3, 0, 2m+n+3) -> (2, 4m+4, 1, m+1, m+n+2)
  rw [show (2 : ℕ) * m + 3 = 2 * (m + 1) + 1 from by ring,
      show (2 : ℕ) * m + n + 3 = (m + n + 2) + (m + 1) from by ring]
  apply stepStar_trans (r1r1r2_chain (m + 1) 0 0 (m + n + 2))
  -- Phase 4 (R1): (2, 4m+4, 1, m+1, m+n+2) -> (1, 4m+6, 0, m+2, m+n+2)
  rw [show 0 + 4 * (m + 1) = 4 * m + 4 from by ring,
      show 0 + (m + 1) = m + 1 from by ring]
  step fm
  -- Phase 5 (drain): (1, 4m+6, 0, m+2, m+n+2)
  -- Use drain_combined.1 with a=1, d=m+2, e=m+n+1 (so e+1 = m+n+2)
  rw [show (m : ℕ) + n + 2 = (m + n + 1) + 1 from by ring]
  apply stepStar_trans ((drain_combined (m + 2)).1 1 (4 * m + 6) (m + n + 1))
  -- Result: (0, 4m+6, 0, 0, 2*1 + 3*(m+2) + (m+n+1) + 1) = (0, 4m+6, 0, 0, 4m+n+10)
  -- Phase 6 (R4 drain): (0, 4m+6, 0, 0, 4m+n+10) -> (0, 0, 4m+6, 0, 4m+n+10)
  rw [show 2 * 1 + 3 * (m + 2) + (m + n + 1) + 1 = 4 * m + n + 10 from by ring]
  apply stepStar_trans (r4_drain (4 * m + 6) 0 (4 * m + n + 10))
  ring_nf; finish

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨0, 0, 2, 0, 5⟩)
  · execute fm 10
  apply progress_nonhalt_simple (fm := fm) (A := ℕ × ℕ)
    (fun p ↦ ⟨0, 0, 2 * p.1 + 2, 0, 2 * p.1 + p.2 + 5⟩) ⟨0, 0⟩
  intro ⟨m, n⟩
  refine ⟨⟨2 * (m + 1), n + 1⟩, ?_⟩
  show ⟨0, 0, 2 * m + 2, 0, 2 * m + n + 5⟩ [fm]⊢⁺
       ⟨0, 0, 2 * (2 * (m + 1)) + 2, 0, 2 * (2 * (m + 1)) + (n + 1) + 5⟩
  rw [show 2 * (2 * (m + 1)) + 2 = 4 * m + 6 from by ring,
      show 2 * (2 * (m + 1)) + (n + 1) + 5 = 4 * m + n + 10 from by ring]
  exact main_trans m n

end Sz22_2003_unofficial_1369
