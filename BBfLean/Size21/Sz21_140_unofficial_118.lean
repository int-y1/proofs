import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz21_140_unofficial #118: [77/15, 9/14, 2/3, 5/11, 45/2]

Vector representation:
```
 0 -1 -1  1  1
-1  2  0 -1  0
 1 -1  0  0  0
 0  0  1  0 -1
-1  2  1  0  0
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz21_140_unofficial_118

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a, b+1, c+1, d, e⟩ => some ⟨a, b, c, d+1, e+1⟩
  | ⟨a+1, b, c, d+1, e⟩ => some ⟨a, b+2, c, d, e⟩
  | ⟨a, b+1, c, d, e⟩ => some ⟨a+1, b, c, d, e⟩
  | ⟨a, b, c, d, e+1⟩ => some ⟨a, b, c+1, d, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b+2, c+1, d, e⟩
  | _ => none

-- R4 repeated: e → c (when b=0, d=0)
theorem e_to_c : ∀ k, ∀ a c e, ⟨a, 0, c, 0, e+k⟩ [fm]⊢* ⟨a, 0, c+k, 0, e⟩ := by
  intro k; induction' k with k h <;> intro a c e
  · exists 0
  rw [show e + (k + 1) = e + k + 1 from by ring]
  step fm
  apply stepStar_trans (h _ _ _)
  ring_nf; finish

-- R3 repeated: b → a (when c=0, d=0)
theorem b_to_a : ∀ k, ∀ a b e, ⟨a, b+k, 0, 0, e⟩ [fm]⊢* ⟨a+k, b, 0, 0, e⟩ := by
  intro k; induction' k with k h <;> intro a b e
  · exists 0
  rw [show b + (k + 1) = (b + k) + 1 from by ring]
  step fm
  apply stepStar_trans (h _ _ _)
  ring_nf; finish

-- R2 repeated: a,d → b (when c=0)
theorem r2_drain : ∀ k, ∀ a b d e, ⟨a+k, b, 0, d+k, e⟩ [fm]⊢* ⟨a, b+2*k, 0, d, e⟩ := by
  intro k; induction' k with k h <;> intro a b d e
  · exists 0
  rw [show a + (k + 1) = (a + k) + 1 from by ring,
      show d + (k + 1) = (d + k) + 1 from by ring]
  step fm
  apply stepStar_trans (h _ _ _ _)
  ring_nf; finish

-- R1R1R2 chain: k rounds
theorem r1r1r2_chain : ∀ k, ∀ A C D E, ⟨A+k, 2, C+2*k, D, E⟩ [fm]⊢* ⟨A, 2, C, D+k, E+2*k⟩ := by
  intro k; induction' k with k h <;> intro A C D E
  · exists 0
  rw [show A + (k + 1) = (A + k) + 1 from by ring,
      show C + 2 * (k + 1) = (C + 2 * k) + 2 from by ring]
  step fm; step fm; step fm
  apply stepStar_trans (h _ _ _ _)
  ring_nf; finish

-- Drain tail: (A, B, 0, A+1, E) →* (0, B+2*A+2+1, 0, 0, E) via R2×A, R3, R2, giving (0, B+2A+3, 0, 0, E)
-- Actually: R2×A gives (0, B+2A, 0, 1, E), then R3 gives (1, B+2A-1, 0, 1, E), then R2 gives (0, B+2A+1, 0, 0, E)
-- So final b = B+2A+1
theorem drain_tail : ∀ A, ∀ B E, ⟨A, B+1, 0, A+1, E⟩ [fm]⊢* ⟨0, B+2*A+2, 0, 0, E⟩ := by
  intro A; induction' A with A ih <;> intro B E
  · -- A=0: (0, B+1, 0, 1, E) → R3 → (1, B, 0, 1, E) → R2 → (0, B+2, 0, 0, E)
    step fm  -- R3
    rw [show (1:ℕ) = 0 + 1 from by ring, show (1:ℕ) = 0 + 1 from by ring]
    step fm  -- R2
    ring_nf; finish
  · -- A+1: (A+1, B+1, 0, A+2, E) → R2 → (A, B+3, 0, A+1, E)
    rw [show A + 1 + 1 = (A + 1) + 1 from by ring]
    -- R2: need a+1 and d+1. a=A+1≥1 (matches a+1 with a=A), but wait b=B+1≥1 so R3 might match.
    -- R1: b+1=B+1, c+1 needs c≥0 but c=0, so c+1 doesn't match (c=0 is not c+1 form). No.
    -- R2: a+1=A+1+1, d+1=A+2. Both match. But R1 is checked first and needs b+1 and c+1.
    -- b=B+1≥1, but c=0 so R1 doesn't match. R2: a=A+1≥1, d=A+2≥1. R2 matches.
    -- Actually the issue: (A+1, B+1, 0, (A+1)+1, E). R2 pattern: (a+1, b, c, d+1, e).
    -- With a=A, b=B+1, c=0, d=A+1, e=E. But first R1 checks (a, b+1, c+1, d, e).
    -- b+1 needs B+1=b+1 so b=B. c+1 needs 0=c+1 which fails. So R1 doesn't match.
    -- R2: a+1 needs A+1=a+1 so a=A. d+1 needs (A+1)+1=d+1 so d=A+1. Matches.
    -- Result: (A, B+1+2, 0, A+1, E) = (A, B+3, 0, A+1, E)
    step fm
    apply stepStar_trans (ih _ _)
    ring_nf; finish

-- Full transition for n = 2*m+1 (odd case)
theorem main_trans_odd (m : ℕ) : ⟨2*m+2, 0, 0, 0, 2*m+1⟩ [fm]⊢⁺ ⟨2*m+3, 0, 0, 0, 2*m+2⟩ := by
  -- Phase 1: e → c via R4
  apply stepStar_stepPlus_stepPlus (c₂ := ⟨2*m+2, 0, 2*m+1, 0, 0⟩)
  · have := e_to_c (2*m+1) (2*m+2) 0 0
    simp only [Nat.zero_add] at this; exact this
  -- Phase 2: R5 step
  apply step_stepStar_stepPlus (c₂ := ⟨2*m+1, 2, 2*m+2, 0, 0⟩)
  · show fm ⟨(2*m+1)+1, 0, 2*m+1, 0, 0⟩ = some ⟨2*m+1, 0+2, (2*m+1)+1, 0, 0⟩
    simp [fm]
  -- Phase 3: R1R1R2 x (m+1) rounds
  apply stepStar_trans (c₂ := ⟨m, 2, 0, m+1, 2*m+2⟩)
  · have := r1r1r2_chain (m+1) m 0 0 0
    rw [show m + (m + 1) = 2 * m + 1 from by ring,
        show 0 + 2 * (m + 1) = 2 * m + 2 from by ring] at this
    simpa using this
  -- Phase 4: drain_tail with A=m, B=1, E=2m+2
  -- (m, 2, 0, m+1, 2m+2) →* (0, 2m+3, 0, 0, 2m+2)
  -- drain_tail needs (A, B+1, 0, A+1, E) form: A=m, B+1=2 so B=1
  apply stepStar_trans (c₂ := ⟨0, 2*m+3, 0, 0, 2*m+2⟩)
  · have := drain_tail m 1 (2*m+2)
    rw [show 1 + 2 * m + 2 = 2 * m + 3 from by ring] at this
    exact this
  -- Phase 5: R3 x (2m+3)
  have := b_to_a (2*m+3) 0 0 (2*m+2)
  simp only [Nat.zero_add] at this; exact this

-- Full transition for n = 2*m (even case)
theorem main_trans_even (m : ℕ) : ⟨2*m+1, 0, 0, 0, 2*m⟩ [fm]⊢⁺ ⟨2*m+2, 0, 0, 0, 2*m+1⟩ := by
  -- Phase 1: e → c via R4
  apply stepStar_stepPlus_stepPlus (c₂ := ⟨2*m+1, 0, 2*m, 0, 0⟩)
  · have := e_to_c (2*m) (2*m+1) 0 0
    simp only [Nat.zero_add] at this; exact this
  -- Phase 2: R5 step
  apply step_stepStar_stepPlus (c₂ := ⟨2*m, 2, 2*m+1, 0, 0⟩)
  · show fm ⟨2*m+1, 0, 2*m, 0, 0⟩ = some ⟨2*m, 0+2, 2*m+1, 0, 0⟩
    rw [show 2*m+1 = 2*m + 1 from by ring]; simp [fm]
  -- Phase 3: R1R1R2 x m rounds
  apply stepStar_trans (c₂ := ⟨m, 2, 1, m, 2*m⟩)
  · have := r1r1r2_chain m m 1 0 0
    rw [show m + m = 2 * m from by ring,
        show 1 + 2 * m = 2 * m + 1 from by ring] at this
    simpa using this
  -- Phase 4: R1 (one step): (m, 2, 1, m, 2m) → (m, 1, 0, m+1, 2m+1)
  apply stepStar_trans (c₂ := ⟨m, 1, 0, m+1, 2*m+1⟩)
  · rw [show (2:ℕ) = 1 + 1 from by ring, show (1:ℕ) = 0 + 1 from by ring]
    step fm
    ring_nf; finish
  -- Phase 5: drain_tail with A=m, B=0, E=2m+1
  -- (m, 1, 0, m+1, 2m+1) →* (0, 2m+2, 0, 0, 2m+1)
  -- drain_tail needs (A, B+1, 0, A+1, E): A=m, B+1=1 so B=0
  apply stepStar_trans (c₂ := ⟨0, 2*m+2, 0, 0, 2*m+1⟩)
  · have := drain_tail m 0 (2*m+1)
    rw [show 0 + 2 * m + 2 = 2 * m + 2 from by ring] at this
    exact this
  -- Phase 6: R3 x (2m+2)
  have := b_to_a (2*m+2) 0 0 (2*m+1)
  simp only [Nat.zero_add] at this; exact this

-- Combined main transition
theorem main_trans (n : ℕ) : ⟨n+1, 0, 0, 0, n⟩ [fm]⊢⁺ ⟨n+2, 0, 0, 0, n+1⟩ := by
  rcases Nat.even_or_odd n with ⟨m, hm⟩ | ⟨m, hm⟩
  · rw [show m + m = 2 * m from by ring] at hm; subst hm
    exact main_trans_even m
  · subst hm
    exact main_trans_odd m

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨2, 0, 0, 0, 1⟩) (by execute fm 6)
  apply progress_nonhalt_simple (fm := fm) (A := ℕ) (fun n ↦ ⟨n+2, 0, 0, 0, n+1⟩) 0
  intro n; exact ⟨n+1, main_trans (n+1)⟩
