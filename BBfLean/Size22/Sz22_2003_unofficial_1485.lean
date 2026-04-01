import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #1485: [7/15, 54/77, 11/3, 125/2, 3/5]

Vector representation:
```
 0 -1 -1  1  0
 1  3  0 -1 -1
 0 -1  0  0  1
-1  0  3  0  0
 0  1 -1  0  0
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_1485

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a, b+1, c+1, d, e⟩ => some ⟨a, b, c, d+1, e⟩
  | ⟨a, b, c, d+1, e+1⟩ => some ⟨a+1, b+3, c, d, e⟩
  | ⟨a, b+1, c, d, e⟩ => some ⟨a, b, c, d, e+1⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b, c+3, d, e⟩
  | ⟨a, b, c+1, d, e⟩ => some ⟨a, b+1, c, d, e⟩
  | _ => none

-- R4 drain: a fires R4 repeatedly, transferring a to c (×3).
theorem r4_drain : ∀ k, ∀ a c e, ⟨a + k, 0, c, 0, e⟩ [fm]⊢* ⟨a, 0, c + 3 * k, 0, e⟩ := by
  intro k; induction' k with k ih
  · intro a c e; exists 0
  · intro a c e; rw [Nat.add_succ]
    step fm
    apply stepStar_trans (ih a (c + 3) e); ring_nf; finish

-- R3 drain: b fires R3 repeatedly, transferring b to e.
theorem r3_drain : ∀ k, ∀ a e, ⟨a, k, 0, 0, e⟩ [fm]⊢* ⟨a, 0, 0, 0, e + k⟩ := by
  intro k; induction' k with k ih
  · intro a e; exists 0
  · intro a e; rw [Nat.add_succ]
    step fm
    apply stepStar_trans (ih a (e + 1)); ring_nf; finish

-- Inner loop: repeated R2, R1×3 cycle.
theorem loop : ∀ m, ∀ k E, ⟨k, 0, 3 * m + 1, 2 * k + 1, E + m + 1⟩ [fm]⊢*
    ⟨k + m + 1, 2, 0, 2 * k + 2 * m + 1, E⟩ := by
  intro m; induction' m with m ih
  · intro k E
    -- State: (k, 0, 1, 2k+1, E+1). R2.
    rw [show 3 * 0 + 1 = 0 + 1 from by ring,
        show 2 * k + 1 = (2 * k) + 1 from by ring,
        show E + 0 + 1 = E + 1 from by ring]
    step fm
    -- State: (k+1, 3, 1, 2k, E). R1.
    rw [show (3 : ℕ) = 2 + 1 from rfl]
    step fm
    rw [show k + 0 + 1 = k + 1 from by ring,
        show 2 * k + 2 * 0 + 1 = 2 * k + 1 from by ring]
    finish
  · intro k E
    -- State: (k, 0, 3m+4, 2k+1, E+m+2). R2.
    rw [show 3 * (m + 1) + 1 = (3 * m + 3) + 1 from by ring,
        show 2 * k + 1 = (2 * k) + 1 from by ring,
        show E + (m + 1) + 1 = (E + m + 1) + 1 from by ring]
    step fm
    -- State: (k+1, 3, 3m+4, 2k, E+m+1). R1×3.
    rw [show (3 : ℕ) = 2 + 1 from rfl,
        show (3 * m + 3) + 1 = ((3 * m + 2) + 1) + 1 from by ring]
    step fm
    rw [show (3 * m + 2) + 1 = ((3 * m + 1) + 1) + 1 from by ring]
    step fm
    rw [show (3 * m + 1) + 1 = (3 * m) + 1 + 1 from by ring,
        show (1 : ℕ) = 0 + 1 from rfl]
    step fm
    -- State: (k+1, 0, 3m+1, 2k+3, E+m+1). Apply IH.
    rw [show 2 * k + 3 = 2 * (k + 1) + 1 from by ring]
    apply stepStar_trans (ih (k + 1) E)
    ring_nf; finish

-- Drain: combined R2/R3+R2 drain followed by R3 drain.
theorem drain : ∀ D, ∀ A G E, ⟨A, G + 2, 0, D, E⟩ [fm]⊢*
    ⟨A + D, 0, 0, 0, G + 2 * D + E + 2⟩ := by
  intro D; induction' D with D ih
  · intro A G E
    rw [show A + 0 = A from by ring,
        show G + 2 * 0 + E + 2 = E + (G + 2) from by ring]
    exact r3_drain (G + 2) A E
  · intro A G E; rcases E with _ | E'
    · -- E = 0: R3 then R2
      rw [show G + 2 = (G + 1) + 1 from by ring,
          show D + 1 = D + 1 from rfl]
      step fm
      -- State: (A, G+1, 0, D+1, 1). R2.
      rw [show D + 1 = D + 1 from rfl, show (1 : ℕ) = 0 + 1 from rfl]
      step fm
      -- State: (A+1, G+4, 0, D, 0).
      rw [show G + 1 + 3 = (G + 2) + 2 from by ring]
      apply stepStar_trans (ih (A + 1) (G + 2) 0)
      ring_nf; finish
    · -- E = E' + 1: R2
      rw [show D + 1 = D + 1 from rfl,
          show E' + 1 = E' + 1 from rfl]
      step fm
      -- State: (A+1, G+5, 0, D, E').
      rw [show G + 2 + 3 = (G + 3) + 2 from by ring]
      apply stepStar_trans (ih (A + 1) (G + 3) E')
      ring_nf; finish

-- R4 full drain from (a, 0, 0, 0, e) to (0, 0, 3a, 0, e).
theorem r4_full (a e : ℕ) : ⟨a, 0, 0, 0, e⟩ [fm]⊢* ⟨0, 0, 3 * a, 0, e⟩ := by
  have h := r4_drain a 0 0 e
  simp at h; exact h

-- Main transition: (a+1, 0, 0, 0, e+a+2) ⊢⁺ (3a+2, 0, 0, 0, 4a+e+5)
theorem main_trans (a e : ℕ) :
    ⟨a + 1, 0, 0, 0, e + a + 2⟩ [fm]⊢⁺ ⟨3 * a + 2, 0, 0, 0, 4 * a + e + 5⟩ := by
  -- Phase 1: R4 drain (a+1 times)
  apply stepStar_stepPlus_stepPlus (r4_full (a + 1) (e + a + 2))
  -- Now at (0, 0, 3(a+1), 0, e+a+2) = (0, 0, 3a+3, 0, e+a+2)
  -- Phase 2: R5, R1 (2 steps)
  rw [show 3 * (a + 1) = ((3 * a + 1) + 1) + 1 from by ring]
  step fm; step fm
  -- Now at (0, 0, 3a+1, 1, e+a+2)
  -- Phase 3: Loop
  rw [show (1 : ℕ) = 2 * 0 + 1 from by ring,
      show e + a + 2 = (e + 1) + a + 1 from by ring]
  apply stepStar_trans (loop a 0 (e + 1))
  -- Now at (a+1, 2, 0, 2a+1, e+1)
  rw [show 0 + a + 1 = a + 1 from by ring,
      show 2 * 0 + 2 * a + 1 = 2 * a + 1 from by ring,
      show (2 : ℕ) = 0 + 2 from by ring]
  -- Phase 4: Combined drain
  apply stepStar_trans (drain (2 * a + 1) (a + 1) 0 (e + 1))
  ring_nf; finish

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨1, 0, 0, 0, 3⟩)
  · execute fm 9
  apply progress_nonhalt_simple (fm := fm) (A := ℕ × ℕ)
    (fun ⟨a, e⟩ ↦ ⟨a + 1, 0, 0, 0, e + a + 2⟩) ⟨0, 1⟩
  intro ⟨a, e⟩
  refine ⟨⟨3 * a + 1, a + e + 2⟩, ?_⟩
  show ⟨a + 1, 0, 0, 0, e + a + 2⟩ [fm]⊢⁺ ⟨3 * a + 1 + 1, 0, 0, 0, (a + e + 2) + (3 * a + 1) + 2⟩
  rw [show 3 * a + 1 + 1 = 3 * a + 2 from by ring,
      show (a + e + 2) + (3 * a + 1) + 2 = 4 * a + e + 5 from by ring]
  exact main_trans a e

end Sz22_2003_unofficial_1485
