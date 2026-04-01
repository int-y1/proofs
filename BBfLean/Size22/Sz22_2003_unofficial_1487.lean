import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #1487: [7/15, 6/77, 121/3, 25/121, 21/2]

Vector representation:
```
 0 -1 -1  1  0
 1  1  0 -1 -1
 0 -1  0  0  2
 0  0  2  0 -2
-1  1  0  1  0
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_1487

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a, b+1, c+1, d, e⟩ => some ⟨a, b, c, d+1, e⟩
  | ⟨a, b, c, d+1, e+1⟩ => some ⟨a+1, b+1, c, d, e⟩
  | ⟨a, b+1, c, d, e⟩ => some ⟨a, b, c, d, e+2⟩
  | ⟨a, b, c, d, e+2⟩ => some ⟨a, b, c+2, d, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b+1, c, d+1, e⟩
  | _ => none

-- R2/R3 interleave: drains d by 2 per round, gaining 2 in a and 1 in b.
-- (a, b, 0, d + 2*j, 1) ->* (a + 2*j, b + j, 0, d, 1)
theorem r2r3_chain : ∀ j a b d, ⟨a, b, 0, d + 2 * j, (1 : ℕ)⟩ [fm]⊢* ⟨a + 2 * j, b + j, 0, d, (1 : ℕ)⟩ := by
  intro j; induction' j with j ih <;> intro a b d
  · exists 0
  · rw [show d + 2 * (j + 1) = (d + 2 * j) + 2 from by ring]
    step fm  -- R2: d+2*j+2 >= 1, e=1 >= 1 -> (a+1, b+1, 0, d+2*j+1, 0)
    step fm  -- R3: b+1 >= 1 -> (a+1, b, 0, d+2*j+1, 2)
    step fm  -- R2: d+2*j+1 >= 1, e=2 >= 1 -> (a+2, b+1, 0, d+2*j, 1)
    apply stepStar_trans (ih (a + 2) (b + 1) d)
    ring_nf; finish

-- R3 drain: (a, j, 0, 0, e) ->* (a, 0, 0, 0, e + 2*j)
theorem r3_drain : ∀ j a e, ⟨a, j, 0, 0, e⟩ [fm]⊢* ⟨a, 0, 0, 0, e + 2 * j⟩ := by
  intro j; induction' j with j ih <;> intro a e
  · exists 0
  · rw [show (j : ℕ) + 1 = j + 1 from rfl]
    step fm  -- R3: b=j+1 >= 1 -> (a, j, 0, 0, e+2)
    apply stepStar_trans (ih a (e + 2))
    ring_nf; finish

-- R4 drain: (a, 0, c, 0, e + 2*j) ->* (a, 0, c + 2*j, 0, e) when b=0, d=0
theorem r4_drain : ∀ j a c e, ⟨a, 0, c, 0, e + 2 * j⟩ [fm]⊢* ⟨a, 0, c + 2 * j, 0, e⟩ := by
  intro j; induction' j with j ih <;> intro a c e
  · exists 0
  · rw [show e + 2 * (j + 1) = (e + 2 * j) + 2 from by ring]
    step fm  -- R4: e >= 2 -> (a, 0, c+2, 0, e+2*j)
    apply stepStar_trans (ih a (c + 2) e)
    ring_nf; finish

-- R5+R1 chain: (a + j, 0, c + j, d, 0) ->* (a, 0, c, d + 2*j, 0) when e=0, b=0
theorem r5r1_chain : ∀ j a c d, ⟨a + j, 0, c + j, d, (0 : ℕ)⟩ [fm]⊢* ⟨a, 0, c, d + 2 * j, (0 : ℕ)⟩ := by
  intro j; induction' j with j ih <;> intro a c d
  · exists 0
  · rw [show a + (j + 1) = (a + j) + 1 from by ring,
        show c + (j + 1) = (c + j) + 1 from by ring]
    step fm  -- R5: a >= 1 -> (a+j, 1, c+j+1, d+1, 0)
    step fm  -- R1: b >= 1, c >= 1 -> (a+j, 0, c+j, d+2, 0)
    apply stepStar_trans (ih a c (d + 2))
    ring_nf; finish

-- Opening: (1, 0, 0, d, 0) ⊢⁺ (1, 1, 0, d, 1) for any d
theorem opening (d : ℕ) : ⟨1, 0, 0, d, (0 : ℕ)⟩ [fm]⊢⁺ ⟨1, 1, 0, d, (1 : ℕ)⟩ := by
  refine ⟨3, by omega, ?_⟩
  show stepNat fm 3 ⟨1, 0, 0, d, 0⟩ = some ⟨1, 1, 0, d, 1⟩
  simp [stepNat, Nat.repeat, fm]

-- Middle: (2*k+1, 0, 2*k+2, 0, 1) ⊢⁺ (2*k+1, 0, 2*k, 2, 0)
theorem middle (k : ℕ) : ⟨2 * k + 1, 0, 2 * k + 2, 0, (1 : ℕ)⟩ [fm]⊢⁺ ⟨2 * k + 1, 0, 2 * k, 2, (0 : ℕ)⟩ := by
  rw [show 2 * k + 1 = (2 * k) + 1 from by ring]
  step fm  -- R5: (2*k, 1, 2*k+2, 1, 1)
  rw [show 2 * k + 2 = (2 * k + 1) + 1 from by ring]
  step fm  -- R1: (2*k, 0, 2*k+1, 2, 1)
  step fm  -- R2: (2*k+1, 1, 2*k+1, 1, 0)
  rw [show 2 * k + 1 = (2 * k) + 1 from by ring]
  step fm  -- R1: (2*k+1, 0, 2*k, 2, 0)
  finish

-- Main transition: (1, 0, 0, 2*k, 0) ⊢⁺ (1, 0, 0, 4*k+2, 0)
theorem main_trans (k : ℕ) : ⟨1, 0, 0, 2 * k, (0 : ℕ)⟩ [fm]⊢⁺ ⟨1, 0, 0, 4 * k + 2, (0 : ℕ)⟩ := by
  -- Phase 1: Opening
  have phase1 := opening (2 * k)
  -- Phase 2: R2/R3 interleave: (1, 1, 0, 2*k, 1) ->* (2*k+1, k+1, 0, 0, 1)
  have phase2 : ⟨1, 1, 0, 2 * k, (1 : ℕ)⟩ [fm]⊢* ⟨2 * k + 1, k + 1, 0, 0, (1 : ℕ)⟩ := by
    rw [show (2 : ℕ) * k = 0 + 2 * k from by ring]
    apply stepStar_trans (r2r3_chain k 1 1 0)
    ring_nf; finish
  -- Phase 3: R3 drain: (2*k+1, k+1, 0, 0, 1) ->* (2*k+1, 0, 0, 0, 2*k+3)
  have phase3 : ⟨2 * k + 1, k + 1, 0, 0, (1 : ℕ)⟩ [fm]⊢* ⟨2 * k + 1, 0, 0, 0, 2 * k + 3⟩ := by
    apply stepStar_trans (r3_drain (k + 1) (2 * k + 1) 1)
    rw [show 1 + 2 * (k + 1) = 2 * k + 3 from by ring]; finish
  -- Phase 4: R4 drain: (2*k+1, 0, 0, 0, 2*k+3) ->* (2*k+1, 0, 2*k+2, 0, 1)
  have phase4 : ⟨2 * k + 1, 0, 0, 0, 2 * k + 3⟩ [fm]⊢* ⟨2 * k + 1, 0, 2 * k + 2, 0, (1 : ℕ)⟩ := by
    rw [show 2 * k + 3 = 1 + 2 * (k + 1) from by ring]
    apply stepStar_trans (r4_drain (k + 1) (2 * k + 1) 0 1)
    rw [show 0 + 2 * (k + 1) = 2 * k + 2 from by ring]; finish
  -- Phase 5: Middle: (2*k+1, 0, 2*k+2, 0, 1) ⊢⁺ (2*k+1, 0, 2*k, 2, 0)
  have phase5 := middle k
  -- Phase 6: R5+R1 chain: (2*k+1, 0, 2*k, 2, 0) ->* (1, 0, 0, 4*k+2, 0)
  have phase6 : ⟨2 * k + 1, 0, 2 * k, 2, (0 : ℕ)⟩ [fm]⊢* ⟨1, 0, 0, 4 * k + 2, (0 : ℕ)⟩ := by
    have h := r5r1_chain (2 * k) 1 0 2
    rw [show 1 + 2 * k = 2 * k + 1 from by ring,
        show 0 + 2 * k = 2 * k from by ring,
        show 2 + 2 * (2 * k) = 4 * k + 2 from by ring] at h
    exact h
  exact stepPlus_trans
    (stepPlus_stepStar_stepPlus phase1 (stepStar_trans phase2 (stepStar_trans phase3 phase4)))
    (stepPlus_stepStar_stepPlus phase5 phase6)

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨1, 0, 0, 0, 0⟩) (by execute fm 0)
  apply progress_nonhalt_simple (fm := fm) (A := ℕ)
    (fun k ↦ ⟨1, 0, 0, 2 * k, 0⟩) 0
  intro k
  refine ⟨2 * k + 1, ?_⟩
  rw [show 2 * (2 * k + 1) = 4 * k + 2 from by ring]
  exact main_trans k

end Sz22_2003_unofficial_1487
