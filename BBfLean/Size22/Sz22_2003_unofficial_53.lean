import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #53: [1/15, 9/539, 196/3, 5/7, 33/2]

Vector representation:
```
 0 -1 -1  0  0
 0  2  0 -2 -1
 2 -1  0  2  0
 0  0  1 -1  0
-1  1  0  0  1
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_53

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a, b+1, c+1, d, e⟩ => some ⟨a, b, c, d, e⟩
  | ⟨a, b, c, d+2, e+1⟩ => some ⟨a, b+2, c, d, e⟩
  | ⟨a, b+1, c, d, e⟩ => some ⟨a+2, b, c, d+2, e⟩
  | ⟨a, b, c, d+1, e⟩ => some ⟨a, b, c+1, d, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b+1, c, d, e+1⟩
  | _ => none

-- R3,R2 interleaved chain: (a, b+1, 0, 0, e+1) ->* (a+2*(e+1), b+e+2, 0, 0, 0)
theorem r3r2_chain : ∀ e, ∀ a b,
    ⟨a, b+1, 0, 0, e+1⟩ [fm]⊢* ⟨a+2*(e+1), b+e+2, 0, 0, 0⟩ := by
  intro e; induction' e with e ih <;> intro a b
  · execute fm 2
  · rw [show b + 1 = b + 1 from rfl]
    step fm; step fm
    rw [show b + 1 + 1 = (b + 1) + 1 from by ring]
    apply stepStar_trans (ih _ _)
    ring_nf; finish

-- R3 chain: (a, k, 0, d, 0) ->* (a+2*k, 0, 0, d+2*k, 0)
theorem r3_chain : ∀ k, ∀ a d,
    ⟨a, k, 0, d, 0⟩ [fm]⊢* ⟨a+2*k, 0, 0, d+2*k, 0⟩ := by
  intro k; induction' k with k ih <;> intro a d
  · exists 0
  · step fm
    apply stepStar_trans (ih _ _)
    ring_nf; finish

-- R4 chain: (a, 0, c, k, 0) ->* (a, 0, c+k, 0, 0)
theorem r4_chain : ∀ k, ∀ a c,
    ⟨a, 0, c, k, 0⟩ [fm]⊢* ⟨a, 0, c+k, 0, 0⟩ := by
  intro k; induction' k with k ih <;> intro a c
  · exists 0
  · step fm
    apply stepStar_trans (ih _ _)
    ring_nf; finish

-- R5,R1 chain: (a+k, 0, k, 0, e) ->* (a, 0, 0, 0, e+k)
theorem r5r1_chain : ∀ k, ∀ a e,
    ⟨a+k, 0, k, 0, e⟩ [fm]⊢* ⟨a, 0, 0, 0, e+k⟩ := by
  intro k; induction' k with k ih <;> intro a e
  · exists 0
  · rw [show a + (k + 1) = (a + k) + 1 from by ring]
    step fm; step fm
    apply stepStar_trans (ih _ _)
    ring_nf; finish

-- Main transition: (a+1, 0, 0, 0, e+1) ->+ (a+2*e+4, 0, 0, 0, 2*e+6)
theorem main_trans : ⟨a+1, 0, 0, 0, e+1⟩ [fm]⊢⁺ ⟨a+2*e+4, 0, 0, 0, 2*e+6⟩ := by
  -- Phase 1a: R5 (3 steps: R5, R3, R2)
  step fm; step fm; step fm
  -- State: (a+2, 2, 0, 0, e+1)
  -- Phase 1b: R3,R2 chain with e+1 rounds
  -- (a+2, 1+1, 0, 0, e+1) ->* (a+2+2*(e+1), 1+e+2, 0, 0, 0)
  rw [show (2 : ℕ) = 1 + 1 from rfl]
  apply stepStar_trans (r3r2_chain e (a+2) 1)
  -- State: (a+2e+4, e+3, 0, 0, 0)
  -- Phase 2: R3 chain with b=e+3
  rw [show (1 + e + 2 : ℕ) = e + 3 from by ring]
  rw [show (a + 2 + 2 * (e + 1) : ℕ) = a + 2*e + 4 from by ring]
  apply stepStar_trans (r3_chain (e+3) (a+2*e+4) 0)
  -- State: (a+4e+10, 0, 0, 2e+6, 0)
  -- Phase 3: R4 chain
  rw [show (a + 2 * e + 4 + 2 * (e + 3) : ℕ) = a + 4*e + 10 from by ring]
  rw [show (0 + 2 * (e + 3) : ℕ) = 2*e + 6 from by ring]
  apply stepStar_trans (r4_chain (2*e+6) (a+4*e+10) 0)
  -- State: (a+4e+10, 0, 2e+6, 0, 0)
  -- Phase 4: R5,R1 chain
  rw [show (0 + (2 * e + 6) : ℕ) = 2*e + 6 from by ring]
  rw [show (a + 4 * e + 10 : ℕ) = (a + 2*e + 4) + (2*e + 6) from by ring]
  apply stepStar_trans (r5r1_chain (2*e+6) (a+2*e+4) 0)
  ring_nf; finish

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨2, 0, 0, 0, 4⟩) (by execute fm 17)
  apply progress_nonhalt_simple (fm := fm) (A := ℕ × ℕ)
    (fun ⟨a, e⟩ ↦ ⟨a+1, 0, 0, 0, e+1⟩) ⟨1, 3⟩
  intro ⟨a, e⟩; exact ⟨⟨a+2*e+3, 2*e+5⟩, main_trans⟩

end Sz22_2003_unofficial_53
