import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #1939: [9/70, 35/33, 20/3, 11/5, 3/2]

Vector representation:
```
-1  2 -1 -1  0
 0 -1  1  1 -1
 2 -1  1  0  0
 0  0 -1  0  1
-1  1  0  0  0
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_1939

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a+1, b, c+1, d+1, e⟩ => some ⟨a, b+2, c, d, e⟩
  | ⟨a, b+1, c, d, e+1⟩ => some ⟨a, b, c+1, d+1, e⟩
  | ⟨a, b+1, c, d, e⟩ => some ⟨a+2, b, c+1, d, e⟩
  | ⟨a, b, c+1, d, e⟩ => some ⟨a, b, c, d, e+1⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b+1, c, d, e⟩
  | _ => none

-- R2+R1 chain: (a+e, b+1, 0, 0, e) ->* (a, b+e+1, 0, 0, 0)
theorem r2r1_chain : ∀ e a b, ⟨a + e, b + 1, 0, 0, e⟩ [fm]⊢* ⟨a, b + e + 1, (0 : ℕ), 0, 0⟩ := by
  intro e; induction' e with e ih <;> intro a b
  · exists 0
  · rw [show a + (e + 1) = (a + e) + 1 from by ring]
    step fm
    step fm
    rw [show b + 2 = (b + 1) + 1 from by ring]
    apply stepStar_trans (ih a (b + 1))
    ring_nf; finish

-- Phase 1: (a+e+1, 0, 0, 0, e) ->+ (a, e+1, 0, 0, 0)
theorem phase1 (a e : ℕ) : ⟨a + e + 1, 0, 0, 0, e⟩ [fm]⊢⁺ ⟨a, e + 1, (0 : ℕ), 0, 0⟩ := by
  rw [show a + e + 1 = (a + e) + 1 from by ring]
  step fm
  apply stepStar_trans (r2r1_chain e a 0)
  ring_nf; finish

-- R3 chain: (a, k+b, c, 0, 0) ->* (a+2k, b, c+k, 0, 0)
-- Need b in +1 form for step fm to fire. Restructure so step sees (_, b'+1, _, 0, 0).
theorem r3_chain : ∀ k a c, ⟨a, k, c, 0, 0⟩ [fm]⊢* ⟨a + 2 * k, 0, c + k, 0, 0⟩ := by
  intro k; induction' k with k ih <;> intro a c
  · exists 0
  · rw [show (k + 1) = k + 1 from rfl]
    step fm
    apply stepStar_trans (ih (a + 2) (c + 1))
    ring_nf; finish

-- R4 chain: (a, 0, k, 0, e) ->* (a, 0, 0, 0, e+k)
theorem r4_chain : ∀ k a e, ⟨a, 0, k, 0, e⟩ [fm]⊢* ⟨a, 0, 0, 0, e + k⟩ := by
  intro k; induction' k with k ih <;> intro a e
  · exists 0
  · step fm
    apply stepStar_trans (ih a (e + 1))
    ring_nf; finish

-- Main transition: (a+e+1, 0, 0, 0, e) ->+ (a+2e+2, 0, 0, 0, e+1)
theorem main_trans (a e : ℕ) : ⟨a + e + 1, 0, 0, 0, e⟩ [fm]⊢⁺ ⟨a + 2 * e + 2, 0, 0, 0, e + 1⟩ := by
  apply stepPlus_stepStar_stepPlus (phase1 a e)
  rw [show e + 1 = e + 1 from rfl]
  apply stepStar_trans (r3_chain (e + 1) a 0)
  rw [show 0 + (e + 1) = e + 1 from by ring]
  apply stepStar_trans (r4_chain (e + 1) (a + 2 * (e + 1)) 0)
  ring_nf; finish

theorem nonhalt : ¬halts fm c₀ := by
  apply progress_nonhalt_simple (fm := fm) (A := ℕ × ℕ)
    (fun ⟨F, e⟩ ↦ ⟨F + e + 1, 0, 0, 0, e⟩) ⟨0, 0⟩
  intro ⟨F, e⟩
  refine ⟨⟨F + e, e + 1⟩, ?_⟩
  show ⟨F + e + 1, 0, 0, 0, e⟩ [fm]⊢⁺ ⟨F + e + (e + 1) + 1, 0, 0, 0, e + 1⟩
  rw [show F + e + (e + 1) + 1 = F + 2 * e + 2 from by ring]
  exact main_trans F e
