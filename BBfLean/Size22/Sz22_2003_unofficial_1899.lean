import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #1899: [9/35, 65/33, 14/3, 11/13, 231/2]

Vector representation:
```
 0  2 -1 -1  0  0
 0 -1  1  0 -1  1
 1 -1  0  1  0  0
 0  0  0  0  1 -1
-1  1  0  1  1  0
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_1899

def Q := ℕ × ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a, b, c+1, d+1, e, f⟩ => some ⟨a, b+2, c, d, e, f⟩
  | ⟨a, b+1, c, d, e+1, f⟩ => some ⟨a, b, c+1, d, e, f+1⟩
  | ⟨a, b+1, c, d, e, f⟩ => some ⟨a+1, b, c, d+1, e, f⟩
  | ⟨a, b, c, d, e, f+1⟩ => some ⟨a, b, c, d, e+1, f⟩
  | ⟨a+1, b, c, d, e, f⟩ => some ⟨a, b+1, c, d+1, e+1, f⟩
  | _ => none

-- R2+R1 interleaved chain: k+1 rounds drain e from k+1 to 0.
-- From (a, b+1, 0, d+k+1, k+1, f) to (a, b+k+2, 0, d, 0, f+k+1).
theorem r2r1_chain : ∀ k, ∀ a b d f,
    ⟨a, b + 1, 0, d + k + 1, k + 1, f⟩ [fm]⊢* ⟨a, b + k + 2, 0, d, 0, f + k + 1⟩ := by
  intro k; induction' k with k ih <;> intro a b d f
  · step fm; step fm; finish
  · -- Goal: (a, b+1, 0, d+(k+1)+1, (k+1)+1, f) →* (a, b+(k+1)+2, 0, d, 0, f+(k+1)+1)
    -- Two steps: R2 then R1
    -- R2: (a, b, 1, d+(k+1)+1, k+1, f+1)
    -- R1: (a, b+2, 0, d+k+1, k+1, f+1)
    -- Then apply ih with b' = b+1, d' = d, f' = f+1
    -- ih: (a, (b+1)+1, 0, d+k+1, k+1, f+1) →* (a, (b+1)+k+2, 0, d, 0, (f+1)+k+1)
    rw [show d + (k + 1) + 1 = d + (k + 2) from by ring,
        show (k + 1) + 1 = (k + 2) from by ring]
    step fm
    step fm
    -- After R2+R1: (a, b+2, 0, d+k+1, k+1, f+1)
    -- Need to match ih's input: (a, (b+1)+1, 0, d+k+1, k+1, f+1)
    rw [show b + 2 = (b + 1) + 1 from by ring]
    apply stepStar_trans (ih a (b + 1) d (f + 1))
    -- ih gives: (a, (b+1)+k+2, 0, d, 0, (f+1)+k+1)
    -- Need: (a, b+(k+1)+2, 0, d, 0, f+(k+1)+1)
    rw [show b + 1 + k + 2 = b + (k + 1) + 2 from by ring,
        show f + 1 + k + 1 = f + (k + 1) + 1 from by ring]
    finish

-- R3 chain: drain b when e=0.
theorem r3_chain : ∀ k, ∀ a b d f,
    ⟨a, b + k, 0, d, 0, f⟩ [fm]⊢* ⟨a + k, b, 0, d + k, 0, f⟩ := by
  intro k; induction' k with k ih <;> intro a b d f
  · exists 0
  · rw [show b + (k + 1) = (b + k) + 1 from by ring]
    step fm
    apply stepStar_trans (ih (a + 1) b (d + 1) f)
    ring_nf; finish

-- R4 chain: move f to e.
theorem r4_chain : ∀ k, ∀ a d e f,
    ⟨a, 0, 0, d, e, f + k⟩ [fm]⊢* ⟨a, 0, 0, d, e + k, f⟩ := by
  intro k; induction' k with k ih <;> intro a d e f
  · exists 0
  · rw [show f + (k + 1) = (f + k) + 1 from by ring]
    step fm
    apply stepStar_trans (ih a d (e + 1) f)
    ring_nf; finish

-- Main transition: (a+1, 0, 0, 2*e, e, 0) →⁺ (a+e+2, 0, 0, 2*(e+1), e+1, 0)
theorem main_trans : ∀ a e,
    ⟨a + 1, 0, 0, 2 * e, e, 0⟩ [fm]⊢⁺ ⟨a + e + 2, 0, 0, 2 * (e + 1), e + 1, 0⟩ := by
  intro a e
  -- Phase 1: R5: (a+1, 0, 0, 2*e, e, 0) → (a, 1, 0, 2*e+1, e+1, 0)
  step fm
  -- Goal: (a, 1, 0, 2*e+1, e+1, 0) ⊢* target
  -- Phase 2: R2+R1 chain (e+1 rounds)
  -- r2r1_chain e: (a, 0+1, 0, 0+e+1, e+1, 0) →* (a, 0+e+2, 0, 0, 0, 0+e+1)
  -- Need to rewrite 2*e+1 as 0+e+1 which is e+1... but 2*e+1 ≠ e+1 in general!
  -- Actually d+k+1 = 0+e+1 means d=0, k=e. Then d+k+1 = e+1 but we have 2*e+1.
  -- So we need d = e: d+e+1 = 2*e+1 ✓
  rw [show 2 * e + 1 = e + e + 1 from by ring,
      show (1 : ℕ) = 0 + 1 from by ring]
  apply stepStar_trans (r2r1_chain e a 0 e 0)
  -- After chain: (a, 0+e+2, 0, e, 0, 0+e+1) = (a, e+2, 0, e, 0, e+1)
  rw [show 0 + e + 2 = e + 2 from by ring,
      show 0 + e + 1 = e + 1 from by ring]
  -- Phase 3: R3 chain (e+2 steps): (a, e+2, 0, e, 0, e+1) →* (a+e+2, 0, 0, 2*e+2, 0, e+1)
  rw [show e + 2 = 0 + (e + 2) from by ring]
  apply stepStar_trans (r3_chain (e + 2) a 0 e (e + 1))
  rw [show a + (e + 2) = a + e + 2 from by ring,
      show e + (e + 2) = 2 * e + 2 from by ring]
  -- Phase 4: R4 chain (e+1 steps): (a+e+2, 0, 0, 2*e+2, 0, e+1) →* (a+e+2, 0, 0, 2*e+2, e+1, 0)
  rw [show e + 1 = 0 + (e + 1) from by ring]
  apply stepStar_trans (r4_chain (e + 1) (a + e + 2) (2 * e + 2) 0 0)
  rw [show 0 + (e + 1) = e + 1 from by ring,
      show 2 * e + 2 = 2 * (e + 1) from by ring]
  finish

theorem nonhalt : ¬halts fm c₀ := by
  apply progress_nonhalt_simple (fm := fm) (A := ℕ × ℕ)
    (fun ⟨a, e⟩ ↦ ⟨a + 1, 0, 0, 2 * e, e, 0⟩) ⟨0, 0⟩
  intro ⟨a, e⟩
  exact ⟨⟨a + e + 1, e + 1⟩, main_trans a e⟩
