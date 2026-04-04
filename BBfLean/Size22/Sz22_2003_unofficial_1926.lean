import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #1926: [9/70, 22/5, 25/33, 7/11, 25/2]

Vector representation:
```
-1  2 -1 -1  0
 1  0 -1  0  1
 0 -1  2  0 -1
 0  0  0  1 -1
-1  0  2  0  0
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_1926

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a+1, b, c+1, d+1, e⟩ => some ⟨a, b+2, c, d, e⟩
  | ⟨a, b, c+1, d, e⟩ => some ⟨a+1, b, c, d, e+1⟩
  | ⟨a, b+1, c, d, e+1⟩ => some ⟨a, b, c+2, d, e⟩
  | ⟨a, b, c, d, e+1⟩ => some ⟨a, b, c, d+1, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b, c+2, d, e⟩
  | _ => none

-- Phase 1: R5R1R1 chain. Each round: a -= 3, b += 4, d -= 2.
-- (a + 3*k + F + 1, b, 0, d + 2*k, 0) →* (F + 1, b + 4*k, 0, d, 0)
theorem r5r1r1_chain : ∀ k, ∀ a b d,
    ⟨a + 3 * k, b, 0, d + 2 * k, 0⟩ [fm]⊢* ⟨a, b + 4 * k, 0, d, 0⟩ := by
  intro k; induction' k with k ih <;> intro a b d
  · exists 0
  · rw [show a + 3 * (k + 1) = (a + 3) + 3 * k from by ring,
        show d + 2 * (k + 1) = (d + 2) + 2 * k from by ring]
    apply stepStar_trans (ih (a := a + 3) (b := b) (d := d + 2))
    rw [show a + 3 = a + 1 + 1 + 1 from by ring,
        show d + 2 = d + 1 + 1 from by ring]
    step fm; step fm; step fm
    ring_nf; finish

-- Phase 3: R3R2R2 chain. Each round: a += 2, b -= 1, e += 1.
-- (a, b + k, 0, 0, e + 1) →* (a + 2*k, b, 0, 0, e + k + 1)
theorem r3r2r2_chain : ∀ k, ∀ a b e,
    ⟨a, b + k, 0, 0, e + 1⟩ [fm]⊢* ⟨a + 2 * k, b, 0, 0, e + k + 1⟩ := by
  intro k; induction' k with k ih <;> intro a b e
  · exists 0
  · rw [show b + (k + 1) = b + k + 1 from by ring]
    step fm; step fm; step fm
    rw [show a + 1 + 1 = a + 2 from by ring,
        show e = e from rfl]
    apply stepStar_trans (ih (a := a + 2) (b := b) (e := e + 1))
    ring_nf; finish

-- Phase 4: R4 chain. Move e to d.
-- (a, 0, 0, d, e + k) →* (a, 0, 0, d + k, e)
theorem e_to_d : ∀ k, ∀ a d e,
    ⟨a, 0, 0, d, e + k⟩ [fm]⊢* ⟨a, 0, 0, d + k, e⟩ := by
  intro k; induction' k with k ih <;> intro a d e
  · exists 0
  · rw [show e + (k + 1) = (e + k) + 1 from by ring]
    step fm
    rw [show d + 1 = (d + 1) from rfl]
    apply stepStar_trans (ih (a := a) (d := d + 1) (e := e))
    rw [show d + 1 + k = d + (k + 1) from by ring]
    finish

-- Main transition: (3k+F+1, 0, 0, 2k, 0) →⁺ (8k+F+2, 0, 0, 4k+2, 0)
-- where k >= 2 (encoded as k = K + 2)
-- C(F, K) = (3K+F+7, 0, 0, 2K+4, 0)
-- C_new  = (8K+F+18, 0, 0, 4K+10, 0)
theorem main_trans (F K : ℕ) :
    ⟨3 * K + F + 7, 0, 0, 2 * K + 4, 0⟩ [fm]⊢⁺ ⟨8 * K + F + 18, 0, 0, 4 * K + 10, 0⟩ := by
  -- Phase 1: R5R1R1 chain with k = K+2 rounds
  -- (3(K+2)+F+1, 0, 0, 2(K+2), 0) →* (F+1, 4(K+2), 0, 0, 0)
  rw [show 3 * K + F + 7 = (F + 1) + 3 * (K + 2) from by ring,
      show 2 * K + 4 = 0 + 2 * (K + 2) from by ring]
  apply stepStar_stepPlus_stepPlus (r5r1r1_chain (K + 2) (a := F + 1) (b := 0) (d := 0))
  rw [show 0 + 4 * (K + 2) = 4 * (K + 2) from by ring,
      show F + 1 = F + 1 from rfl]
  -- Phase 2: R5R2R2: (F+1, 4(K+2), 0, 0, 0) →⁺ (F+2, 4(K+2), 0, 0, 2)
  rw [show F + 1 = F + 0 + 1 from by ring]
  step fm; step fm; step fm
  -- Phase 3: R3R2R2 chain with 4(K+2) rounds
  rw [show F + 0 + 1 + 1 = F + 2 from by ring,
      show 4 * (K + 2) = 0 + (4 * K + 8) from by ring]
  apply stepStar_trans (r3r2r2_chain (4 * K + 8) (a := F + 2) (b := 0) (e := 1))
  rw [show F + 2 + 2 * (4 * K + 8) = 8 * K + F + 18 from by ring,
      show 1 + (4 * K + 8) + 1 = 4 * K + 10 from by ring]
  -- Phase 4: R4 chain with 4K+10 rounds
  rw [show 4 * K + 10 = 0 + (4 * K + 10) from by ring]
  apply stepStar_trans (e_to_d (4 * K + 10) (a := 8 * K + F + 18) (d := 0) (e := 0))
  finish

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨7, 0, 0, 4, 0⟩) (by execute fm 24)
  show ¬halts fm (⟨3 * 0 + 0 + 7, 0, 0, 2 * 0 + 4, 0⟩ : Q)
  apply progress_nonhalt_simple (fm := fm) (A := ℕ × ℕ)
    (fun ⟨F, K⟩ ↦ ⟨3 * K + F + 7, 0, 0, 2 * K + 4, 0⟩) ⟨0, 0⟩
  intro ⟨F, K⟩
  refine ⟨⟨2 * K + F + 2, 2 * K + 3⟩, ?_⟩
  show ⟨3 * K + F + 7, 0, 0, 2 * K + 4, 0⟩ [fm]⊢⁺ ⟨3 * (2 * K + 3) + (2 * K + F + 2) + 7, 0, 0, 2 * (2 * K + 3) + 4, 0⟩
  rw [show 3 * (2 * K + 3) + (2 * K + F + 2) + 7 = 8 * K + F + 18 from by ring,
      show 2 * (2 * K + 3) + 4 = 4 * K + 10 from by ring]
  exact main_trans F K
