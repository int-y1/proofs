import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #160: [1/45, 4/21, 121/3, 15/2, 63/11]

Vector representation:
```
 0 -2 -1  0  0
 2 -1  0 -1  0
 0 -1  0  0  2
-1  1  1  0  0
 0  2  0  1 -1
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_160

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a, b+2, c+1, d, e⟩ => some ⟨a, b, c, d, e⟩
  | ⟨a, b+1, c, d+1, e⟩ => some ⟨a+2, b, c, d, e⟩
  | ⟨a, b+1, c, d, e⟩ => some ⟨a, b, c, d, e+2⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b+1, c+1, d, e⟩
  | ⟨a, b, c, d, e+1⟩ => some ⟨a, b+2, c, d+1, e⟩
  | _ => none

-- Phase 1: R5+R1 loop transfers c to d, consuming e
theorem phase1 : ∀ k d e, ⟨0, 0, k, d, e + k⟩ [fm]⊢* ⟨0, 0, 0, d + k, e⟩ := by
  intro k; induction' k with k ih <;> intro d e
  · exists 0
  rw [show e + (k + 1) = (e + k) + 1 from by ring]
  step fm; step fm
  apply stepStar_trans (ih _ _)
  ring_nf; finish

-- Phase 2a: 3 steps
theorem phase2a (d e : ℕ) : ⟨0, 0, 0, d + 1, e + 1⟩ [fm]⊢⁺ ⟨4, 0, 0, d, e⟩ := by
  step fm; step fm; step fm; finish

-- Phase 2b: R4+R2 loop
theorem phase2b : ∀ d a c e, ⟨a + 1, 0, c, d, e⟩ [fm]⊢* ⟨a + 1 + d, 0, c + d, 0, e⟩ := by
  intro d; induction' d with d ih <;> intro a c e
  · exists 0
  step fm; step fm
  apply stepStar_trans (ih _ _ _)
  ring_nf; finish

-- Phase 3: R4+R3 loop
theorem phase3 : ∀ k c e, ⟨k, 0, c, 0, e⟩ [fm]⊢* ⟨0, 0, c + k, 0, e + 2 * k⟩ := by
  intro k; induction' k with k ih <;> intro c e
  · exists 0
  step fm; step fm
  apply stepStar_trans (ih _ _)
  ring_nf; finish

-- Main transition
theorem main_step (c e : ℕ) :
    ⟨0, 0, c + 1, 0, e + c + 2⟩ [fm]⊢⁺ ⟨0, 0, 2 * c + 4, 0, e + 2 * c + 8⟩ := by
  -- Phase 1
  apply stepStar_stepPlus_stepPlus
  · show ⟨0, 0, c + 1, 0, e + c + 2⟩ [fm]⊢* ⟨0, 0, 0, c + 1, e + 1⟩
    have h := phase1 (c + 1) 0 (e + 1)
    simp only [Nat.zero_add] at h
    rwa [show e + 1 + (c + 1) = e + c + 2 from by ring] at h
  -- Phase 2a
  apply stepPlus_stepStar_stepPlus (phase2a c e)
  -- Phase 2b
  apply stepStar_trans
  · show ⟨4, 0, 0, c, e⟩ [fm]⊢* ⟨c + 4, 0, c, 0, e⟩
    have h := phase2b c 3 0 e
    simp only [Nat.zero_add] at h
    rwa [show 3 + 1 + c = c + 4 from by ring] at h
  -- Phase 3
  show ⟨c + 4, 0, c, 0, e⟩ [fm]⊢* ⟨0, 0, 2 * c + 4, 0, e + 2 * c + 8⟩
  have h := phase3 (c + 4) c e
  rwa [show c + (c + 4) = 2 * c + 4 from by ring,
       show e + 2 * (c + 4) = e + 2 * c + 8 from by ring] at h

theorem nonhalt : ¬halts fm c₀ := by
  have boot : c₀ [fm]⊢* ⟨0, 0, 1, 0, 2⟩ := by
    unfold c₀; step fm; step fm; finish
  apply stepStar_not_halts_not_halts boot
  apply progress_nonhalt (fun q ↦ ∃ c e, q = ⟨0, 0, c + 1, 0, e + c + 2⟩)
  · intro q ⟨c, e, hq⟩
    refine ⟨⟨0, 0, 2 * c + 4, 0, e + 2 * c + 8⟩, ⟨2 * c + 3, e + 3, ?_⟩, ?_⟩
    · change (0, 0, 2 * c + 4, 0, e + 2 * c + 8) = (0, 0, (2 * c + 3) + 1, 0, (e + 3) + (2 * c + 3) + 2)
      have h1 : 2 * c + 4 = (2 * c + 3) + 1 := by omega
      have h2 : e + 2 * c + 8 = (e + 3) + (2 * c + 3) + 2 := by omega
      rw [h1, h2]
    rw [hq]; exact main_step c e
  · exact ⟨0, 0, rfl⟩

end Sz22_2003_unofficial_160
