import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz21_140_unofficial #49: [35/6, 4/55, 143/2, 3/7, 6/13]

Vector representation:
```
-1 -1  1  1  0  0
 2  0 -1  0 -1  0
-1  0  0  0  1  1
 0  1  0 -1  0  0
 1  1  0  0  0 -1
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz21_140_unofficial_49

def Q := ℕ × ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a+1, b+1, c, d, e, f⟩ => some ⟨a, b, c+1, d+1, e, f⟩
  | ⟨a, b, c+1, d, e+1, f⟩ => some ⟨a+2, b, c, d, e, f⟩
  | ⟨a+1, b, c, d, e, f⟩ => some ⟨a, b, c, d, e+1, f+1⟩
  | ⟨a, b, c, d+1, e, f⟩ => some ⟨a, b+1, c, d, e, f⟩
  | ⟨a, b, c, d, e, f+1⟩ => some ⟨a+1, b+1, c, d, e, f⟩
  | _ => none

-- Phase 1: R3 repeated: a → e,f (when b=0, c=0)
theorem a_to_ef : ∀ k, ∀ a d e f, ⟨a+k, 0, 0, d, e, f⟩ [fm]⊢* ⟨a, 0, 0, d, e+k, f+k⟩ := by
  intro k; induction' k with k h <;> intro a d e f
  · exists 0
  rw [← Nat.add_assoc]
  step fm
  apply stepStar_trans (h _ _ _ _)
  ring_nf; finish

-- Phase 2: R4 repeated: d → b (when a=0, c=0)
theorem d_to_b : ∀ k, ∀ b d e f, ⟨0, b, 0, d+k, e, f⟩ [fm]⊢* ⟨0, b+k, 0, d, e, f⟩ := by
  intro k; induction' k with k h <;> intro b d e f
  · exists 0
  rw [← Nat.add_assoc]
  step fm
  apply stepStar_trans (h _ _ _ _)
  ring_nf; finish

-- R2 chain: c,e → a (when b=0)
theorem r2_chain : ∀ k, ∀ a c d f, ⟨a, 0, c+k, d, k, f⟩ [fm]⊢* ⟨a+2*k, 0, c, d, 0, f⟩ := by
  intro k; induction' k with k h <;> intro a c d f
  · exists 0
  rw [show c + (k + 1) = (c + k) + 1 from by ring]
  step fm
  apply stepStar_trans (h _ _ _ _)
  ring_nf; finish

-- Interleaved chain: (2, B, C, D, B+C, F) ->* (B+2+2*C, 0, 0, D+B, 0, F)
-- by strong induction on B
theorem interleaved : ∀ B, ∀ C D F, ⟨2, B, C, D, B+C, F⟩ [fm]⊢* ⟨B+2+2*C, 0, 0, D+B, 0, F⟩ := by
  intro B; induction' B using Nat.strongRecOn with B ih; intro C D F
  rcases B with _ | _ | B
  · -- B=0: (2, 0, C, D, C, F) -> R2 x C -> (2+2C, 0, 0, D, 0, F)
    simp only [Nat.zero_add]
    have h := r2_chain C 2 0 D F
    simp only [Nat.zero_add] at h
    refine stepStar_trans h ?_
    ring_nf; finish
  · -- B=1: (2, 1, C, D, C+1, F) -> R1 -> (1, 0, C+1, D+1, C+1, F)
    --        -> R2 x (C+1) -> (2C+3, 0, 0, D+1, 0, F)
    rw [show 1 + C = C + 1 from by ring]
    step fm
    have h := r2_chain (C + 1) 1 0 (D + 1) F
    simp only [Nat.zero_add] at h
    refine stepStar_trans h ?_
    ring_nf; finish
  · -- B=B+2: R1, R1, R2 then IH with B
    rw [show (B + 2) + C = B + (C + 2) from by ring]
    step fm
    rw [show B + (C + 2) = (B + 1) + (C + 1) from by ring]
    step fm
    rw [show (B + 1) + (C + 1) = B + (C + 2) from by ring]
    step fm
    have h := ih B (by omega) (C + 1) (D + 2) F
    rw [show B + (C + 1) = B + (C + 1) from rfl] at h
    refine stepStar_trans h ?_
    ring_nf; finish

-- Phase 3: (0, n, 0, 0, n+1, g+1) ->* (n+2, 0, 0, n+1, 0, g)
-- R5, R1, R2, then interleaved chain
theorem phase3 : ∀ n g, ⟨0, n, 0, 0, n+1, g+1⟩ [fm]⊢* ⟨n+2, 0, 0, n+1, 0, g⟩ := by
  intro n g
  -- R5: (0, n, 0, 0, n+1, g+1) -> (1, n+1, 0, 0, n+1, g)
  step fm
  -- R1: (1, n+1, 0, 0, n+1, g). a=1>=1, b=n+1>=1. R1 fires.
  rw [show n + 1 = n + 1 from rfl]
  step fm
  -- R2: (0, n, 1, 1, n+1, g). c=1>=1, e=n+1>=1. But a=0, so R1 doesn't fire. R2 fires.
  rw [show n + 1 = n + 1 from rfl]
  step fm
  -- Now at (2, n, 0, 1, n, g). This is (2, n, 0, 1, n+0, g).
  have h := interleaved n 0 1 g
  rw [show n + 0 = n from by ring] at h
  refine stepStar_trans h ?_
  ring_nf; finish

-- Main transition: (n+2, 0, 0, n+1, 0, F) ->+ (n+3, 0, 0, n+2, 0, F+n+1)
-- Uses phases 1, 2, and 3
theorem main_trans (n F : ℕ) : ⟨n+2, 0, 0, n+1, 0, F⟩ [fm]⊢⁺ ⟨n+3, 0, 0, n+2, 0, F+n+1⟩ := by
  -- Phase 1: R3 x (n+2): (n+2, 0, 0, n+1, 0, F) -> (0, 0, 0, n+1, n+2, F+n+2)
  apply stepStar_stepPlus_stepPlus (c₂ := ⟨0, 0, 0, n+1, n+2, F+n+2⟩)
  · have h := a_to_ef (n + 2) 0 (n + 1) 0 F
    simp only [Nat.zero_add] at h
    refine stepStar_trans h ?_
    ring_nf; finish
  -- Phase 2 + 3: (0, 0, 0, n+1, n+2, F+n+2) -> ... -> (n+3, 0, 0, n+2, 0, F+n+1)
  -- Phase 2: R4 x (n+1): (0, 0, 0, n+1, n+2, F+n+2) -> (0, n+1, 0, 0, n+2, F+n+2)
  apply stepStar_stepPlus_stepPlus (c₂ := ⟨0, n+1, 0, 0, n+2, F+n+2⟩)
  · have h := d_to_b (n + 1) 0 0 (n + 2) (F + n + 2)
    simp only [Nat.zero_add] at h
    refine stepStar_trans h ?_
    ring_nf; finish
  -- Phase 3: (0, n+1, 0, 0, n+2, F+n+2) -> (n+3, 0, 0, n+2, 0, F+n+1)
  -- This is phase3 with n' = n+1, g = F+n+1.
  -- phase3: (0, n', 0, 0, n'+1, g+1) ->* (n'+2, 0, 0, n'+1, 0, g)
  -- So n' = n+1, n'+1 = n+2, g+1 = F+n+2 means g = F+n+1.
  -- Result: (n+3, 0, 0, n+2, 0, F+n+1) ✓
  -- But we need stepPlus, not stepStar. Phase 3 starts with R5 which is a step.
  -- Actually, let me use the fact that phase3 has at least 3 steps (R5, R1, R2).
  -- Let's split: first R5 step gives stepPlus, then rest is stepStar.
  apply step_stepStar_stepPlus (c₂ := ⟨1, n+2, 0, 0, n+2, F+n+1⟩)
  · -- R5 step
    show fm ⟨0, n+1, 0, 0, n+2, (F + n + 1) + 1⟩ = some ⟨1, n+2, 0, 0, n+2, F+n+1⟩
    simp [fm]
  -- R1: (1, n+2, 0, 0, n+2, F+n+1) -> (0, n+1, 1, 1, n+2, F+n+1)
  rw [show n + 2 = (n + 1) + 1 from by ring]
  step fm
  -- R2: (0, n+1, 1, 1, n+2, F+n+1) -> (2, n+1, 0, 1, n+1, F+n+1)
  rw [show n + 2 = (n + 1) + 1 from by ring]
  step fm
  -- Now (2, n+1, 0, 1, n+1, F+n+1) = (2, n+1, 0, 1, (n+1)+0, F+n+1)
  have h := interleaved (n + 1) 0 1 (F + n + 1)
  rw [show (n + 1) + 0 = n + 1 from by ring] at h
  refine stepStar_trans h ?_
  ring_nf; finish

theorem nonhalt : ¬halts fm c₀ := by
  -- Bootstrap: c₀ = (1,0,0,0,0,0) reaches (2,0,0,1,0,0) in 4 steps
  apply stepStar_not_halts_not_halts (c₂ := ⟨2, 0, 0, 1, 0, 0⟩) (by execute fm 4)
  -- Canonical form: C(n, F) = (n+2, 0, 0, n+1, 0, F)
  -- Transition: (n+2, 0, 0, n+1, 0, F) ->+ (n+3, 0, 0, n+2, 0, F+n+1)
  apply progress_nonhalt_simple (fm := fm) (A := ℕ × ℕ)
    (fun ⟨n, F⟩ ↦ ⟨n+2, 0, 0, n+1, 0, F⟩) ⟨0, 0⟩
  intro ⟨n, F⟩; exact ⟨⟨n+1, F+n+1⟩, main_trans n F⟩

end Sz21_140_unofficial_49
