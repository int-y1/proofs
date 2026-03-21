import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz21_140_unofficial #122: [77/15, 9/91, 26/3, 5/11, 33/2]

Vector representation:
```
 0 -1 -1  1  1  0
 0  2  0 -1  0 -1
 1 -1  0  0  0  1
 0  0  1  0 -1  0
-1  1  0  0  1  0
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz21_140_unofficial_122

def Q := ℕ × ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a, b+1, c+1, d, e, f⟩ => some ⟨a, b, c, d+1, e+1, f⟩
  | ⟨a, b, c, d+1, e, f+1⟩ => some ⟨a, b+2, c, d, e, f⟩
  | ⟨a, b+1, c, d, e, f⟩ => some ⟨a+1, b, c, d, e, f+1⟩
  | ⟨a, b, c, d, e+1, f⟩ => some ⟨a, b, c+1, d, e, f⟩
  | ⟨a+1, b, c, d, e, f⟩ => some ⟨a, b+1, c, d, e+1, f⟩
  | _ => none

-- Phase 1: R3 repeated: b → a,f (when c=0, d=0)
theorem b_to_af : ∀ k, ∀ a b e f, ⟨a, b+k, 0, 0, e, f⟩ [fm]⊢* ⟨a+k, b, 0, 0, e, f+k⟩ := by
  intro k; induction' k with k h <;> intro a b e f
  · exists 0
  rw [show b + (k + 1) = (b + k) + 1 from by ring]
  step fm
  apply stepStar_trans (h _ _ _ _)
  ring_nf; finish

-- Phase 2: R4 repeated: e → c
theorem e_to_c : ∀ k, ∀ a c e f, ⟨a, 0, c, 0, e+k, f⟩ [fm]⊢* ⟨a, 0, c+k, 0, e, f⟩ := by
  intro k; induction' k with k h <;> intro a c e f
  · exists 0
  rw [show e + (k + 1) = (e + k) + 1 from by ring]
  step fm
  apply stepStar_trans (h _ _ _ _)
  ring_nf; finish

-- R2 drain: when c=0, drains d and f together
theorem r2_drain : ∀ k, ∀ a b d e, ⟨a, b, 0, d+k, e, k⟩ [fm]⊢* ⟨a, b+2*k, 0, d, e, 0⟩ := by
  intro k; induction' k with k h <;> intro a b d e
  · exists 0
  rw [show d + (k + 1) = (d + k) + 1 from by ring]
  step fm
  apply stepStar_trans (h _ _ _ _)
  ring_nf; finish

-- General inner loop: (a, 2, C, d, e, C+d) →* (a, C+2*d+2, 0, 0, e+C, 0)
-- By strong induction on C.
theorem gen_inner : ∀ C, ∀ a d e, ⟨a, 2, C, d, e, C+d⟩ [fm]⊢* ⟨a, C+2*d+2, 0, 0, e+C, 0⟩ := by
  intro C; induction' C using Nat.strongRecOn with C ih; intro a d e
  rcases C with _ | _ | C
  · -- C=0: (a, 2, 0, d, e, 0+d)
    simp only [Nat.zero_add]
    -- Now goal: (a, 2, 0, d, e, d) →* (a, 2*d+2, 0, 0, e, 0)
    have h := r2_drain d a 2 0 e
    simp only [Nat.zero_add] at h
    refine stepStar_trans h ?_
    ring_nf; finish
  · -- C=1: (a, 2, 1, d, e, 1+d)
    -- R1: b=2>=1, c=1>=1 → (a, 1, 0, d+1, e+1, 1+d)
    rw [show 1 + d = d + 1 from by ring]
    step fm
    -- (a, 1, 0, d+1, e+1, d+1). R2 fires (d+1>=1, f=d+1>=1).
    have h := r2_drain (d + 1) a 1 0 (e + 1)
    simp only [Nat.zero_add] at h
    refine stepStar_trans h ?_
    ring_nf; finish
  · -- C+2: (a, 2, C+2, d, e, (C+2)+d)
    -- R1: b=2>=1, c=C+2>=1 → (a, 1, C+1, d+1, e+1, C+2+d)
    rw [show C + 2 + d = d + (C + 2) from by ring,
        show C + 2 = (C + 1) + 1 from by ring]
    step fm
    -- (a, 1, C+1, d+1, e+1, d+(C+2))
    -- R1: b=1>=1, c=C+1>=1 → (a, 0, C, d+2, e+2, d+(C+2))
    rw [show d + (C + 2) = (d + 1) + (C + 1) from by ring]
    step fm
    -- (a, 0, C, d+2, e+1+1, (d+1)+(C+1))
    -- R2: d+2>=1, f=(d+1)+(C+1)>=1 → (a, 2, C, d+1, e+1+1, (d+1)+(C+1)-1)
    rw [show d + 2 = (d + 1) + 1 from by ring,
        show (d + 1) + (C + 1) = (C + (d + 1)) + 1 from by ring]
    step fm
    -- (a, 2, C, d+1, e+1+1, C+(d+1))
    have h := ih C (by omega) a (d + 1) (e + 1 + 1)
    refine stepStar_trans h ?_
    ring_nf; finish

-- Main transition: (a, n+1, 0, 0, n+1, 0) →⁺ (a+n, n+2, 0, 0, n+2, 0)
theorem main_trans : ⟨a, n+1, 0, 0, n+1, 0⟩ [fm]⊢⁺ ⟨a+n, n+2, 0, 0, n+2, 0⟩ := by
  -- Phase 1: R3 x (n+1): →* (a+n+1, 0, 0, 0, n+1, n+1)
  apply stepStar_stepPlus_stepPlus (c₂ := ⟨a+n+1, 0, 0, 0, n+1, n+1⟩)
  · have h := b_to_af (n + 1) a 0 (n + 1) 0
    simp only [Nat.zero_add] at h
    convert h using 2
  -- Phase 2: R4 x (n+1): →* (a+n+1, 0, n+1, 0, 0, n+1)
  apply stepStar_stepPlus_stepPlus (c₂ := ⟨a+n+1, 0, n+1, 0, 0, n+1⟩)
  · have h := e_to_c (n + 1) (a + n + 1) 0 0 (n + 1)
    simp only [Nat.zero_add] at h
    exact h
  -- Phase 3: R5 step then inner
  rw [show a + n + 1 = (a + n) + 1 from by ring]
  apply step_stepStar_stepPlus
  · show fm ⟨(a + n) + 1, 0, n + 1, 0, 0, n + 1⟩ = some ⟨a + n, 1, n + 1, 0, 1, n + 1⟩
    simp [fm]
  -- (a+n, 1, n+1, 0, 1, n+1)
  -- R1: b=1>=1, c=n+1>=1 → (a+n, 0, n, 1, 2, n+1)
  rw [show n + 1 = n + 1 from rfl]
  step fm
  -- (a+n, 0, n, 1, 1+1, n+1)
  -- R2: d=1>=1, f=n+1>=1 → (a+n, 2, n, 0, 1+1, n)
  rw [show n + 1 = n + 1 from rfl]
  step fm
  -- (a+n, 2, n, 0, 1+1, n) - apply gen_inner
  have h := gen_inner n (a + n) 0 (1 + 1)
  rw [show n + 0 = n from by ring] at h
  refine stepStar_trans h ?_
  ring_nf; finish

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨0, 1, 0, 0, 1, 0⟩) (by execute fm 1)
  apply progress_nonhalt_simple (fm := fm) (A := ℕ × ℕ)
    (fun ⟨a, n⟩ ↦ ⟨a, n+1, 0, 0, n+1, 0⟩) ⟨0, 0⟩
  intro ⟨a, n⟩; exact ⟨⟨a+n, n+1⟩, main_trans⟩
