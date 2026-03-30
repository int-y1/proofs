import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #980: [4/15, 33/14, 65/2, 7/11, 21/13]

Vector representation:
```
 2 -1 -1  0  0  0
-1  1  0 -1  1  0
-1  0  1  0  0  1
 0  0  0  1 -1  0
 0  1  0  1  0 -1
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_980

def Q := ℕ × ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a, b+1, c+1, d, e, f⟩ => some ⟨a+2, b, c, d, e, f⟩
  | ⟨a+1, b, c, d+1, e, f⟩ => some ⟨a, b+1, c, d, e+1, f⟩
  | ⟨a+1, b, c, d, e, f⟩ => some ⟨a, b, c+1, d, e, f+1⟩
  | ⟨a, b, c, d, e+1, f⟩ => some ⟨a, b, c, d+1, e, f⟩
  | ⟨a, b, c, d, e, f+1⟩ => some ⟨a, b+1, c, d+1, e, f⟩
  | _ => none

-- R4 chain: drain e into d
theorem r4_chain : ∀ k, ∀ c d f, ⟨0, 0, c, d, k, f⟩ [fm]⊢* ⟨0, 0, c, d + k, 0, f⟩ := by
  intro k; induction' k with k ih <;> intro c d f
  · exists 0
  · rw [show (k : ℕ) + 1 = k + 1 from rfl]
    step fm
    apply stepStar_trans (ih c (d + 1) f)
    ring_nf; finish

-- R3 chain: a→c,f
theorem r3_chain : ∀ k, ∀ c e f, ⟨k, 0, c, 0, e, f⟩ [fm]⊢* ⟨0, 0, c + k, 0, e, f + k⟩ := by
  intro k; induction' k with k ih <;> intro c e f
  · exists 0
  · rw [show (k : ℕ) + 1 = k + 1 from rfl]
    step fm
    apply stepStar_trans (ih (c + 1) e (f + 1))
    ring_nf; finish

-- R5 chain: f→b,d (one step)
-- (0, 0, c, d, 0, f+1) → (0, 1, c, d+1, 0, f)

-- R1 step: (a, b+1, c+1, d, e, f) → (a+2, b, c, d, e, f)

-- R2-R1 interleaved chain: eats c and d simultaneously
-- (a+1, 0, c+k, d+k, e, f) →* (a+k+1, 0, c, d, e+k, f)
theorem r2r1_chain : ∀ k, ∀ a c d e f,
    ⟨a + 1, 0, c + k, d + k, e, f⟩ [fm]⊢* ⟨a + k + 1, 0, c, d, e + k, f⟩ := by
  intro k; induction' k with k ih <;> intro a c d e f
  · ring_nf; finish
  · rw [show c + (k + 1) = (c + k) + 1 from by ring,
        show d + (k + 1) = (d + k) + 1 from by ring]
    step fm
    step fm
    apply stepStar_trans (ih (a + 1) c d (e + 1) f)
    ring_nf; finish

-- Main transition: C(n,f) ⊢⁺ C(n+1, f+n+3)
-- C(n,f) = (0, 0, n+2, 0, n+1, f)
-- Phases:
-- 1. R4 chain (n+1 steps): (0,0,n+2,0,n+1,f) →* (0,0,n+2,n+1,0,f)
-- 2. R5: (0,0,n+2,n+1,0,f) → (0,1,n+2,n+2,0,f-1)   [f = f'+1]
-- 3. R1: (0,1,n+2,n+2,0,f') → (2,0,n+1,n+2,0,f')
-- 4. R2-R1 chain (n+1 rounds): (2,0,n+1,n+2,0,f') →* (n+3,0,0,1,n+1,f')
-- 5. R2: (n+3,0,0,1,n+1,f') → (n+2,1,0,0,n+2,f')
-- 6. R3: (n+2,1,0,0,n+2,f') → (n+1,1,1,0,n+2,f'+1) = (n+1,1,1,0,n+2,f)
-- 7. R1: (n+1,1,1,0,n+2,f) → (n+3,0,0,0,n+2,f)
-- 8. R3 chain (n+3 steps): (n+3,0,0,0,n+2,f) →* (0,0,n+3,0,n+2,f+n+3)
theorem main_trans (n f : ℕ) :
    ⟨0, 0, n + 2, 0, n + 1, f + 1⟩ [fm]⊢⁺ ⟨0, 0, n + 3, 0, n + 2, f + 1 + (n + 3)⟩ := by
  -- Phase 1: R4 chain
  have h1 : ⟨0, 0, n + 2, 0, n + 1, f + 1⟩ [fm]⊢* ⟨0, 0, n + 2, n + 1, 0, f + 1⟩ := by
    have := r4_chain (n + 1) (n + 2) 0 (f + 1)
    rw [show 0 + (n + 1) = n + 1 from by ring] at this
    exact this
  -- Phase 2: R5
  have h2 : ⟨0, 0, n + 2, n + 1, 0, f + 1⟩ [fm]⊢⁺ ⟨0, 1, n + 2, n + 2, 0, f⟩ := by
    rw [show n + 1 = (n + 1) from rfl, show n + 2 = (n + 1) + 1 from by ring]
    step fm
    finish
  -- Phase 3: R1
  have h3 : ⟨0, 1, n + 2, n + 2, 0, f⟩ [fm]⊢* ⟨2, 0, n + 1, n + 2, 0, f⟩ := by
    rw [show n + 2 = (n + 1) + 1 from by ring]
    step fm
    finish
  -- Phase 4: R2-R1 chain (n+1 rounds)
  have h4 : ⟨2, 0, n + 1, n + 2, 0, f⟩ [fm]⊢* ⟨n + 3, 0, 0, 1, n + 1, f⟩ := by
    have := r2r1_chain (n + 1) 1 0 1 0 f
    rw [show 1 + (n + 1) + 1 = n + 3 from by ring,
        show 1 + 1 = 2 from rfl,
        show 0 + (n + 1) = n + 1 from by ring,
        show 1 + (n + 1) = n + 2 from by ring] at this
    exact this
  -- Phase 5: R2
  have h5 : ⟨n + 3, 0, 0, 1, n + 1, f⟩ [fm]⊢* ⟨n + 2, 1, 0, 0, n + 2, f⟩ := by
    rw [show n + 3 = (n + 2) + 1 from by ring]
    step fm
    ring_nf; finish
  -- Phase 6: R3
  have h6 : ⟨n + 2, 1, 0, 0, n + 2, f⟩ [fm]⊢* ⟨n + 1, 1, 1, 0, n + 2, f + 1⟩ := by
    rw [show n + 2 = (n + 1) + 1 from by ring]
    step fm
    ring_nf; finish
  -- Phase 7: R1
  have h7 : ⟨n + 1, 1, 1, 0, n + 2, f + 1⟩ [fm]⊢* ⟨n + 3, 0, 0, 0, n + 2, f + 1⟩ := by
    step fm
    ring_nf; finish
  -- Phase 8: R3 chain
  have h8 : ⟨n + 3, 0, 0, 0, n + 2, f + 1⟩ [fm]⊢* ⟨0, 0, n + 3, 0, n + 2, f + 1 + (n + 3)⟩ := by
    have := r3_chain (n + 3) 0 (n + 2) (f + 1)
    rw [show 0 + (n + 3) = n + 3 from by ring,
        show f + 1 + (n + 3) = f + 1 + (n + 3) from rfl] at this
    exact this
  -- Compose all phases
  exact stepStar_stepPlus_stepPlus h1
    (stepPlus_stepStar_stepPlus h2
      (stepStar_trans h3
        (stepStar_trans h4
          (stepStar_trans h5
            (stepStar_trans h6
              (stepStar_trans h7 h8))))))

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨0, 0, 2, 0, 1, 3⟩) (by execute fm 8)
  apply progress_nonhalt_simple (fm := fm) (A := ℕ × ℕ)
    (fun ⟨n, f⟩ ↦ ⟨0, 0, n + 2, 0, n + 1, f + 1⟩) ⟨0, 2⟩
  intro ⟨n, f⟩
  refine ⟨⟨n + 1, f + n + 3⟩, ?_⟩
  show ⟨0, 0, n + 2, 0, n + 1, f + 1⟩ [fm]⊢⁺ ⟨0, 0, n + 1 + 2, 0, n + 1 + 1, f + n + 3 + 1⟩
  rw [show f + n + 3 + 1 = f + 1 + (n + 3) from by ring,
      show n + 1 + 2 = n + 3 from by ring,
      show n + 1 + 1 = n + 2 from by ring]
  exact main_trans n f
