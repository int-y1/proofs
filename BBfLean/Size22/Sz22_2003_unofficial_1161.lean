import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #1161: [5/6, 44/35, 91/2, 3/11, 18/13]

Vector representation:
```
-1 -1  1  0  0  0
 2  0 -1 -1  1  0
-1  0  0  1  0  1
 0  1  0  0 -1  0
 1  2  0  0  0 -1
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_1161

def Q := ℕ × ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a+1, b+1, c, d, e, f⟩ => some ⟨a, b, c+1, d, e, f⟩
  | ⟨a, b, c+1, d+1, e, f⟩ => some ⟨a+2, b, c, d, e+1, f⟩
  | ⟨a+1, b, c, d, e, f⟩ => some ⟨a, b, c, d+1, e, f+1⟩
  | ⟨a, b, c, d, e+1, f⟩ => some ⟨a, b+1, c, d, e, f⟩
  | ⟨a, b, c, d, e, f+1⟩ => some ⟨a+1, b+2, c, d, e, f⟩
  | _ => none

theorem e_to_b : ∀ k, ∀ b, ⟨0, b, 0, d, e + k, f⟩ [fm]⊢* ⟨0, b + k, 0, d, e, f⟩ := by
  intro k; induction' k with k ih <;> intro b
  · exists 0
  · rw [show e + (k + 1) = (e + k) + 1 from by ring]
    step fm
    apply stepStar_trans (ih (b + 1))
    ring_nf; finish

theorem a_to_df : ∀ k, ∀ d f, ⟨a + k, 0, 0, d, e, f⟩ [fm]⊢* ⟨a, 0, 0, d + k, e, f + k⟩ := by
  intro k; induction' k with k ih <;> intro d f
  · exists 0
  · rw [show a + (k + 1) = (a + k) + 1 from by ring]
    step fm
    apply stepStar_trans (ih (d + 1) (f + 1))
    ring_nf; finish

theorem r2r1r1_chain : ∀ k, ∀ b c d e,
    ⟨0, b + 2 * k, c + 1, d + k, e, f⟩ [fm]⊢* ⟨0, b, c + 1 + k, d, e + k, f⟩ := by
  intro k; induction' k with k ih <;> intro b c d e
  · exists 0
  · rw [show b + 2 * (k + 1) = (b + 2 * k) + 2 from by ring,
        show d + (k + 1) = (d + k) + 1 from by ring]
    step fm
    step fm
    step fm
    rw [show c + 1 + 1 = (c + 1) + 1 from by ring]
    apply stepStar_trans (ih b (c + 1) d (e + 1))
    ring_nf; finish

theorem r2r3_chain : ∀ k, ∀ a e f,
    ⟨a, 0, k + 1, 1, e, f⟩ [fm]⊢* ⟨a + k, 0, 1, 1, e + k, f + k⟩ := by
  intro k; induction' k with k ih <;> intro a e f
  · exists 0
  · step fm
    step fm
    apply stepStar_trans (ih (a + 1) (e + 1) (f + 1))
    ring_nf; finish

-- Phase 1-3: e_to_b + R5 + R1.
-- (0, 0, 0, n+2, 2n+2, F+1) →* (0, 2n+3, 1, n+2, 0, F)
theorem phase_1_3 (n F : ℕ) :
    ⟨0, 0, 0, n + 2, 2 * n + 2, F + 1⟩ [fm]⊢*
    ⟨0, 2 * n + 3, 1, n + 2, 0, F⟩ := by
  rw [show 2 * n + 2 = 0 + (2 * n + 2) from by ring]
  apply stepStar_trans (e_to_b (2 * n + 2) 0 (d := n + 2) (e := 0) (f := F + 1))
  rw [show 0 + (2 * n + 2) = 2 * n + 2 from by ring]
  -- State: (0, 2n+2, 0, n+2, 0, F+1). R5 fires.
  step fm
  -- State: (1, 2n+4, 0, n+2, 0, F)
  rw [show 2 * n + 2 + 2 = (2 * n + 3) + 1 from by ring]
  step fm
  -- State: (0, 2n+3, 1, n+2, 0, F)
  finish

-- Phase 4: r2r1r1_chain.
-- (0, 2n+3, 1, n+2, 0, F) →* (0, 1, n+2, 1, n+1, F)
theorem phase_4 (n F : ℕ) :
    ⟨0, 2 * n + 3, 1, n + 2, 0, F⟩ [fm]⊢*
    ⟨0, 1, n + 2, 1, n + 1, F⟩ := by
  rw [show 2 * n + 3 = 1 + 2 * (n + 1) from by ring,
      show (1 : ℕ) = 0 + 1 from by ring,
      show n + 2 = 1 + (n + 1) from by ring,
      show (0 : ℕ) = 0 from rfl]
  apply stepStar_trans (r2r1r1_chain (n + 1) 1 0 1 0 (f := F))
  rw [show 0 + 1 + (n + 1) = n + 2 from by ring,
      show 0 + (n + 1) = n + 1 from by ring]
  finish

-- Phase 5-7: R2 + R1 + R3.
-- (0, 1, n+2, 1, n+1, F) →* (0, 0, n+2, 1, n+2, F+1)
theorem phase_5_7 (n F : ℕ) :
    ⟨0, 1, n + 2, 1, n + 1, F⟩ [fm]⊢*
    ⟨0, 0, n + 2, 1, n + 2, F + 1⟩ := by
  -- R2: need c+1 = n+2, d+1 = 1. So c = n+1, d = 0.
  rw [show n + 2 = (n + 1) + 1 from by ring,
      show (1 : ℕ) = 0 + 1 from by ring]
  step fm
  -- R1: need a+1 = 2, b+1 = 1. So a = 1, b = 0.
  step fm
  -- R3: need a+1 = 1. So a = 0.
  step fm
  ring_nf; finish

-- Phase 8: r2r3_chain.
-- (0, 0, n+2, 1, n+2, F) →* (n+1, 0, 1, 1, 2n+3, F+n+1)
theorem phase_8 (n F : ℕ) :
    ⟨0, 0, n + 2, 1, n + 2, F⟩ [fm]⊢*
    ⟨n + 1, 0, 1, 1, 2 * n + 3, F + n + 1⟩ := by
  rw [show n + 2 = (n + 1) + 1 from by ring]
  apply stepStar_trans (r2r3_chain (n + 1) 0 (n + 2) F)
  rw [show (n + 2) + (n + 1) = 2 * n + 3 from by ring]
  ring_nf; finish

-- Phase 9-10: R2 + R3 chain.
-- (n+1, 0, 1, 1, 2n+3, F) →⁺ (0, 0, 0, n+3, 2n+4, F+n+3)
theorem phase_9_10 (n F : ℕ) :
    ⟨n + 1, 0, 1, 1, 2 * n + 3, F⟩ [fm]⊢⁺
    ⟨0, 0, 0, n + 3, 2 * n + 4, F + n + 3⟩ := by
  -- R2: c+1 = 1 → c = 0, d+1 = 1 → d = 0
  step fm
  -- State: (n+3, 0, 0, 0, 2n+4, F)
  rw [show (n + 1) + 2 = n + 3 from by ring,
      show (2 * n + 3) + 1 = 2 * n + 4 from by ring]
  -- R3 (first step, to stay in ⊢⁺)
  step fm
  -- State: (n+2, 0, 0, 1, 2n+4, F+1)
  rw [show F + 1 = F + 1 from rfl]
  -- Remaining R3 via a_to_df
  rw [show n + 2 = 0 + (n + 2) from by ring]
  apply stepStar_trans (a_to_df (n + 2) (a := 0) (e := 2 * n + 4) 1 (F + 1))
  ring_nf; finish

theorem main_trans (n : ℕ) :
    ⟨0, 0, 0, n + 2, 2 * n + 2, (n + 1) * (n + 2) + 1⟩ [fm]⊢⁺
    ⟨0, 0, 0, n + 3, 2 * n + 4, (n + 2) * (n + 3) + 1⟩ := by
  -- Compose phases 1-3, 4, 5-7, 8, 9-10
  -- Phase 1-3: →* (0, 2n+3, 1, n+2, 0, (n+1)*(n+2))
  apply stepStar_stepPlus_stepPlus (phase_1_3 n ((n + 1) * (n + 2)))
  -- Phase 4: →* (0, 1, n+2, 1, n+1, (n+1)*(n+2))
  apply stepStar_stepPlus_stepPlus (phase_4 n ((n + 1) * (n + 2)))
  -- Phase 5-7: →* (0, 0, n+2, 1, n+2, (n+1)*(n+2)+1)
  apply stepStar_stepPlus_stepPlus (phase_5_7 n ((n + 1) * (n + 2)))
  -- Phase 8: →* (n+1, 0, 1, 1, 2n+3, (n+1)*(n+2)+1+(n+1))
  apply stepStar_stepPlus_stepPlus (phase_8 n ((n + 1) * (n + 2) + 1))
  -- Phase 9-10: →⁺ (0, 0, 0, n+3, 2n+4, ...)
  -- F = (n+1)*(n+2)+1+(n+1) = (n+1)*(n+2)+(n+2) = (n+2)²
  -- phase_9_10 gives target f: F + n + 3 = (n+2)² + n + 3 = n²+4n+4+n+3 = n²+5n+7
  -- (n+2)*(n+3)+1 = n²+5n+6+1 = n²+5n+7. Equal!
  show ⟨n + 1, 0, 1, 1, 2 * n + 3, (n + 1) * (n + 2) + 1 + (n + 1)⟩ [fm]⊢⁺
       ⟨0, 0, 0, n + 3, 2 * n + 4, (n + 2) * (n + 3) + 1⟩
  have h := phase_9_10 n ((n + 1) * (n + 2) + 1 + (n + 1))
  convert h using 2; ring_nf

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨0, 0, 0, 2, 2, 3⟩)
  · execute fm 9
  apply progress_nonhalt_simple (fm := fm) (A := ℕ)
    (fun n ↦ ⟨0, 0, 0, n + 2, 2 * n + 2, (n + 1) * (n + 2) + 1⟩) 0
  intro n; exists n + 1
  show ⟨0, 0, 0, n + 2, 2 * n + 2, (n + 1) * (n + 2) + 1⟩ [fm]⊢⁺
       ⟨0, 0, 0, n + 1 + 2, 2 * (n + 1) + 2, (n + 1 + 1) * (n + 1 + 2) + 1⟩
  exact main_trans n
