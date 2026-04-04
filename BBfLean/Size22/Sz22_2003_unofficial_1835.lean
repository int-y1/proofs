import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #1835: [9/10, 77/2, 52/21, 5/13, 15/11]

Vector representation:
```
-1  2 -1  0  0  0
-1  0  0  1  1  0
 2 -1  0 -1  0  1
 0  0  1  0  0 -1
 0  1  1  0 -1  0
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_1835

def Q := ℕ × ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a+1, b, c+1, d, e, f⟩ => some ⟨a, b+2, c, d, e, f⟩
  | ⟨a+1, b, c, d, e, f⟩ => some ⟨a, b, c, d+1, e+1, f⟩
  | ⟨a, b+1, c, d+1, e, f⟩ => some ⟨a+2, b, c, d, e, f+1⟩
  | ⟨a, b, c, d, e, f+1⟩ => some ⟨a, b, c+1, d, e, f⟩
  | ⟨a, b, c, d, e+1, f⟩ => some ⟨a, b+1, c+1, d, e, f⟩
  | _ => none

-- R4 chain: (0,0,c,d,e,f+k) →* (0,0,c+k,d,e,f)
theorem r4_chain : ∀ k c d e f, ⟨0, 0, c, d, e, f + k⟩ [fm]⊢* ⟨0, 0, c + k, d, e, f⟩ := by
  intro k; induction' k with k ih <;> intro c d e f
  · exists 0
  · rw [show f + (k + 1) = (f + k) + 1 from by ring]
    step fm
    apply stepStar_trans (ih (c + 1) d e f)
    ring_nf; finish

-- R3+R1+R1 chain: (0, 1, c+2k, d+k, e, f) →* (0, 3k+1, c, d, e, f+k)
theorem r3r1r1_chain : ∀ k c d e f,
    ⟨0, 1, c + 2 * k, d + k, e, f⟩ [fm]⊢*
    ⟨0, 3 * k + 1, c, d, e, f + k⟩ := by
  intro k; induction' k with k ih <;> intro c d e f
  · exists 0
  · rw [show c + 2 * (k + 1) = (c + 2) + 2 * k from by ring,
        show d + (k + 1) = (d + 1) + k from by ring]
    apply stepStar_trans (ih (c + 2) (d + 1) e f)
    rw [show c + 2 = c + 1 + 1 from by ring,
        show 3 * k + 1 = (3 * k) + 1 from by ring]
    step fm; step fm; step fm
    ring_nf; finish

-- R3+R2+R2 chain: (0, k+1, 0, d+1, e, f) →* (0, 1, 0, d+k+1, e+2k, f+k)
theorem r3r2r2_chain : ∀ k d e f,
    ⟨0, k + 1, 0, d + 1, e, f⟩ [fm]⊢*
    ⟨0, 1, 0, d + k + 1, e + 2 * k, f + k⟩ := by
  intro k; induction' k with k ih <;> intro d e f
  · exists 0
  · rw [show (k + 1) + 1 = k + 1 + 1 from rfl]
    step fm; step fm; step fm
    rw [show d + 1 + 1 = (d + 1) + 1 from by ring]
    apply stepStar_trans (ih (d + 1) (e + 2) (f + 1))
    ring_nf; finish

-- Closing: (0, 1, 0, d+1, e, f) →⁺ (0, 0, 0, d+2, e+2, f+1)
theorem closing : ⟨0, 1, 0, d + 1, e, f⟩ [fm]⊢⁺ ⟨0, 0, 0, d + 2, e + 2, f + 1⟩ := by
  step fm; step fm; step fm; finish

-- Compose all phases into a single ⊢* from the state after R5
theorem phases234 (m k : ℕ) :
    (⟨0, 1, 2 * m + 4, m + k + 3, m + 5 * k + 4, 0⟩ : Q) [fm]⊢*
    ⟨0, 0, 0, 3 * m + k + 8, 7 * m + 5 * k + 18, 4 * m + 9⟩ := by
  -- Phase 3: R3+R1+R1 x (m+2)
  rw [show 2 * m + 4 = 0 + 2 * (m + 2) from by ring,
      show m + k + 3 = (k + 1) + (m + 2) from by ring]
  apply stepStar_trans
    (r3r1r1_chain (m + 2) 0 (k + 1) (m + 5 * k + 4) 0)
  -- (0, 3(m+2)+1, 0, k+1, m+5k+4, m+2)
  rw [show 3 * (m + 2) + 1 = (3 * m + 6) + 1 from by ring,
      show 0 + (m + 2) = m + 2 from by ring]
  -- Phase 4: R3+R2+R2 x (3m+6)
  apply stepStar_trans
    (r3r2r2_chain (3 * m + 6) k (m + 5 * k + 4) (m + 2))
  -- (0, 1, 0, k+3m+7, 7m+5k+16, 4m+8)
  rw [show k + (3 * m + 6) + 1 = (3 * m + k + 6) + 1 from by ring,
      show m + 5 * k + 4 + 2 * (3 * m + 6) = 7 * m + 5 * k + 16 from by ring,
      show m + 2 + (3 * m + 6) = 4 * m + 8 from by ring]
  -- Closing
  apply stepPlus_stepStar closing

-- Main transition
theorem main_trans (m k : ℕ) :
    (⟨0, 0, 0, m + k + 3, m + 5 * k + 5, 2 * m + 3⟩ : Q) [fm]⊢⁺
    ⟨0, 0, 0, 3 * m + k + 8, 7 * m + 5 * k + 18, 4 * m + 9⟩ := by
  -- Phase 1: R4
  rw [show (2 * m + 3 : ℕ) = 0 + (2 * m + 3) from by ring]
  apply stepStar_stepPlus_stepPlus
    (r4_chain (2 * m + 3) 0 (m + k + 3) (m + 5 * k + 5) 0)
  -- (0, 0, 2m+3, m+k+3, m+5k+5, 0)
  rw [show 0 + (2 * m + 3) = 2 * m + 3 from by ring,
      show m + 5 * k + 5 = (m + 5 * k + 4) + 1 from by ring]
  -- Phase 2: R5 + remaining phases
  apply step_stepStar_stepPlus (by rfl)
  -- (0, 1, 2m+4, m+k+3, m+5k+4, 0)
  show ⟨0, 0 + 1, 2 * m + 3 + 1, m + k + 3, m + 5 * k + 4, 0⟩ [fm]⊢*
    ⟨0, 0, 0, 3 * m + k + 8, 7 * m + 5 * k + 18, 4 * m + 9⟩
  rw [show 0 + 1 = 1 from by ring,
      show 2 * m + 3 + 1 = 2 * m + 4 from by ring]
  exact phases234 m k

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨0, 0, 0, 3, 5, 3⟩) (by execute fm 11)
  apply progress_nonhalt_simple (fm := fm) (A := ℕ × ℕ)
    (fun ⟨m, k⟩ ↦ ⟨0, 0, 0, m + k + 3, m + 5 * k + 5, 2 * m + 3⟩) ⟨0, 0⟩
  intro ⟨m, k⟩
  refine ⟨⟨2 * m + 3, m + k + 2⟩, ?_⟩
  show (⟨0, 0, 0, m + k + 3, m + 5 * k + 5, 2 * m + 3⟩ : Q) [fm]⊢⁺
    ⟨0, 0, 0, (2 * m + 3) + (m + k + 2) + 3,
     (2 * m + 3) + 5 * (m + k + 2) + 5, 2 * (2 * m + 3) + 3⟩
  rw [show (2 * m + 3) + (m + k + 2) + 3 = 3 * m + k + 8 from by ring,
      show (2 * m + 3) + 5 * (m + k + 2) + 5 = 7 * m + 5 * k + 18 from by ring,
      show 2 * (2 * m + 3) + 3 = 4 * m + 9 from by ring]
  exact main_trans m k
