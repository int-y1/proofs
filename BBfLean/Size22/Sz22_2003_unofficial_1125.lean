import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #1125: [5/6, 44/35, 1183/2, 3/11, 15/13]

Vector representation:
```
-1 -1  1  0  0  0
 2  0 -1 -1  1  0
-1  0  0  1  0  2
 0  1  0  0 -1  0
 0  1  1  0  0 -1
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_1125

def Q := ℕ × ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a+1, b+1, c, d, e, f⟩ => some ⟨a, b, c+1, d, e, f⟩
  | ⟨a, b, c+1, d+1, e, f⟩ => some ⟨a+2, b, c, d, e+1, f⟩
  | ⟨a+1, b, c, d, e, f⟩ => some ⟨a, b, c, d+1, e, f+2⟩
  | ⟨a, b, c, d, e+1, f⟩ => some ⟨a, b+1, c, d, e, f⟩
  | ⟨a, b, c, d, e, f+1⟩ => some ⟨a, b+1, c+1, d, e, f⟩
  | _ => none

-- R3 drain: (a+k, 0, 0, d, e, f) →* (a, 0, 0, d+k, e, f+2*k)
theorem r3_drain : ∀ k a d e f, ⟨a + k, 0, 0, d, e, f⟩ [fm]⊢* ⟨a, 0, 0, d + k, e, f + 2 * k⟩ := by
  intro k; induction' k with k ih <;> intro a d e f
  · exists 0
  · rw [show a + (k + 1) = (a + k) + 1 from by ring]
    step fm
    apply stepStar_trans (ih a (d + 1) e (f + 2))
    ring_nf; finish

-- R4 drain: (0, b, 0, d, e+k, f) →* (0, b+k, 0, d, e, f)
theorem r4_drain : ∀ k b d e f, ⟨0, b, 0, d, e + k, f⟩ [fm]⊢* ⟨0, b + k, 0, d, e, f⟩ := by
  intro k; induction' k with k ih <;> intro b d e f
  · exists 0
  · rw [show e + (k + 1) = (e + k) + 1 from by ring]
    step fm
    apply stepStar_trans (ih (b + 1) d e f)
    ring_nf; finish

-- Interleaved R2+R1 chain:
-- (0, 2*d+1, c+1, d+1, e, f) →* (1, 0, c+d+1, 0, e+d+1, f)
theorem interleaved : ∀ d c e f, ⟨0, 2 * d + 1, c + 1, d + 1, e, f⟩ [fm]⊢* ⟨1, 0, c + d + 1, 0, e + d + 1, f⟩ := by
  intro d; induction' d with d ih <;> intro c e f
  · step fm; step fm; finish
  · rw [show 2 * (d + 1) + 1 = (2 * d + 1) + 1 + 1 from by ring,
        show (d + 1) + 1 = (d + 1) + 1 from rfl]
    step fm; step fm; step fm
    apply stepStar_trans (ih (c + 1) (e + 1) f)
    ring_nf; finish

-- R3+R2 chain: (a+1, 0, k, 0, e, f) →* (a+k+1, 0, 0, 0, e+k, f+2*k)
theorem r3r2_chain : ∀ k a e f, ⟨a + 1, 0, k, 0, e, f⟩ [fm]⊢* ⟨a + k + 1, 0, 0, 0, e + k, f + 2 * k⟩ := by
  intro k; induction' k with k ih <;> intro a e f
  · exists 0
  · step fm; step fm
    apply stepStar_trans (ih (a + 1) (e + 1) (f + 2))
    ring_nf; finish

-- Full phase composition: (n+2, 0, 0, 0, 2*n+2, (2*n+3)*(n+1)) →* (n+3, 0, 0, 0, 2*n+4, (2*n+5)*(n+2))
theorem full_phase (n : ℕ) :
    ⟨n + 2, 0, 0, 0, 2 * n + 2, (2 * n + 3) * (n + 1)⟩ [fm]⊢*
    ⟨n + 3, 0, 0, 0, 2 * n + 4, (2 * n + 5) * (n + 2)⟩ := by
  -- Phase 1: R3 drain (n+2 times)
  rw [show n + 2 = 0 + (n + 2) from by ring]
  apply stepStar_trans (r3_drain (n + 2) 0 0 (2 * n + 2) ((2 * n + 3) * (n + 1)))
  -- Now: (0, 0, 0, n+2, 2n+2, (2n+3)(n+1) + 2(n+2))
  -- Phase 2: R4 drain (2n+2 times)
  rw [show (2 * n + 3) * (n + 1) + 2 * (n + 2) = (2 * n + 5) * (n + 1) + 2 from by ring,
      show 2 * n + 2 = 0 + (2 * n + 2) from by ring]
  apply stepStar_trans (r4_drain (2 * n + 2) 0 (0 + (n + 2)) 0 ((2 * n + 5) * (n + 1) + 2))
  -- Now: (0, 2n+2, 0, n+2, 0, (2n+5)(n+1)+2)
  -- Phase 3: R5 step
  rw [show (2 * n + 5) * (n + 1) + 2 = ((2 * n + 5) * (n + 1) + 1) + 1 from by ring]
  step fm
  -- Now: (0, 2n+3, 1, n+2, 0, (2n+5)(n+1)+1)
  -- Phase 3b: Interleaved chain
  show ⟨0, 0 + (2 * n + 2) + 1, 1, 0 + (n + 2), 0, (2 * n + 5) * (n + 1) + 1⟩ [fm]⊢*
    ⟨n + 3, 0, 0, 0, 2 * n + 4, (2 * n + 5) * (0 + (n + 2))⟩
  rw [show 0 + (2 * n + 2) + 1 = 2 * (n + 1) + 1 from by ring,
      show (1 : ℕ) = 0 + 1 from by ring,
      show 0 + (n + 2) = (n + 1) + 1 from by ring]
  apply stepStar_trans (interleaved (n + 1) 0 0 ((2 * n + 5) * (n + 1) + 1))
  -- After interleaved: (1, 0, 0+(n+1)+1, 0, 0+(n+1)+1, (2n+5)(n+1)+1)
  -- Need: (n+3, 0, 0, 0, 2n+4, (2n+5)(n+2))
  show ⟨1, 0, 0 + (n + 1) + 1, 0, 0 + (n + 1) + 1, (2 * n + 5) * (n + 1) + 1⟩ [fm]⊢*
    ⟨n + 3, 0, 0, 0, 2 * n + 4, (2 * n + 5) * (n + 1 + 1)⟩
  rw [show 0 + (n + 1) + 1 = n + 2 from by ring,
      show n + 1 + 1 = n + 2 from by ring,
      show (1 : ℕ) = 0 + 1 from by ring]
  apply stepStar_trans (r3r2_chain (n + 2) 0 (n + 2) ((2 * n + 5) * (n + 1) + 1))
  rw [show 0 + (n + 2) + 1 = n + 3 from by ring,
      show (2 * n + 5) * (n + 1) + 1 + 2 * (n + 2) = (2 * n + 5) * (n + 2) from by ring,
      show n + 2 + (n + 2) = 2 * n + 4 from by ring]
  finish

-- Main transition as stepPlus
theorem main_trans (n : ℕ) :
    ⟨n + 2, 0, 0, 0, 2 * n + 2, (2 * n + 3) * (n + 1)⟩ [fm]⊢⁺
    ⟨n + 3, 0, 0, 0, 2 * n + 4, (2 * n + 5) * (n + 2)⟩ := by
  apply stepStar_stepPlus (full_phase n)
  simp [Q]

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨2, 0, 0, 0, 2, 3⟩)
  · execute fm 6
  apply progress_nonhalt_simple (fm := fm) (A := ℕ)
    (fun n ↦ ⟨n + 2, 0, 0, 0, 2 * n + 2, (2 * n + 3) * (n + 1)⟩) 0
  intro n; exact ⟨n + 1, main_trans n⟩

end Sz22_2003_unofficial_1125
