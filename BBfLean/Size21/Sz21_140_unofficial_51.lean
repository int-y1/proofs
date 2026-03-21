import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz21_140_unofficial #51: [35/6, 4/55, 847/2, 3/7, 5/11]

Vector representation:
```
-1 -1  1  1  0
 2  0 -1  0 -1
-1  0  0  1  2
 0  1  0 -1  0
 0  0  1  0 -1
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz21_140_unofficial_51

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a+1, b+1, c, d, e⟩ => some ⟨a, b, c+1, d+1, e⟩
  | ⟨a, b, c+1, d, e+1⟩ => some ⟨a+2, b, c, d, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b, c, d+1, e+2⟩
  | ⟨a, b, c, d+1, e⟩ => some ⟨a, b+1, c, d, e⟩
  | ⟨a, b, c, d, e+1⟩ => some ⟨a, b, c+1, d, e⟩
  | _ => none

-- R3 chain: (a+k, 0, 0, d, e) →* (a, 0, 0, d+k, e+2k)
theorem r3_chain : ∀ k, ∀ a d e, ⟨a+k, 0, 0, d, e⟩ [fm]⊢* ⟨a, 0, 0, d+k, e+2*k⟩ := by
  intro k; induction' k with k h <;> intro a d e
  · exists 0
  rw [show a + (k + 1) = (a + k) + 1 from by ring]
  step fm
  apply stepStar_trans (h _ _ _)
  ring_nf; finish

-- R4 chain: (0, b, 0, d+k, e) →* (0, b+k, 0, d, e)
theorem r4_chain : ∀ k, ∀ b d e, ⟨0, b, 0, d+k, e⟩ [fm]⊢* ⟨0, b+k, 0, d, e⟩ := by
  intro k; induction' k with k h <;> intro b d e
  · exists 0
  rw [show d + (k + 1) = (d + k) + 1 from by ring]
  step fm
  apply stepStar_trans (h _ _ _)
  ring_nf; finish

-- R2 chain: (a, 0, c+k, d, k) →* (a+2k, 0, c, d, 0)
theorem r2_chain : ∀ k, ∀ a c d, ⟨a, 0, c+k, d, k⟩ [fm]⊢* ⟨a+2*k, 0, c, d, 0⟩ := by
  intro k; induction' k with k h <;> intro a c d
  · exists 0
  rw [show c + (k + 1) = (c + k) + 1 from by ring]
  step fm
  apply stepStar_trans (h _ _ _)
  ring_nf; finish

-- Interleaved R1R1R2 chain:
-- Each round: b -= 2, c += 1, d += 2, e -= 1
-- (2, 2k, C, D, E+k) →* (2, 0, C+k, D+2k, E)
theorem r1r1r2_round : ∀ k, ∀ C D E, ⟨2, 2*k, C, D, E+k⟩ [fm]⊢* ⟨2, 0, C+k, D+2*k, E⟩ := by
  intro k; induction' k with k h <;> intro C D E
  · exists 0
  rw [show 2 * (k + 1) = (2 * k) + 1 + 1 from by ring,
      show E + (k + 1) = (E + k) + 1 from by ring]
  -- R1: (2, 2k+1+1, C, D, E+k+1) → (1, 2k+1, C+1, D+1, E+k+1)
  step fm
  -- Need to show: (1, 2k+1, C+1, D+1, E+k+1)
  rw [show 2 * k + 1 = (2 * k) + 1 from by ring]
  -- R1: (1, 2k+1, C+1, D+1, E+k+1) → (0, 2k, C+2, D+2, E+k+1)
  step fm
  -- R2: (0, 2k, C+2, D+2, E+k+1) → (2, 2k, C+1, D+2, E+k)
  rw [show E + k + 1 = (E + k) + 1 from by ring]
  step fm
  apply stepStar_trans (h _ _ _)
  ring_nf; finish

-- Middle phase: (0, 2n+2, 0, 0, 2n+3) →* (2n+3, 0, 0, 2n+3, 1)
theorem middle_phase (n : ℕ) : ⟨0, 2*n+2, 0, 0, 2*n+3⟩ [fm]⊢* ⟨2*n+3, 0, 0, 2*n+3, 1⟩ := by
  -- R5: (0, 2n+2, 0, 0, 2n+3) → (0, 2n+2, 1, 0, 2n+2)
  apply stepStar_trans (c₂ := ⟨0, 2*n+2, 1, 0, 2*n+2⟩)
  · rw [show 2 * n + 3 = (2 * n + 2) + 1 from by ring]; step fm; finish
  -- R2: (0, 2n+2, 1, 0, 2n+2) → (2, 2n+2, 0, 0, 2n+1)
  apply stepStar_trans (c₂ := ⟨2, 2*n+2, 0, 0, 2*n+1⟩)
  · rw [show 2 * n + 2 = (2 * n + 1) + 1 from by ring]; step fm; finish
  -- R1R1R2 rounds (n+1 rounds): (2, 2(n+1), 0, 0, n+(n+1)) →* (2, 0, n+1, 2(n+1), n)
  apply stepStar_trans (c₂ := ⟨2, 0, n+1, 2*n+2, n⟩)
  · have h := r1r1r2_round (n+1) 0 0 n
    rw [show 2 * (n + 1) = 2 * n + 2 from by ring,
        show n + (n + 1) = 2 * n + 1 from by ring] at h
    convert h using 2; ring_nf
  -- R2 chain: (2, 0, (1+n), 2n+2, n) →* (2+2n, 0, 1, 2n+2, 0) = (2n+2, 0, 1, 2n+2, 0)
  apply stepStar_trans (c₂ := ⟨2*n+2, 0, 1, 2*n+2, 0⟩)
  · have h := r2_chain n 2 1 (2*n+2)
    convert h using 2; ring_nf
  -- R3: (2n+2, 0, 1, 2n+2, 0) → (2n+1, 0, 1, 2n+3, 2)
  -- But wait: a = 2n+2 >= 1, b = 0. R1 needs b >= 1, fails. R2 needs c >= 1 and e >= 1,
  -- c = 1 but e = 0, fails. R3 needs a >= 1, fires.
  apply stepStar_trans (c₂ := ⟨2*n+1, 0, 1, 2*n+3, 2⟩)
  · rw [show 2 * n + 2 = (2 * n + 1) + 1 from by ring]
    step fm; ring_nf; finish
  -- R2: (2n+1, 0, 1, 2n+3, 2) → (2n+3, 0, 0, 2n+3, 1)
  -- a = 2n+1, b = 0, c = 1, e = 2. R1 needs b >= 1, fails.
  -- R2 needs c >= 1 (yes) and e >= 1 (yes). R2 fires.
  rw [show (1 : ℕ) = 0 + 1 from by ring,
      show (2 : ℕ) = 1 + 1 from by ring]
  step fm
  ring_nf; finish

-- Main transition: (n+1, 0, 0, n+1, 1) →⁺ (2n+3, 0, 0, 2n+3, 1)
theorem main_trans (n : ℕ) : ⟨n+1, 0, 0, n+1, 1⟩ [fm]⊢⁺ ⟨2*n+3, 0, 0, 2*n+3, 1⟩ := by
  -- Phase A: R3 chain (n+1 steps): (n+1, 0, 0, n+1, 1) →* (0, 0, 0, 2n+2, 2n+3)
  apply stepStar_stepPlus_stepPlus (c₂ := ⟨0, 0, 0, 2*n+2, 2*n+3⟩)
  · have h := r3_chain (n+1) 0 (n+1) 1
    convert h using 2; ring_nf
  -- Phase B: R4 chain (2n+2 steps): (0, 0, 0, 2n+2, 2n+3) →* (0, 2n+2, 0, 0, 2n+3)
  apply stepStar_stepPlus_stepPlus (c₂ := ⟨0, 2*n+2, 0, 0, 2*n+3⟩)
  · have h := r4_chain (2*n+2) 0 0 (2*n+3)
    convert h using 2; ring_nf
  -- Middle phase: (0, 2n+2, 0, 0, 2n+3) →* (2n+3, 0, 0, 2n+3, 1)
  apply stepStar_stepPlus (middle_phase n)
  intro h
  have : (0 : ℕ) = 2 * n + 3 := by
    have := congr_arg (fun q : Q => q.1) h; simp at this
  omega

theorem nonhalt : ¬halts fm c₀ := by
  -- Bootstrap: c₀ reaches (2, 0, 0, 2, 1) in 7 steps
  apply stepStar_not_halts_not_halts (c₂ := ⟨2, 0, 0, 2, 1⟩) (by execute fm 7)
  -- (2, 0, 0, 2, 1) = C(1) where C(n) = (n+1, 0, 0, n+1, 1)
  apply progress_nonhalt_simple (fm := fm) (A := ℕ) (fun n ↦ ⟨n+1, 0, 0, n+1, 1⟩) 1
  intro n; exact ⟨2*n+2, main_trans n⟩
