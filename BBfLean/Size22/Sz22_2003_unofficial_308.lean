import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #308: [154/15, 1/26, 21/2, 65/7, 4/143]

Vector representation:
```
 1 -1 -1  1  1  0
-1  0  0  0  0 -1
-1  1  0  1  0  0
 0  0  1 -1  0  1
 2  0  0  0 -1 -1
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_308

def Q := ℕ × ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a, b+1, c+1, d, e, f⟩ => some ⟨a+1, b, c, d+1, e+1, f⟩
  | ⟨a+1, b, c, d, e, f+1⟩ => some ⟨a, b, c, d, e, f⟩
  | ⟨a+1, b, c, d, e, f⟩ => some ⟨a, b+1, c, d+1, e, f⟩
  | ⟨a, b, c, d+1, e, f⟩ => some ⟨a, b, c+1, d, e, f+1⟩
  | ⟨a, b, c, d, e+1, f+1⟩ => some ⟨a+2, b, c, d, e, f⟩
  | _ => none

-- R4 repeated: convert d to c and f
theorem d_to_cf : ∀ k c e f, ⟨0, 0, c, k, e, f⟩ [fm]⊢* ⟨0, 0, c+k, 0, e, f+k⟩ := by
  intro k; induction' k with k ih <;> intro c e f
  · exists 0
  step fm
  have h := ih (c + 1) e (f + 1)
  rw [show c + 1 + k = c + (k + 1) from by ring,
      show f + 1 + k = f + (k + 1) from by ring] at h
  exact h

-- Drain: consume e and f in groups of (R5, R2, R2), ending with one R5
theorem drain : ∀ k c e, ⟨0, 0, c, 0, e+k+1, 3*k+1⟩ [fm]⊢* ⟨2, 0, c, 0, e, 0⟩ := by
  intro k; induction' k with k ih <;> intro c e
  · step fm; finish
  step fm  -- R5
  step fm  -- R2
  step fm  -- R2
  exact ih c e

-- Bounce: R3, R1 pairs consuming c and building d
theorem bounce : ∀ k d e, ⟨2, 0, k, d, e, 0⟩ [fm]⊢* ⟨2, 0, 0, d+2*k, e+k, 0⟩ := by
  intro k; induction' k with k ih <;> intro d e
  · exists 0
  step fm  -- R3
  step fm  -- R1
  have h := ih (d + 2) (e + 1)
  rw [show d + 2 + 2 * k = d + 2 * (k + 1) from by ring,
      show e + 1 + k = e + (k + 1) from by ring] at h
  exact h

-- Phase 1: 8 explicit steps
theorem phase1 : ∀ d e, ⟨2, 0, 0, d, e, 0⟩ [fm]⊢⁺ ⟨0, 0, 0, d+2, e+2, 0⟩ := by
  intro d e
  step fm; step fm; step fm; step fm
  step fm; step fm; step fm; step fm
  finish

-- Main transition: parametrized so all arithmetic is clean
theorem main_trans (m s : ℕ) :
    ⟨2, 0, 0, 3*m+2, s+m+1, 0⟩ [fm]⊢⁺ ⟨2, 0, 0, 6*m+8, s+3*m+5, 0⟩ := by
  apply stepPlus_stepStar_stepPlus
  · exact phase1 (3*m+2) (s+m+1)
  -- After phase1: (0, 0, 0, 3m+4, s+m+3, 0)
  -- d_to_cf: k=3m+4, c=0, e=s+m+3, f=0
  apply stepStar_trans (c₂ := ⟨0, 0, 3*m+4, 0, s+m+3, 3*m+4⟩)
  · have h := d_to_cf (3*m+4) 0 (s+m+3) 0
    simp only [Nat.zero_add] at h; exact h
  -- drain: k=m+1, c=3m+4, e=s+1
  -- drain(m+1, 3m+4, s+1): (0,0,3m+4,0,(s+1)+(m+1)+1,3*(m+1)+1) ⊢* (2,0,3m+4,0,s+1,0)
  -- (s+1)+(m+1)+1 = s+m+3 ✓, 3*(m+1)+1 = 3m+4 ✓
  apply stepStar_trans (c₂ := ⟨2, 0, 3*m+4, 0, s+1, 0⟩)
  · have h := drain (m+1) (3*m+4) (s+1)
    convert h using 3; ring_nf
  -- bounce: k=3m+4, d=0, e=s+1
  have h := bounce (3*m+4) 0 (s+1)
  convert h using 3; ring_nf

-- Define the sequence of m-values
def mseq : ℕ → ℕ
  | 0 => 0
  | n+1 => 2 * mseq n + 2

def eseq : ℕ → ℕ
  | 0 => 1
  | n+1 => eseq n + 2 * mseq n + 4

theorem eseq_gt_mseq : ∀ n, eseq n ≥ mseq n + 1 := by
  intro n; induction' n with n ih
  · simp [eseq, mseq]
  · simp only [eseq, mseq]; omega

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨2, 0, 0, 2, 1, 0⟩) (by execute fm 8)
  apply progress_nonhalt_simple (fm := fm) (A := ℕ)
    (fun n ↦ ⟨2, 0, 0, 3 * mseq n + 2, eseq n, 0⟩) 0
  intro n
  exists n + 1
  show ⟨2, 0, 0, 3 * mseq n + 2, eseq n, 0⟩ [fm]⊢⁺
    ⟨2, 0, 0, 3 * mseq (n + 1) + 2, eseq (n + 1), 0⟩
  simp only [mseq, eseq]
  have hge := eseq_gt_mseq n
  set s := eseq n - mseq n - 1
  have hs : eseq n = s + mseq n + 1 := by omega
  rw [hs]
  convert main_trans (mseq n) s using 2; ring_nf

end Sz22_2003_unofficial_308
