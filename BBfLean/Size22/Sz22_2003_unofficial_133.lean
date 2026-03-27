import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #133: [1/45, 154/5, 5/91, 1/7, 39/11, 5/2]

Vector representation:
```
 0 -2 -1  0  0  0
 1  0 -1  1  1  0
 0  0  1 -1  0 -1
 0  0  0 -1  0  0
 0  1  0  0 -1  1
-1  0  1  0  0  0
```

This Fractran program doesn't halt. Starting from (1,0,0,0,0,0), computation
reaches the canonical form (a, 0, 0, 0, 0, 4k) with a >= 1 and then loops
via (a, 0, 0, 0, 0, 4k) ⊢⁺ (a + 8k + 1, 0, 0, 0, 0, 4(k+1)).

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_133

def Q := ℕ × ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a, b+2, c+1, d, e, f⟩ => some ⟨a, b, c, d, e, f⟩
  | ⟨a, b, c+1, d, e, f⟩ => some ⟨a+1, b, c, d+1, e+1, f⟩
  | ⟨a, b, c, d+1, e, f+1⟩ => some ⟨a, b, c+1, d, e, f⟩
  | ⟨a, b, c, d+1, e, f⟩ => some ⟨a, b, c, d, e, f⟩
  | ⟨a, b, c, d, e+1, f⟩ => some ⟨a, b+1, c, d, e, f+1⟩
  | ⟨a+1, b, c, d, e, f⟩ => some ⟨a, b, c+1, d, e, f⟩
  | _ => none

-- R3+R2 chain with b=0: (a, 0, 0, 1, e, f+k) →* (a+k, 0, 0, 1, e+k, f)
-- Each R3+R2 pair: d stays 1, a and e increase by 1, f decreases by 1
theorem r3r2_b0 : ∀ k a e f, ⟨a, 0, 0, 1, e, f+k⟩ [fm]⊢* ⟨a+k, (0 : ℕ), 0, 1, e+k, f⟩ := by
  intro k; induction k with
  | zero => intro a e f; exists 0
  | succ k ih =>
    intro a e f
    rw [show f + (k + 1) = (f + k) + 1 from by ring]
    -- R3: d=0+1, f=(f+k)+1 pattern -> c+1, d-1, f-1
    rw [show (1 : ℕ) = 0 + 1 from by ring]
    step fm
    -- now (a, 0, 0+1, 0, e, f+k) -> R2 fires (b=0 < 2)
    step fm
    -- now (a+1, 0, 0, 0+1, e+1, f+k) = (a+1, 0, 0, 1, e+1, f+k)
    apply stepStar_trans (ih (a + 1) (e + 1) f)
    ring_nf; finish

-- R3+R2 chain with b=1: (a, 1, 0, 1, e, f+k) →* (a+k, 1, 0, 1, e+k, f)
theorem r3r2_b1 : ∀ k a e f, ⟨a, 1, 0, 1, e, f+k⟩ [fm]⊢* ⟨a+k, (1 : ℕ), 0, 1, e+k, f⟩ := by
  intro k; induction k with
  | zero => intro a e f; exists 0
  | succ k ih =>
    intro a e f
    rw [show f + (k + 1) = (f + k) + 1 from by ring,
        show (1 : ℕ) = 0 + 1 from by ring]
    step fm
    -- now (a, 1, 0+1, 0, e, f+k): b=1 < 2, so R1 doesn't fire, R2 does
    step fm
    apply stepStar_trans (ih (a + 1) (e + 1) f)
    ring_nf; finish

-- Phase 1 with b=0: R6 + R2 + (R3+R2)^f + R4
-- (a+1, 0, 0, 0, 0, f+1) ⊢⁺ (a+f+2, 0, 0, 0, f+2, 0)
theorem phase1_b0 (a f : ℕ) : ⟨a+1, 0, 0, 0, 0, f+1⟩ [fm]⊢⁺ ⟨a+2+f, (0 : ℕ), 0, 0, f+2, 0⟩ := by
  apply step_stepStar_stepPlus (c₂ := ⟨a, 0, 1, 0, 0, f + 1⟩)
  · simp [fm]  -- R6
  apply stepStar_trans (c₂ := ⟨a + 1, 0, 0, 1, 1, f + 1⟩)
  · step fm; finish -- R2
  apply stepStar_trans (c₂ := ⟨a + f + 2, 0, 0, 1, f + 2, 0⟩)
  · have h := r3r2_b0 (f + 1) (a + 1) 1 0
    simp only [Nat.zero_add] at h
    rw [show a + 1 + (f + 1) = a + f + 2 from by ring,
        show 1 + (f + 1) = f + 2 from by ring] at h
    exact h
  rw [show (1 : ℕ) = 0 + 1 from by ring]
  step fm
  rw [show a + 2 + f = a + f + 2 from by ring]
  finish

-- Phase 1 with b=1: R6 + R2 + (R3+R2)^f + R4
-- (a+1, 1, 0, 0, 0, f+1) ⊢⁺ (a+f+2, 1, 0, 0, f+2, 0)
theorem phase1_b1 (a f : ℕ) : ⟨a+1, 1, 0, 0, 0, f+1⟩ [fm]⊢⁺ ⟨a+2+f, (1 : ℕ), 0, 0, f+2, 0⟩ := by
  apply step_stepStar_stepPlus (c₂ := ⟨a, 1, 1, 0, 0, f + 1⟩)
  · simp [fm]  -- R6
  apply stepStar_trans (c₂ := ⟨a + 1, 1, 0, 1, 1, f + 1⟩)
  · step fm; finish -- R2 (b=1 < 2, so R1 doesn't fire)
  apply stepStar_trans (c₂ := ⟨a + f + 2, 1, 0, 1, f + 2, 0⟩)
  · have h := r3r2_b1 (f + 1) (a + 1) 1 0
    simp only [Nat.zero_add] at h
    rw [show a + 1 + (f + 1) = a + f + 2 from by ring,
        show 1 + (f + 1) = f + 2 from by ring] at h
    exact h
  rw [show (1 : ℕ) = 0 + 1 from by ring]
  step fm
  rw [show a + 2 + f = a + f + 2 from by ring]
  finish

-- R5 chain: (a, b, 0, 0, e+k, f) →* (a, b+k, 0, 0, e, f+k)
theorem r5_chain : ∀ k a b e f, ⟨a, b, 0, 0, e+k, f⟩ [fm]⊢* ⟨a, b+k, (0 : ℕ), 0, e, f+k⟩ := by
  intro k; induction k with
  | zero => intro a b e f; exists 0
  | succ k ih =>
    intro a b e f
    rw [show e + (k + 1) = (e + k) + 1 from by ring]
    step fm
    apply stepStar_trans (ih a (b + 1) e (f + 1))
    ring_nf; finish

-- R6+R1 drain: (a+k, b+2*k, 0, 0, 0, f) →* (a, b, 0, 0, 0, f)
theorem r61_drain : ∀ k a b f, ⟨a+k, b+2*k, 0, 0, 0, f⟩ [fm]⊢* ⟨a, b, (0 : ℕ), 0, 0, f⟩ := by
  intro k; induction k with
  | zero => intro a b f; exists 0
  | succ k ih =>
    intro a b f
    rw [show a + (k + 1) = (a + k) + 1 from by ring,
        show b + 2 * (k + 1) = (b + 2 * k) + 1 + 1 from by ring]
    -- R6: match (a+k)+1
    step fm
    -- now (a+k, (b+2*k)+1+1, 0+1, 0, 0, f): b+2*k+2 >= 2, c=1, so R1 fires
    rw [show b + 2 * k + 1 = (b + 2 * k) + 1 from by ring]
    step fm
    apply stepStar_trans (ih a b f)
    ring_nf; finish

-- Sub-cycle: b=0, f even (f=2(m+1)): (a+1, 0, 0, 0, 0, 2(m+1)) ⊢⁺ (a+m+2, 1, 0, 0, 0, 2m+3)
theorem sub_even_b0 (a m : ℕ) :
    ⟨a+1, 0, 0, 0, 0, 2*(m+1)⟩ [fm]⊢⁺ ⟨a+m+2, (1 : ℕ), 0, 0, 0, 2*m+3⟩ := by
  apply stepPlus_stepStar_stepPlus (c₂ := ⟨a + 2 * m + 3, 2 * m + 3, 0, 0, 0, 2 * m + 3⟩)
  · apply stepPlus_stepStar_stepPlus (c₂ := ⟨a + 2 * m + 3, 0, 0, 0, 2 * m + 3, 0⟩)
    · have h := phase1_b0 a (2 * m + 1)
      rw [show (2 * m + 1) + 1 = 2 * (m + 1) from by ring,
          show a + 2 + (2 * m + 1) = a + 2 * m + 3 from by ring,
          show (2 * m + 1) + 2 = 2 * m + 3 from by ring] at h
      exact h
    · have h := r5_chain (2 * m + 3) (a + 2 * m + 3) 0 0 0
      simp only [Nat.zero_add] at h; exact h
  · have h := r61_drain (m + 1) (a + m + 2) 1 (2 * m + 3)
    rw [show a + m + 2 + (m + 1) = a + 2 * m + 3 from by ring,
        show 1 + 2 * (m + 1) = 2 * m + 3 from by ring] at h
    exact h

-- Sub-cycle: b=1, f odd (f=2m+1): (a+1, 1, 0, 0, 0, 2m+1) ⊢⁺ (a+m+1, 1, 0, 0, 0, 2m+2)
theorem sub_odd_b1 (a m : ℕ) :
    ⟨a+1, 1, 0, 0, 0, 2*m+1⟩ [fm]⊢⁺ ⟨a+m+1, (1 : ℕ), 0, 0, 0, 2*m+2⟩ := by
  apply stepPlus_stepStar_stepPlus (c₂ := ⟨a + 2 * m + 2, 2 * m + 3, 0, 0, 0, 2 * m + 2⟩)
  · apply stepPlus_stepStar_stepPlus (c₂ := ⟨a + 2 * m + 2, 1, 0, 0, 2 * m + 2, 0⟩)
    · have h := phase1_b1 a (2 * m)
      rw [show (2 * m) + 1 = 2 * m + 1 from by ring,
          show a + 2 + 2 * m = a + 2 * m + 2 from by ring,
          show 2 * m + 2 = 2 * m + 2 from by ring] at h
      exact h
    · have h := r5_chain (2 * m + 2) (a + 2 * m + 2) 1 0 0
      simp only [Nat.zero_add] at h
      rw [show 1 + (2 * m + 2) = 2 * m + 3 from by ring] at h
      exact h
  · have h := r61_drain (m + 1) (a + m + 1) 1 (2 * m + 2)
    rw [show a + m + 1 + (m + 1) = a + 2 * m + 2 from by ring,
        show 1 + 2 * (m + 1) = 2 * m + 3 from by ring] at h
    exact h

-- Sub-cycle: b=1, f even (f=2(m+1)): (a+1, 1, 0, 0, 0, 2(m+1)) ⊢⁺ (a+m+1, 0, 0, 0, 0, 2m+3)
theorem sub_even_b1 (a m : ℕ) :
    ⟨a+1, 1, 0, 0, 0, 2*(m+1)⟩ [fm]⊢⁺ ⟨a+m+1, (0 : ℕ), 0, 0, 0, 2*m+3⟩ := by
  apply stepPlus_stepStar_stepPlus (c₂ := ⟨a + 2 * m + 3, 2 * m + 4, 0, 0, 0, 2 * m + 3⟩)
  · apply stepPlus_stepStar_stepPlus (c₂ := ⟨a + 2 * m + 3, 1, 0, 0, 2 * m + 3, 0⟩)
    · have h := phase1_b1 a (2 * m + 1)
      rw [show (2 * m + 1) + 1 = 2 * (m + 1) from by ring,
          show a + 2 + (2 * m + 1) = a + 2 * m + 3 from by ring,
          show (2 * m + 1) + 2 = 2 * m + 3 from by ring] at h
      exact h
    · have h := r5_chain (2 * m + 3) (a + 2 * m + 3) 1 0 0
      simp only [Nat.zero_add] at h
      rw [show 1 + (2 * m + 3) = 2 * m + 4 from by ring] at h
      exact h
  · have h := r61_drain (m + 2) (a + m + 1) 0 (2 * m + 3)
    rw [show a + m + 1 + (m + 2) = a + 2 * m + 3 from by ring,
        show 0 + 2 * (m + 2) = 2 * m + 4 from by ring] at h
    exact h

-- Sub-cycle: b=0, f odd (f=2m+1): (a+1, 0, 0, 0, 0, 2m+1) ⊢⁺ (a+m+1, 0, 0, 0, 0, 2m+2)
theorem sub_odd_b0 (a m : ℕ) :
    ⟨a+1, 0, 0, 0, 0, 2*m+1⟩ [fm]⊢⁺ ⟨a+m+1, (0 : ℕ), 0, 0, 0, 2*m+2⟩ := by
  apply stepPlus_stepStar_stepPlus (c₂ := ⟨a + 2 * m + 2, 2 * m + 2, 0, 0, 0, 2 * m + 2⟩)
  · apply stepPlus_stepStar_stepPlus (c₂ := ⟨a + 2 * m + 2, 0, 0, 0, 2 * m + 2, 0⟩)
    · have h := phase1_b0 a (2 * m)
      rw [show (2 * m) + 1 = 2 * m + 1 from by ring,
          show a + 2 + 2 * m = a + 2 * m + 2 from by ring,
          show 2 * m + 2 = 2 * m + 2 from by ring] at h
      exact h
    · have h := r5_chain (2 * m + 2) (a + 2 * m + 2) 0 0 0
      simp only [Nat.zero_add] at h; exact h
  · have h := r61_drain (m + 1) (a + m + 1) 0 (2 * m + 2)
    rw [show a + m + 1 + (m + 1) = a + 2 * m + 2 from by ring,
        show 0 + 2 * (m + 1) = 2 * m + 2 from by ring] at h
    exact h

-- Main transition: (a+1, 0, 0, 0, 0, 4(k+1)) ⊢⁺ (a+8k+10, 0, 0, 0, 0, 4(k+2))
theorem main_trans (a k : ℕ) :
    ⟨a+1, 0, 0, 0, 0, 4*(k+1)⟩ [fm]⊢⁺ ⟨a+8*k+10, (0 : ℕ), 0, 0, 0, 4*(k+2)⟩ := by
  -- Sub-cycle 1: b=0, f=4(k+1)=2*(2k+2), even, m=2k+1
  apply stepPlus_trans (c₂ := ⟨a + 2 * k + 3, 1, 0, 0, 0, 4 * k + 5⟩)
  · have h := sub_even_b0 a (2 * k + 1)
    rw [show 2 * ((2 * k + 1) + 1) = 4 * (k + 1) from by ring,
        show a + (2 * k + 1) + 2 = a + 2 * k + 3 from by ring,
        show 2 * (2 * k + 1) + 3 = 4 * k + 5 from by ring] at h
    exact h
  -- Sub-cycle 2: b=1, f=4k+5=2*(2k+2)+1, odd, m=2k+2
  apply stepPlus_trans (c₂ := ⟨a + 4 * k + 5, 1, 0, 0, 0, 4 * k + 6⟩)
  · have h := sub_odd_b1 (a + 2 * k + 2) (2 * k + 2)
    rw [show a + 2 * k + 2 + 1 = a + 2 * k + 3 from by ring,
        show 2 * (2 * k + 2) + 1 = 4 * k + 5 from by ring,
        show a + 2 * k + 2 + (2 * k + 2) + 1 = a + 4 * k + 5 from by ring,
        show 2 * (2 * k + 2) + 2 = 4 * k + 6 from by ring] at h
    exact h
  -- Sub-cycle 3: b=1, f=4k+6=2*(2k+3), even, m=2k+2
  apply stepPlus_trans (c₂ := ⟨a + 6 * k + 7, 0, 0, 0, 0, 4 * k + 7⟩)
  · have h := sub_even_b1 (a + 4 * k + 4) (2 * k + 2)
    rw [show a + 4 * k + 4 + 1 = a + 4 * k + 5 from by ring,
        show 2 * ((2 * k + 2) + 1) = 4 * k + 6 from by ring,
        show a + 4 * k + 4 + (2 * k + 2) + 1 = a + 6 * k + 7 from by ring,
        show 2 * (2 * k + 2) + 3 = 4 * k + 7 from by ring] at h
    exact h
  -- Sub-cycle 4: b=0, f=4k+7=2*(2k+3)+1, odd, m=2k+3
  have h := sub_odd_b0 (a + 6 * k + 6) (2 * k + 3)
  rw [show a + 6 * k + 6 + 1 = a + 6 * k + 7 from by ring,
      show 2 * (2 * k + 3) + 1 = 4 * k + 7 from by ring,
      show a + 6 * k + 6 + (2 * k + 3) + 1 = a + 8 * k + 10 from by ring,
      show 2 * (2 * k + 3) + 2 = 4 * (k + 2) from by ring] at h
  exact h

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨2, 0, 0, 0, 0, 4⟩) (by execute fm 44)
  apply progress_nonhalt_simple (fm := fm) (A := ℕ × ℕ)
    (fun ⟨a, k⟩ ↦ ⟨a + 1, 0, 0, 0, 0, 4 * (k + 1)⟩) ⟨1, 0⟩
  intro ⟨a, k⟩
  refine ⟨⟨a + 8 * k + 9, k + 1⟩, ?_⟩
  show ⟨a + 1, 0, 0, 0, 0, 4 * (k + 1)⟩ [fm]⊢⁺ ⟨a + 8 * k + 9 + 1, (0 : ℕ), 0, 0, 0, 4 * (k + 1 + 1)⟩
  rw [show a + 8 * k + 9 + 1 = a + 8 * k + 10 from by ring,
      show k + 1 + 1 = k + 2 from by ring]
  exact main_trans a k

end Sz22_2003_unofficial_133
