import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #24: [1/15, 18/77, 7/3, 25/49, 363/2]

Vector representation:
```
 0 -1 -1  0  0
 1  2  0 -1 -1
 0 -1  0  1  0
 0  0  2 -2  0
-1  1  0  0  2
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_24

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a, b+1, c+1, d, e⟩ => some ⟨a, b, c, d, e⟩
  | ⟨a, b, c, d+1, e+1⟩ => some ⟨a+1, b+2, c, d, e⟩
  | ⟨a, b+1, c, d, e⟩ => some ⟨a, b, c, d+1, e⟩
  | ⟨a, b, c, d+2, e⟩ => some ⟨a, b, c+2, d, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b+1, c, d, e+2⟩
  | _ => none

-- R2/R3 interleaved chain: (a, b, 0, 1, n+1) ⊢* (a+n+1, b+n+2, 0, 0, 0)
theorem r2r3_chain : ∀ n, ∀ a b, ⟨a, b, 0, 1, n+1⟩ [fm]⊢* ⟨a+n+1, b+n+2, 0, 0, 0⟩ := by
  intro n; induction n with
  | zero => intro a b; step fm; ring_nf; finish
  | succ n ih =>
    intro a b
    step fm; step fm
    apply stepStar_trans (ih _ _)
    ring_nf; finish

-- R3 drain (e=0): transfer b to d
theorem r3_drain : ∀ k, ∀ a d, ⟨a, k, 0, d, 0⟩ [fm]⊢* ⟨a, 0, 0, d+k, 0⟩ := by
  intro k; induction k with
  | zero => intro a d; ring_nf; finish
  | succ k ih =>
    intro a d
    step fm
    apply stepStar_trans (ih _ _)
    ring_nf; finish

-- R4 chain: transfer d to c (pairs), b=0, e=0
theorem r4_chain : ∀ k, ∀ a c, ⟨a, 0, c, 2*k, 0⟩ [fm]⊢* ⟨a, 0, c+2*k, 0, 0⟩ := by
  intro k; induction k with
  | zero => intro a c; ring_nf; finish
  | succ k ih =>
    intro a c
    rw [show 2 * (k + 1) = 2 * k + 2 from by ring]
    step fm
    apply stepStar_trans (ih _ _)
    ring_nf; finish

-- R4 chain variant with remainder 1
theorem r4_chain_rem1 : ∀ k, ∀ a c, ⟨a, 0, c, 2*k+1, 0⟩ [fm]⊢* ⟨a, 0, c+2*k, 1, 0⟩ := by
  intro k; induction k with
  | zero => intro a c; ring_nf; finish
  | succ k ih =>
    intro a c
    rw [show 2 * (k + 1) + 1 = (2 * k + 1) + 2 from by ring]
    step fm
    apply stepStar_trans (ih _ _)
    ring_nf; finish

-- R5/R1 drain: (a+k, 0, k, 0, e) ⊢* (a, 0, 0, 0, e+2*k)
theorem r5r1_drain : ∀ k, ∀ a e, ⟨a+k, 0, k, 0, e⟩ [fm]⊢* ⟨a, 0, 0, 0, e+2*k⟩ := by
  intro k; induction k with
  | zero => intro a e; ring_nf; finish
  | succ k ih =>
    intro a e
    rw [show a + (k + 1) = (a + k) + 1 from by ring]
    step fm; step fm
    apply stepStar_trans (ih _ _)
    ring_nf; finish

-- Transition 1: (1, 0, 0, 0, 2k+2) ⊢⁺ (3, 0, 0, 0, 4k+3)
theorem trans1 : ⟨1, 0, 0, 0, 2*k+2⟩ [fm]⊢⁺ ⟨3, 0, 0, 0, 4*k+3⟩ := by
  -- R5, R3
  step fm; step fm
  -- R2/R3 chain: (0,0,0,1,2k+4) ⊢* (2k+4, 2k+5, 0, 0, 0)
  rw [show 2 * k + 4 = (2 * k + 3) + 1 from by ring]
  apply stepStar_trans (r2r3_chain (2*k+3) 0 0)
  rw [show 0 + (2 * k + 3) + 1 = 2 * k + 4 from by ring,
      show 0 + (2 * k + 3) + 2 = 2 * k + 5 from by ring]
  -- R3 drain: (2k+4, 2k+5, 0, 0, 0) ⊢* (2k+4, 0, 0, 2k+5, 0)
  apply stepStar_trans (r3_drain (2*k+5) (2*k+4) 0)
  rw [show 0 + (2 * k + 5) = 2 * k + 5 from by ring]
  -- R4 chain with remainder 1: d=2k+5=2*(k+2)+1
  rw [show 2 * k + 5 = 2 * (k + 2) + 1 from by ring]
  apply stepStar_trans (r4_chain_rem1 (k+2) (2*k+4) 0)
  rw [show 0 + 2 * (k + 2) = 2 * k + 4 from by ring]
  -- 5 fixed steps: R5, R1, R2, R1, R1
  step fm; step fm; step fm; step fm; step fm
  -- R5/R1 drain: (2k+4, 0, 2k+1, 0, 1) ⊢* (3, 0, 0, 0, 1+2*(2k+1))
  rw [show 2 * k + 4 = 3 + (2 * k + 1) from by ring]
  apply stepStar_trans (r5r1_drain (2*k+1) 3 1)
  ring_nf; finish

-- Transition 2: (3, 0, 0, 0, 2m+1) ⊢⁺ (1, 0, 0, 0, 4m+8)
theorem trans2 : ⟨3, 0, 0, 0, 2*m+1⟩ [fm]⊢⁺ ⟨1, 0, 0, 0, 4*m+8⟩ := by
  -- R5, R3
  step fm; step fm
  -- R2/R3 chain: (2,0,0,1,2m+3) ⊢* (2m+5, 2m+4, 0, 0, 0)
  rw [show 2 * m + 3 = (2 * m + 2) + 1 from by ring]
  apply stepStar_trans (r2r3_chain (2*m+2) 2 0)
  rw [show 2 + (2 * m + 2) + 1 = 2 * m + 5 from by ring,
      show 0 + (2 * m + 2) + 2 = 2 * m + 4 from by ring]
  -- R3 drain: (2m+5, 2m+4, 0, 0, 0) ⊢* (2m+5, 0, 0, 2m+4, 0)
  apply stepStar_trans (r3_drain (2*m+4) (2*m+5) 0)
  rw [show 0 + (2 * m + 4) = 2 * m + 4 from by ring]
  -- R4 chain: d=2m+4=2*(m+2), so m+2 R4 steps
  rw [show 2 * m + 4 = 2 * (m + 2) from by ring]
  apply stepStar_trans (r4_chain (m+2) (2*m+5) 0)
  rw [show 0 + 2 * (m + 2) = 2 * m + 4 from by ring]
  -- R5/R1 drain: (2m+5, 0, 2m+4, 0, 0) ⊢* (1, 0, 0, 0, 2*(2m+4))
  rw [show 2 * m + 5 = 1 + (2 * m + 4) from by ring]
  apply stepStar_trans (r5r1_drain (2*m+4) 1 0)
  ring_nf; finish

-- Composed transition: (1, 0, 0, 0, 2k+2) ⊢⁺ (1, 0, 0, 0, 8k+12)
theorem main_trans : ⟨1, 0, 0, 0, 2*k+2⟩ [fm]⊢⁺ ⟨1, 0, 0, 0, 8*k+12⟩ := by
  apply stepPlus_stepStar_stepPlus trans1
  rw [show 4 * k + 3 = 2 * (2 * k + 1) + 1 from by ring]
  have h := @trans2 (2*k+1)
  rw [show 4 * (2 * k + 1) + 8 = 8 * k + 12 from by ring] at h
  exact stepPlus_stepStar h

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨1, 0, 0, 0, 4⟩)
  · execute fm 22
  apply progress_nonhalt_simple (fm := fm) (A := ℕ)
    (fun k ↦ ⟨1, 0, 0, 0, 2*k+2⟩) 1
  intro k
  exists (4*k+5)
  have h := @main_trans k
  rw [show 2 * (4 * k + 5) + 2 = 8 * k + 12 from by ring]
  exact h

end Sz22_2003_unofficial_24
