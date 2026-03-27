import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #136: [1/45, 196/15, 3/7, 25/2, 49/5]

Vector representation:
```
 0 -2 -1  0
 2 -1 -1  2
 0  1  0 -1
-1  0  2  0
 0  0 -1  2
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_136

def Q := ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a, b+2, c+1, d⟩ => some ⟨a, b, c, d⟩
  | ⟨a, b+1, c+1, d⟩ => some ⟨a+2, b, c, d+2⟩
  | ⟨a, b, c, d+1⟩ => some ⟨a, b+1, c, d⟩
  | ⟨a+1, b, c, d⟩ => some ⟨a, b, c+2, d⟩
  | ⟨a, b, c+1, d⟩ => some ⟨a, b, c, d+2⟩
  | _ => none

-- R3/R2 spiral chain: (a, 0, c+k, d+2) →* (a+2k, 0, c, d+k+2)
theorem spiral_chain : ∀ k a c d,
    (⟨a, 0, c+k, d+2⟩ : Q) [fm]⊢* ⟨a+2*k, 0, c, d+k+2⟩ := by
  intro k; induction k with
  | zero => intro a c d; simp; exists 0
  | succ k ih =>
    intro a c d
    rw [show c + (k + 1) = (c + k) + 1 from by ring,
        show d + 2 = (d + 1) + 1 from by ring]
    step fm; step fm
    rw [show d + 1 + 2 = (d + 1) + 2 from by ring]
    apply stepStar_trans (ih (a + 2) c (d + 1))
    rw [show a + 2 + 2 * k = a + 2 * (k + 1) from by ring,
        show d + 1 + k + 2 = d + (k + 1) + 2 from by ring]
    finish

-- R3 chain: d → b transfer
theorem d_to_b : ∀ k a b,
    (⟨a, b, 0, k⟩ : Q) [fm]⊢* ⟨a, b+k, 0, 0⟩ := by
  intro k; induction k with
  | zero => intro a b; exists 0
  | succ k ih =>
    intro a b; step fm
    apply stepStar_trans (ih a (b + 1))
    rw [show b + 1 + k = b + (k + 1) from by ring]; finish

-- R4/R1/R1 drain: (a+k, b+4k, 0, 0) →* (a, b, 0, 0)
theorem drain : ∀ k a b,
    (⟨a+k, b+4*k, 0, 0⟩ : Q) [fm]⊢* ⟨a, b, 0, 0⟩ := by
  intro k; induction k with
  | zero => intro a b; simp; exists 0
  | succ k ih =>
    intro a b
    rw [show a + (k + 1) = (a + k) + 1 from by ring,
        show b + 4 * (k + 1) = (b + 4 * k + 2) + 1 + 1 from by ring]
    step fm; step fm; step fm
    exact ih a b

-- R4 chain: (k, 0, c, 0) →* (0, 0, c+2k, 0)
theorem a_to_c : ∀ k c,
    (⟨k, 0, c, 0⟩ : Q) [fm]⊢* ⟨0, 0, c+2*k, 0⟩ := by
  intro k; induction k with
  | zero => intro c; simp; exists 0
  | succ k ih =>
    intro c; step fm
    apply stepStar_trans (ih (c + 2))
    rw [show c + 2 + 2 * k = c + 2 * (k + 1) from by ring]; finish

-- Terminal b=1: (a+1, 1, 0, 0) →* (a+4, 0, 1, 0)
theorem terminal_b1 : ∀ a,
    (⟨a+1, 1, 0, 0⟩ : Q) [fm]⊢* ⟨a+4, 0, 1, 0⟩ := by
  intro a
  step fm; step fm; step fm; step fm; step fm; step fm; step fm
  step fm; step fm; step fm; step fm; step fm; step fm; step fm
  finish

-- Terminal b=2: (a+1, 2, 0, 0) →* (a, 0, 1, 0)
theorem terminal_b2 : ∀ a,
    (⟨a+1, 2, 0, 0⟩ : Q) [fm]⊢* ⟨a, 0, 1, 0⟩ := by
  intro a; step fm; step fm; finish

-- Terminal b=3: (a+1, 3, 0, 0) →* (a+1, 0, 1, 0)
theorem terminal_b3 : ∀ a,
    (⟨a+1, 3, 0, 0⟩ : Q) [fm]⊢* ⟨a+1, 0, 1, 0⟩ := by
  intro a; step fm; step fm; step fm; step fm; step fm; step fm; step fm; finish

-- Helper: spiral from R5 output to (A, B, 0, 0) form
-- (0, 0, C, 2) →* (2C, C+2, 0, 0)
theorem spiral_and_transfer (C : ℕ) :
    (⟨0, 0, C, 2⟩ : Q) [fm]⊢* ⟨2*C, C+2, 0, 0⟩ := by
  apply stepStar_trans (c₂ := ⟨2*C, 0, 0, C+2⟩)
  · have h := spiral_chain C 0 0 0
    simp only [Nat.zero_add] at h; exact h
  have h := d_to_b (C+2) (2*C) 0
  simp only [Nat.zero_add] at h; exact h

-- Case C%4=0: (0, 0, 4m+2, 0) ⊢⁺ (0, 0, 14m+5, 0)
theorem main_r0 (m : ℕ) :
    (⟨0, 0, 4*m+2, 0⟩ : Q) [fm]⊢⁺ ⟨0, 0, 14*m+5, 0⟩ := by
  rw [show 4 * m + 2 = (4 * m + 1) + 1 from by ring]
  apply step_stepStar_stepPlus (c₂ := ⟨0, 0, 4*m+1, 2⟩)
  · simp [fm]
  apply stepStar_trans (c₂ := ⟨8*m+2, 4*m+3, 0, 0⟩)
  · have h := spiral_and_transfer (4*m+1)
    rw [show 2 * (4 * m + 1) = 8 * m + 2 from by ring,
        show (4 * m + 1) + 2 = 4 * m + 3 from by ring] at h; exact h
  apply stepStar_trans (c₂ := ⟨7*m+2, 3, 0, 0⟩)
  · have h := drain m (7*m+2) 3
    rw [show 7 * m + 2 + m = 8 * m + 2 from by ring,
        show 3 + 4 * m = 4 * m + 3 from by ring] at h; exact h
  apply stepStar_trans (c₂ := ⟨7*m+2, 0, 1, 0⟩)
  · rw [show 7 * m + 2 = (7 * m + 1) + 1 from by ring]
    exact terminal_b3 (7*m+1)
  have h := a_to_c (7*m+2) 1
  rw [show 1 + 2 * (7 * m + 2) = 14 * m + 5 from by ring] at h; exact h

-- Case C%4=1: (0, 0, 4m+3, 0) ⊢⁺ (0, 0, 14m+6, 0)
theorem main_r1 (m : ℕ) :
    (⟨0, 0, 4*m+3, 0⟩ : Q) [fm]⊢⁺ ⟨0, 0, 14*m+6, 0⟩ := by
  rw [show 4 * m + 3 = (4 * m + 2) + 1 from by ring]
  apply step_stepStar_stepPlus (c₂ := ⟨0, 0, 4*m+2, 2⟩)
  · simp [fm]
  apply stepStar_trans (c₂ := ⟨8*m+4, 4*m+4, 0, 0⟩)
  · have h := spiral_and_transfer (4*m+2)
    rw [show 2 * (4 * m + 2) = 8 * m + 4 from by ring,
        show (4 * m + 2) + 2 = 4 * m + 4 from by ring] at h; exact h
  apply stepStar_trans (c₂ := ⟨7*m+3, 0, 0, 0⟩)
  · have h := drain (m+1) (7*m+3) 0
    rw [show 7 * m + 3 + (m + 1) = 8 * m + 4 from by ring,
        show 0 + 4 * (m + 1) = 4 * m + 4 from by ring] at h; exact h
  have h := a_to_c (7*m+3) 0
  rw [show 0 + 2 * (7 * m + 3) = 14 * m + 6 from by ring] at h; exact h

-- Case C%4=2: (0, 0, 4m+4, 0) ⊢⁺ (0, 0, 14m+17, 0)
theorem main_r2 (m : ℕ) :
    (⟨0, 0, 4*m+4, 0⟩ : Q) [fm]⊢⁺ ⟨0, 0, 14*m+17, 0⟩ := by
  rw [show 4 * m + 4 = (4 * m + 3) + 1 from by ring]
  apply step_stepStar_stepPlus (c₂ := ⟨0, 0, 4*m+3, 2⟩)
  · simp [fm]
  apply stepStar_trans (c₂ := ⟨8*m+6, 4*m+5, 0, 0⟩)
  · have h := spiral_and_transfer (4*m+3)
    rw [show 2 * (4 * m + 3) = 8 * m + 6 from by ring,
        show (4 * m + 3) + 2 = 4 * m + 5 from by ring] at h; exact h
  apply stepStar_trans (c₂ := ⟨7*m+5, 1, 0, 0⟩)
  · have h := drain (m+1) (7*m+5) 1
    rw [show 7 * m + 5 + (m + 1) = 8 * m + 6 from by ring,
        show 1 + 4 * (m + 1) = 4 * m + 5 from by ring] at h; exact h
  apply stepStar_trans (c₂ := ⟨7*m+8, 0, 1, 0⟩)
  · rw [show 7 * m + 5 = (7 * m + 4) + 1 from by ring]
    exact terminal_b1 (7*m+4)
  have h := a_to_c (7*m+8) 1
  rw [show 1 + 2 * (7 * m + 8) = 14 * m + 17 from by ring] at h; exact h

-- Case C%4=3: (0, 0, 4m+5, 0) ⊢⁺ (0, 0, 14m+13, 0)
theorem main_r3 (m : ℕ) :
    (⟨0, 0, 4*m+5, 0⟩ : Q) [fm]⊢⁺ ⟨0, 0, 14*m+13, 0⟩ := by
  rw [show 4 * m + 5 = (4 * m + 4) + 1 from by ring]
  apply step_stepStar_stepPlus (c₂ := ⟨0, 0, 4*m+4, 2⟩)
  · simp [fm]
  apply stepStar_trans (c₂ := ⟨8*m+8, 4*m+6, 0, 0⟩)
  · have h := spiral_and_transfer (4*m+4)
    rw [show 2 * (4 * m + 4) = 8 * m + 8 from by ring,
        show (4 * m + 4) + 2 = 4 * m + 6 from by ring] at h; exact h
  apply stepStar_trans (c₂ := ⟨7*m+7, 2, 0, 0⟩)
  · have h := drain (m+1) (7*m+7) 2
    rw [show 7 * m + 7 + (m + 1) = 8 * m + 8 from by ring,
        show 2 + 4 * (m + 1) = 4 * m + 6 from by ring] at h; exact h
  apply stepStar_trans (c₂ := ⟨7*m+6, 0, 1, 0⟩)
  · rw [show 7 * m + 7 = (7 * m + 6) + 1 from by ring]
    exact terminal_b2 (7*m+6)
  have h := a_to_c (7*m+6) 1
  rw [show 1 + 2 * (7 * m + 6) = 14 * m + 13 from by ring] at h; exact h

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨0, 0, 2, 0⟩) (by execute fm 1)
  apply progress_nonhalt_simple (fm := fm) (A := ℕ)
    (fun n ↦ ⟨0, 0, n+2, 0⟩) 0
  intro n
  rcases Nat.even_or_odd n with ⟨k₁, hk₁⟩ | ⟨k₁, hk₁⟩
  · rcases Nat.even_or_odd k₁ with ⟨m, hm⟩ | ⟨m, hm⟩
    · -- n = 4m
      subst hm; subst hk₁
      refine ⟨14*m+3, ?_⟩
      rw [show m + m + (m + m) + 2 = 4 * m + 2 from by omega,
          show 14 * m + 3 + 2 = 14 * m + 5 from by ring]
      exact main_r0 m
    · -- n = 4m+2
      subst hm; subst hk₁
      refine ⟨14*m+15, ?_⟩
      rw [show 2 * m + 1 + (2 * m + 1) + 2 = 4 * m + 4 from by omega,
          show 14 * m + 15 + 2 = 14 * m + 17 from by ring]
      exact main_r2 m
  · rcases Nat.even_or_odd k₁ with ⟨m, hm⟩ | ⟨m, hm⟩
    · -- n = 4m+1
      subst hm; subst hk₁
      refine ⟨14*m+4, ?_⟩
      rw [show 2 * (m + m) + 1 + 2 = 4 * m + 3 from by omega,
          show 14 * m + 4 + 2 = 14 * m + 6 from by ring]
      exact main_r1 m
    · -- n = 4m+3
      subst hm; subst hk₁
      refine ⟨14*m+11, ?_⟩
      rw [show 2 * (2 * m + 1) + 1 + 2 = 4 * m + 5 from by omega,
          show 14 * m + 11 + 2 = 14 * m + 13 from by ring]
      exact main_r3 m

end Sz22_2003_unofficial_136
