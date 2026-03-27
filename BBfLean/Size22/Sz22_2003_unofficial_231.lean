import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #231: [11/105, 15/22, 4/3, 49/2, 33/7]

Vector representation:
```
 0 -1 -1 -1  1
-1  1  1  0 -1
 2 -1  0  0  0
-1  0  0  2  0
 0  1  0 -1  1
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_231

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a, b+1, c+1, d+1, e⟩ => some ⟨a, b, c, d, e+1⟩
  | ⟨a+1, b, c, d, e+1⟩ => some ⟨a, b+1, c+1, d, e⟩
  | ⟨a, b+1, c, d, e⟩ => some ⟨a+2, b, c, d, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b, c, d+2, e⟩
  | ⟨a, b, c, d+1, e⟩ => some ⟨a, b+1, c, d, e+1⟩
  | _ => none

-- R3 chain: b → a (d=0, e=0)
theorem b_to_a : ∀ k a b c, ⟨a, b+k, c, 0, 0⟩ [fm]⊢* ⟨a+2*k, b, c, 0, 0⟩ := by
  intro k; induction k with
  | zero => intro a b c; exists 0
  | succ k ih =>
    intro a b c
    rw [show b + (k + 1) = (b + k) + 1 from by ring]
    step fm
    apply stepStar_trans (ih _ _ _)
    ring_nf; finish

-- R4 chain: a → d (b=0, e=0)
theorem a_to_d : ∀ k a c d, ⟨a+k, 0, c, d, 0⟩ [fm]⊢* ⟨a, 0, c, d+2*k, 0⟩ := by
  intro k; induction k with
  | zero => intro a c d; exists 0
  | succ k ih =>
    intro a c d
    rw [show a + (k + 1) = (a + k) + 1 from by ring]
    step fm
    apply stepStar_trans (ih _ _ _)
    ring_nf; finish

-- R5+R1 drain: pairs reducing c and d, increasing e
theorem drain : ∀ k c d e, ⟨0, 0, c+k, d+2*k, e⟩ [fm]⊢* ⟨(0 : ℕ), 0, c, d, e+2*k⟩ := by
  intro k; induction k with
  | zero => intro c d e; exists 0
  | succ k ih =>
    intro c d e
    rw [show c + (k + 1) = (c + k) + 1 from by ring,
        show d + 2 * (k + 1) = d + 2 * k + 1 + 1 from by ring]
    step fm
    rw [show d + 2 * k + 1 = (d + 2 * k) + 1 from by ring]
    show ⟨0, 0 + 1, (c + k) + 1, (d + 2 * k) + 1, e + 1⟩ [fm]⊢* ⟨0, 0, c, d, e + 2 * (k + 1)⟩
    step fm
    apply stepStar_trans (ih _ _ _)
    ring_nf; finish

-- Expand phase: 3 steps per round (R3, R2, R2)
-- (0, B+1, C, 0, F+2*k) →* (0, B+1+k, C+2*k, 0, F)
theorem expand : ∀ k B C F, ⟨0, B+1, C, 0, F+2*k⟩ [fm]⊢* ⟨(0 : ℕ), B+1+k, C+2*k, 0, F⟩ := by
  intro k; induction k with
  | zero => intro B C F; exists 0
  | succ k ih =>
    intro B C F
    -- State: (0, B+1, C, 0, F+2*(k+1))
    -- R3: b>=1 → (2, B, C, 0, F+2k+2)
    rw [show F + 2 * (k + 1) = F + 2 * k + 2 from by ring]
    apply stepStar_trans (c₂ := ⟨2, B, C, 0, F + 2 * k + 2⟩)
    · rw [show B + 1 = B + 0 + 1 from by ring]; step fm; ring_nf; finish
    -- R2: a>=1, e>=1 → (1, B+1, C+1, 0, F+2k+1)
    apply stepStar_trans (c₂ := ⟨1, B+1, C+1, 0, F + 2 * k + 1⟩)
    · rw [show (2 : ℕ) = 1 + 1 from by ring,
          show F + 2 * k + 2 = (F + 2 * k + 1) + 1 from by ring]
      step fm; finish
    -- R2: a>=1, e>=1 → (0, B+2, C+2, 0, F+2k)
    apply stepStar_trans (c₂ := ⟨0, B+2, C+2, 0, F + 2 * k⟩)
    · rw [show (1 : ℕ) = 0 + 1 from by ring,
          show F + 2 * k + 1 = (F + 2 * k) + 1 from by ring]
      step fm; finish
    -- Now apply IH with B+1
    have h := ih (B + 1) (C + 2) F
    rw [show B + 2 = (B + 1) + 1 from by ring]
    apply stepStar_trans h
    ring_nf; finish

-- Main transition: (0, 0, 0, 2, 2*(m+1)) ⊢⁺ (0, 0, 0, 2, 4*(m+1)+2)
theorem main_trans (m : ℕ) : ⟨0, 0, 0, 2, 2*m+2⟩ [fm]⊢⁺ ⟨0, 0, 0, 2, 4*m+6⟩ := by
  -- Phase 1: 8 fixed steps to reach (0, 2, 3, 0, 2m)
  -- (0, 0, 0, 2, 2m+2): R5
  rw [show (2 : ℕ) = 1 + 1 from by ring]
  apply step_stepStar_stepPlus (c₂ := ⟨0, 1, 0, 1, 2*m+3⟩)
  · rw [show 2 * m + 2 = (2 * m + 2) from rfl,
        show 2 * m + 3 = 2 * m + 2 + 1 from by ring]
    simp [fm]
  -- (0, 1, 0, 1, 2m+3): R3
  apply stepStar_trans (c₂ := ⟨2, 0, 0, 1, 2*m+3⟩)
  · rw [show (1 : ℕ) = 0 + 1 from by ring]; step fm; finish
  -- (2, 0, 0, 1, 2m+3): R2
  apply stepStar_trans (c₂ := ⟨1, 1, 1, 1, 2*m+2⟩)
  · rw [show (2 : ℕ) = 1 + 1 from by ring,
        show 2 * m + 3 = (2 * m + 2) + 1 from by ring]
    step fm; finish
  -- (1, 1, 1, 1, 2m+2): R1
  apply stepStar_trans (c₂ := ⟨1, 0, 0, 0, 2*m+3⟩)
  · rw [show (1 : ℕ) = 0 + 1 from by ring,
        show 2 * m + 2 = (2 * m + 2) from rfl]
    step fm; finish
  -- (1, 0, 0, 0, 2m+3): R2
  apply stepStar_trans (c₂ := ⟨0, 1, 1, 0, 2*m+2⟩)
  · rw [show (1 : ℕ) = 0 + 1 from by ring,
        show 2 * m + 3 = (2 * m + 2) + 1 from by ring]
    step fm; finish
  -- (0, 1, 1, 0, 2m+2): R3
  apply stepStar_trans (c₂ := ⟨2, 0, 1, 0, 2*m+2⟩)
  · rw [show (1 : ℕ) = 0 + 1 from by ring]; step fm; finish
  -- (2, 0, 1, 0, 2m+2): R2
  apply stepStar_trans (c₂ := ⟨1, 1, 2, 0, 2*m+1⟩)
  · rw [show (2 : ℕ) = 1 + 1 from by ring,
        show 2 * m + 2 = (2 * m + 1) + 1 from by ring]
    step fm; finish
  -- (1, 1, 2, 0, 2m+1): R2
  apply stepStar_trans (c₂ := ⟨0, 2, 3, 0, 2*m⟩)
  · rw [show (1 : ℕ) = 0 + 1 from by ring,
        show 2 * m + 1 = (2 * m) + 1 from by ring]
    step fm; finish
  -- Phase 2: Expand (0, 2, 3, 0, 2m) →* (0, m+2, 2m+1, 0, 0) -- wait
  -- (0, 2, 3, 0, 2*m) with B+1=2, so B=1, C=3, F=0, k=m
  -- expand m 1 3 0: (0, 1+1, 3, 0, 0+2*m) →* (0, 1+1+m, 3+2*m, 0, 0)
  apply stepStar_trans (c₂ := ⟨0, m+2, 2*m+3, 0, 0⟩)
  · have h := expand m 1 3 0
    rw [show (0 : ℕ) + 2 * m = 2 * m from by ring] at h
    rw [show (2 : ℕ) = 1 + 1 from by ring,
        show m + 2 = 1 + 1 + m from by ring,
        show 2 * m + 3 = 3 + 2 * m from by ring]
    exact h
  -- Phase 3: b_to_a (0, m+2, 2m+3, 0, 0) →* (2m+4, 0, 2m+3, 0, 0)
  apply stepStar_trans (c₂ := ⟨2*m+4, 0, 2*m+3, 0, 0⟩)
  · have h := b_to_a (m+2) 0 0 (2*m+3)
    simp only [Nat.zero_add] at h
    rw [show 2 * (m + 2) = 2 * m + 4 from by ring] at h
    exact h
  -- Phase 4: a_to_d (2m+4, 0, 2m+3, 0, 0) →* (0, 0, 2m+3, 4m+8, 0)
  apply stepStar_trans (c₂ := ⟨0, 0, 2*m+3, 4*m+8, 0⟩)
  · have h := a_to_d (2*m+4) 0 (2*m+3) 0
    simp only [Nat.zero_add] at h
    rw [show 2 * (2 * m + 4) = 4 * m + 8 from by ring] at h
    exact h
  -- Phase 5: drain (0, 0, 2m+3, 4m+8, 0) →* (0, 0, 0, 2, 4m+6)
  -- drain (2*m+3) 0 2 0: (0, 0, 0+(2m+3), 2+2*(2m+3), 0) →* (0, 0, 0, 2, 0+2*(2m+3))
  -- 2+2*(2m+3) = 2+4m+6 = 4m+8 ✓
  -- 2*(2m+3) = 4m+6 ✓
  · have h := drain (2*m+3) 0 2 0
    simp only [Nat.zero_add] at h
    rw [show 2 + 2 * (2 * m + 3) = 4 * m + 8 from by ring,
        show 2 * (2 * m + 3) = 4 * m + 6 from by ring] at h
    exact h

theorem nonhalt : ¬halts fm c₀ := by
  -- Execute from c₀ to reach (0, 0, 0, 2, 2) = first recurrent state
  apply stepStar_not_halts_not_halts (c₂ := ⟨0, 0, 0, 2, 2⟩) (by execute fm 11)
  -- Use progress_nonhalt_simple with parameter m where state is (0, 0, 0, 2, 2m+2)
  apply progress_nonhalt_simple (fm := fm) (A := ℕ)
    (fun m ↦ ⟨0, 0, 0, 2, 2*m+2⟩) 0
  intro m
  refine ⟨2*m+2, ?_⟩
  show ⟨0, 0, 0, 2, 2 * m + 2⟩ [fm]⊢⁺ ⟨0, 0, 0, 2, 2 * (2 * m + 2) + 2⟩
  rw [show 2 * (2 * m + 2) + 2 = 4 * m + 6 from by ring]
  exact main_trans m

end Sz22_2003_unofficial_231
