import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #167: [1/45, 50/77, 7/5, 3/7, 605/2]

Vector representation:
```
 0 -2 -1  0  0
 1  0  2 -1 -1
 0  0 -1  1  0
 0  1  0 -1  0
-1  0  1  0  2
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_167

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a, b+2, c+1, d, e⟩ => some ⟨a, b, c, d, e⟩
  | ⟨a, b, c, d+1, e+1⟩ => some ⟨a+1, b, c+2, d, e⟩
  | ⟨a, b, c+1, d, e⟩ => some ⟨a, b, c, d+1, e⟩
  | ⟨a, b, c, d+1, e⟩ => some ⟨a, b+1, c, d, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b, c+1, d, e+2⟩
  | _ => none

-- R3+R2 pairs with b=0
theorem r3r2_b0 : ∀ k a c e,
    ⟨a, 0, c+1, 0, e+k⟩ [fm]⊢* ⟨a+k, (0 : ℕ), c+k+1, 0, e⟩ := by
  intro k; induction k with
  | zero => intro a c e; exists 0
  | succ k ih =>
    intro a c e
    rw [show e + (k + 1) = (e + k) + 1 from by ring]
    step fm
    step fm
    apply stepStar_trans (ih _ _ _)
    ring_nf; finish

-- R3+R2 pairs with b=1
theorem r3r2_b1 : ∀ k a c e,
    ⟨a, 1, c+1, 0, e+k⟩ [fm]⊢* ⟨a+k, (1 : ℕ), c+k+1, 0, e⟩ := by
  intro k; induction k with
  | zero => intro a c e; exists 0
  | succ k ih =>
    intro a c e
    rw [show e + (k + 1) = (e + k) + 1 from by ring]
    step fm
    step fm
    apply stepStar_trans (ih _ _ _)
    ring_nf; finish

-- c → d via R3 (b=0, e=0)
theorem c_to_d_b0 : ∀ k a d,
    ⟨a, 0, k, d, 0⟩ [fm]⊢* ⟨a, (0 : ℕ), 0, d+k, 0⟩ := by
  intro k; induction k with
  | zero => intro a d; simp; exists 0
  | succ k ih =>
    intro a d
    show ⟨a, 0, k + 1, d, 0⟩ [fm]⊢* _
    step fm
    rw [show d + (k + 1) = (d + 1) + k from by ring]
    exact ih a (d + 1)

-- c → d via R3 (b=1, e=0)
theorem c_to_d_b1 : ∀ k a d,
    ⟨a, 1, k, d, 0⟩ [fm]⊢* ⟨a, (1 : ℕ), 0, d+k, 0⟩ := by
  intro k; induction k with
  | zero => intro a d; simp; exists 0
  | succ k ih =>
    intro a d
    show ⟨a, 1, k + 1, d, 0⟩ [fm]⊢* _
    step fm
    rw [show d + (k + 1) = (d + 1) + k from by ring]
    exact ih a (d + 1)

-- d → b via R4 (c=0, e=0)
theorem d_to_b : ∀ k a b,
    ⟨a, b, 0, k, 0⟩ [fm]⊢* ⟨a, b+k, (0 : ℕ), 0, 0⟩ := by
  intro k; induction k with
  | zero => intro a b; simp; exists 0
  | succ k ih =>
    intro a b
    show ⟨a, b, 0, k + 1, 0⟩ [fm]⊢* _
    step fm
    rw [show b + (k + 1) = (b + 1) + k from by ring]
    exact ih a (b + 1)

-- R5+R1 pairs
theorem r5r1_chain : ∀ k a b e,
    ⟨a+k, b+2*k, 0, 0, e⟩ [fm]⊢* ⟨a, b, (0 : ℕ), 0, e+2*k⟩ := by
  intro k; induction k with
  | zero => intro a b e; exists 0
  | succ k ih =>
    intro a b e
    rw [show a + (k + 1) = (a + k) + 1 from by ring,
        show b + 2 * (k + 1) = (b + 2 * k) + 1 + 1 from by ring]
    step fm
    rw [show (b + 2 * k) + 1 = (b + 2 * k + 1) from by ring]
    step fm
    apply stepStar_trans (ih _ _ _)
    ring_nf; finish

-- Main transition: (A+1, 0, 0, 0, 2*F) ⊢⁺ (A+2*F+1, 0, 0, 0, 2*(F+3))
theorem main_trans (A F : ℕ) :
    ⟨A+1, 0, 0, 0, 2*F⟩ [fm]⊢⁺ ⟨A+2*F+1, 0, 0, 0, 2*(F+3)⟩ := by
  -- Phase 1: R5 step
  apply step_stepStar_stepPlus (c₂ := ⟨A, 0, 1, 0, 2*F+2⟩)
  · simp [fm]
  -- Phase 1b: R3+R2 pairs with b=0
  -- r3r2_b0 gives: (A, 0, 1, 0, 2*F+2) →* (A+(2*F+2), 0, (2*F+2)+1, 0, 0)
  apply stepStar_trans (c₂ := ⟨A+2*F+2, 0, 2*F+3, 0, 0⟩)
  · have h := r3r2_b0 (2*F+2) A 0 0; simp only [Nat.zero_add] at h
    -- h : (A, 0, 1, 0, 2*F+2) →* (A+(2*F+2), 0, (2*F+2)+1, 0, 0)
    -- goal: ... →* (A+2*F+2, 0, 2*F+3, 0, 0)
    -- Need to show A+(2*F+2) = A+2*F+2 and (2*F+2)+1 = 2*F+3
    rw [show (2 * F + 2 + 1 : ℕ) = 2 * F + 3 from by ring,
        show (A + (2 * F + 2) : ℕ) = A + 2 * F + 2 from by ring] at h
    exact h
  -- Phase 2: c → d
  apply stepStar_trans (c₂ := ⟨A+2*F+2, 0, 0, 2*F+3, 0⟩)
  · have h := c_to_d_b0 (2*F+3) (A+2*F+2) 0
    simp only [Nat.zero_add] at h; exact h
  -- Phase 3: d → b
  apply stepStar_trans (c₂ := ⟨A+2*F+2, 2*F+3, 0, 0, 0⟩)
  · have h := d_to_b (2*F+3) (A+2*F+2) 0
    simp only [Nat.zero_add] at h; exact h
  -- Phase 4: (F+1) R5+R1 pairs
  -- r5r1_chain gives: (a+(F+1), b+2*(F+1), 0, 0, e) →* (a, b, 0, 0, e+2*(F+1))
  -- We want: (A+2*F+2, 2*F+3, 0, 0, 0) →* (A+F+1, 1, 0, 0, 2*(F+1))
  -- Set a=A+F+1, b=1, e=0, k=F+1
  apply stepStar_trans (c₂ := ⟨A+F+1, 1, 0, 0, 2*(F+1)⟩)
  · have h := r5r1_chain (F+1) (A+F+1) 1 0; simp only [Nat.zero_add] at h
    rw [show A + F + 1 + (F + 1) = A + 2 * F + 2 from by ring,
        show 1 + 2 * (F + 1) = 2 * F + 3 from by ring] at h
    exact h
  -- Phase 5: R5 step
  -- (A+F+1, 1, 0, 0, 2*(F+1)) → (A+F, 1, 1, 0, 2*(F+1)+2)
  apply stepStar_trans (c₂ := ⟨A+F, 1, 1, 0, 2*F+4⟩)
  · rw [show A + F + 1 = (A + F) + 1 from by ring,
        show 2 * (F + 1) = 2 * F + 2 from by ring]
    step fm; ring_nf; finish
  -- Phase 5b: R3+R2 pairs with b=1
  apply stepStar_trans (c₂ := ⟨A+3*F+4, 1, 2*F+5, 0, 0⟩)
  · have h := r3r2_b1 (2*F+4) (A+F) 0 0; simp only [Nat.zero_add] at h
    rw [show A + F + (2 * F + 4) = A + 3 * F + 4 from by ring,
        show (2 * F + 4 + 1 : ℕ) = 2 * F + 5 from by ring] at h
    exact h
  -- Phase 6: c → d
  apply stepStar_trans (c₂ := ⟨A+3*F+4, 1, 0, 2*F+5, 0⟩)
  · have h := c_to_d_b1 (2*F+5) (A+3*F+4) 0
    simp only [Nat.zero_add] at h; exact h
  -- Phase 7: d → b
  apply stepStar_trans (c₂ := ⟨A+3*F+4, 2*F+6, 0, 0, 0⟩)
  · have h := d_to_b (2*F+5) (A+3*F+4) 1
    rw [show 1 + (2 * F + 5) = 2 * F + 6 from by ring] at h
    exact h
  -- Phase 8: (F+3) R5+R1 pairs
  · rw [show (2 * F + 6 : ℕ) = 2 * (F + 3) from by ring]
    have h := r5r1_chain (F+3) (A+2*F+1) 0 0; simp only [Nat.zero_add] at h
    rw [show A + 2 * F + 1 + (F + 3) = A + 3 * F + 4 from by ring] at h
    exact h

theorem nonhalt : ¬halts fm c₀ := by
  apply progress_nonhalt_simple (fm := fm) (A := ℕ × ℕ)
    (fun ⟨A, F⟩ ↦ ⟨A+1, 0, 0, 0, 2*F⟩) ⟨0, 0⟩
  intro ⟨A, F⟩
  refine ⟨⟨A + 2 * F, F + 3⟩, ?_⟩
  show ⟨A + 1, 0, 0, 0, 2 * F⟩ [fm]⊢⁺ ⟨A + 2 * F + 1, 0, 0, 0, 2 * (F + 3)⟩
  exact main_trans A F

end Sz22_2003_unofficial_167
