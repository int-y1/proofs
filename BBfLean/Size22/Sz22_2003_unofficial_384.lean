import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #384: [2/15, 99/14, 25/2, 7/11, 22/5]

Vector representation:
```
 1 -1 -1  0  0
-1  2  0 -1  1
-1  0  2  0  0
 0  0  0  1 -1
 1  0 -1  0  1
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_384

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a, b+1, c+1, d, e⟩ => some ⟨a+1, b, c, d, e⟩
  | ⟨a+1, b, c, d+1, e⟩ => some ⟨a, b+2, c, d, e+1⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b, c+2, d, e⟩
  | ⟨a, b, c, d, e+1⟩ => some ⟨a, b, c, d+1, e⟩
  | ⟨a, b, c+1, d, e⟩ => some ⟨a+1, b, c, d, e+1⟩
  | _ => none

-- R4 chain: move e to d
theorem e_to_d : ∀ k c d e, ⟨0, 0, c, d, e+k⟩ [fm]⊢* ⟨0, 0, c, d+k, e⟩ := by
  intro k; induction' k with k h <;> intro c d e
  · exists 0
  rw [show e + (k + 1) = (e + k) + 1 from by ring]
  step fm
  apply stepStar_trans (h _ _ _)
  ring_nf; finish

-- R3 chain: move a to c (when d=0, b=0)
theorem a_to_c : ∀ k a c e, ⟨a+k, 0, c, 0, e⟩ [fm]⊢* ⟨a, 0, c+2*k, 0, e⟩ := by
  intro k; induction' k with k h <;> intro a c e
  · exists 0
  rw [show a + (k + 1) = (a + k) + 1 from by ring]
  step fm
  apply stepStar_trans (h _ _ _)
  ring_nf; finish

-- Climb chain: repeated (R2, R1, R1)
-- (a+1, 0, c+2k, d+k, e) ⊢* (a+k+1, 0, c, d, e+k)
theorem climb : ∀ k a c d e, ⟨a+1, 0, c+2*k, d+k, e⟩ [fm]⊢* ⟨a+k+1, 0, c, d, e+k⟩ := by
  intro k; induction k with
  | zero => intro a c d e; exists 0
  | succ k ih =>
    intro a c d e
    -- Step 1: R2
    have h1 : fm ⟨a+1, 0, c + 2 * (k + 1), (d + k) + 1, e⟩ =
              some ⟨a, 0+2, c + 2 * (k + 1), d + k, e + 1⟩ := by simp [fm]
    rw [show d + (k + 1) = (d + k) + 1 from by ring]
    apply stepStar_trans (step_stepStar h1)
    -- Step 2: R1
    have h2 : fm ⟨a, (0+1)+1, (c + 2 * k + 1) + 1, d + k, e + 1⟩ =
              some ⟨a + 1, 0 + 1, c + 2 * k + 1, d + k, e + 1⟩ := by simp [fm]
    rw [show c + 2 * (k + 1) = (c + 2 * k + 1) + 1 from by ring,
        show (0 : ℕ) + 2 = (0 + 1) + 1 from by ring]
    apply stepStar_trans (step_stepStar h2)
    -- Step 3: R1
    have h3 : fm ⟨a + 1, 0 + 1, (c + 2 * k) + 1, d + k, e + 1⟩ =
              some ⟨a + 1 + 1, 0, c + 2 * k, d + k, e + 1⟩ := by simp [fm]
    rw [show c + 2 * k + 1 = (c + 2 * k) + 1 from by ring]
    apply stepStar_trans (step_stepStar h3)
    -- Now use IH
    have h4 := ih (a + 1) c d (e + 1)
    rw [show a + 1 + 1 = (a + 1) + 1 from by ring] at *
    refine stepStar_trans h4 ?_
    ring_nf; finish

-- R2 drain (c=0): repeated R2 steps
-- (a+k, b, 0, d+k, e) ⊢* (a, b+2k, 0, d, e+k)
theorem r2_drain : ∀ k a b d e, ⟨a+k, b, 0, d+k, e⟩ [fm]⊢* ⟨a, b+2*k, 0, d, e+k⟩ := by
  intro k; induction k with
  | zero => intro a b d e; exists 0
  | succ k ih =>
    intro a b d e
    rw [show a + (k + 1) = (a + k) + 1 from by ring,
        show d + (k + 1) = (d + k) + 1 from by ring]
    step fm
    apply stepStar_trans (ih _ _ _ _)
    ring_nf; finish

-- Tail: (a+1, b, 0, 0, e) ⊢* (0, 0, 2*(a+1)+b, 0, e)
theorem tail : ∀ b, ∀ a e, ⟨a+1, b, 0, 0, e⟩ [fm]⊢* ⟨0, 0, 2*(a+1)+b, 0, e⟩ := by
  intro b; induction' b using Nat.strongRecOn with b ih; intro a e
  rcases b with _ | _ | b
  · -- b=0: just a_to_c
    have h := a_to_c (a+1) 0 0 e
    simp only [Nat.zero_add] at h
    simp only [(by ring : 2 * (a + 1) + 0 = 2 * (a + 1))]
    exact h
  · -- b=1: R3, R1, then a_to_c
    step fm; step fm
    show ⟨a+1, 0, 1, 0, e⟩ [fm]⊢* ⟨0, 0, 2 * (a + 1) + 1, 0, e⟩
    have h := a_to_c (a+1) 0 1 e
    simp only [Nat.zero_add, (by ring : 1 + 2 * (a + 1) = 2 * (a + 1) + 1)] at h
    exact h
  · -- b+2: R3, R1, R1, then IH with a+1, b
    step fm; step fm; step fm
    show ⟨(a+1)+1, b, 0, 0, e⟩ [fm]⊢* ⟨0, 0, 2 * (a + 1) + (b + 2), 0, e⟩
    have h := ih b (by omega) (a+1) e
    simp only [(by ring : 2 * ((a + 1) + 1) + b = 2 * (a + 1) + (b + 2))] at h
    exact h

-- Main transition for n=0
theorem trans_base : ⟨0, 0, 2, 0, 0⟩ [fm]⊢⁺ ⟨0, 0, 3, 0, 1⟩ := by
  execute fm 2

-- Main transition for odd n: n = 2*m+1, m ≥ 0
theorem trans_odd (m : ℕ) : ⟨0, 0, 2*m+3, 0, 2*m+1⟩ [fm]⊢⁺ ⟨0, 0, 2*m+4, 0, 2*m+2⟩ := by
  -- Phase 1: e_to_d: (0, 0, 2m+3, 0, 2m+1) ⊢* (0, 0, 2m+3, 2m+1, 0)
  apply stepStar_stepPlus_stepPlus
  · have h := e_to_d (2*m+1) (2*m+3) 0 0
    simp only [Nat.zero_add] at h; exact h
  -- Phase 2: R5 step: (0, 0, 2m+3, 2m+1, 0) → (1, 0, 2m+2, 2m+1, 1)
  apply step_stepStar_stepPlus
  · show fm ⟨0, 0, (2*m+2)+1, 2*m+1, 0⟩ = some ⟨0+1, 0, 2*m+2, 2*m+1, 0+1⟩
    simp [fm]
  -- Phase 3: climb k=m+1: (1, 0, 2m+2, 2m+1, 1) ⊢* (m+2, 0, 0, m, m+2)
  apply stepStar_trans (c₂ := ⟨m+2, 0, 0, m, m+2⟩)
  · have h := climb (m+1) 0 0 m 1
    simp only [Nat.zero_add,
               (by ring : 0 + 2 * (m + 1) = 2 * m + 2),
               (by ring : m + (m + 1) = 2 * m + 1),
               (by ring : 1 + (m + 1) = m + 2)] at h
    exact h
  -- Phase 4: r2_drain k=m: (m+2, 0, 0, m, m+2) ⊢* (2, 2m, 0, 0, 2m+2)
  apply stepStar_trans (c₂ := ⟨2, 2*m, 0, 0, 2*m+2⟩)
  · have h := r2_drain m 2 0 0 (m+2)
    simp only [Nat.zero_add,
               (by ring : 2 + m = m + 2),
               (by ring : 0 + 2 * m = 2 * m),
               (by ring : m + 2 + m = 2 * m + 2)] at h
    exact h
  -- Phase 5: tail: (2, 2m, 0, 0, 2m+2) ⊢* (0, 0, 2m+4, 0, 2m+2)
  have h := tail (2*m) 1 (2*m+2)
  simp only [(by ring : 1 + 1 = 2),
             (by ring : 2 * (1 + 1) + 2 * m = 2 * m + 4)] at h
  exact h

-- Main transition for even n: n = 2*(m+1), m ≥ 0
theorem trans_even (m : ℕ) : ⟨0, 0, 2*m+4, 0, 2*m+2⟩ [fm]⊢⁺ ⟨0, 0, 2*m+5, 0, 2*m+3⟩ := by
  -- Phase 1: e_to_d: (0, 0, 2m+4, 0, 2m+2) ⊢* (0, 0, 2m+4, 2m+2, 0)
  apply stepStar_stepPlus_stepPlus
  · have h := e_to_d (2*m+2) (2*m+4) 0 0
    simp only [Nat.zero_add] at h; exact h
  -- Phase 2: R5 step: (0, 0, 2m+4, 2m+2, 0) → (1, 0, 2m+3, 2m+2, 1)
  apply step_stepStar_stepPlus
  · show fm ⟨0, 0, (2*m+3)+1, 2*m+2, 0⟩ = some ⟨0+1, 0, 2*m+3, 2*m+2, 0+1⟩
    simp [fm]
  -- Phase 3: climb k=m+1: (1, 0, 2m+3, 2m+2, 1) ⊢* (m+2, 0, 1, m+1, m+2)
  apply stepStar_trans (c₂ := ⟨m+2, 0, 1, m+1, m+2⟩)
  · have h := climb (m+1) 0 1 (m+1) 1
    simp only [Nat.zero_add,
               (by ring : 1 + 2 * (m + 1) = 2 * m + 3),
               (by ring : m + 1 + (m + 1) = 2 * m + 2),
               (by ring : 1 + (m + 1) = m + 2)] at h
    exact h
  -- Phase 4: R2, R1: (m+2, 0, 1, m+1, m+2) → (m+1, 2, 1, m, m+3) → (m+2, 1, 0, m, m+3)
  have hr2 : fm ⟨(m+1)+1, 0, 1, m+1, m+2⟩ = some ⟨m+1, 0+2, 1, m, m+2+1⟩ := by simp [fm]
  rw [show m + 2 = (m + 1) + 1 from by ring]
  apply stepStar_trans (step_stepStar hr2)
  have hr1 : fm ⟨m+1, (0+1)+1, 0+1, m, m+2+1⟩ = some ⟨m+1+1, 0+1, 0, m, m+2+1⟩ := by simp [fm]
  rw [show (0 : ℕ) + 2 = (0 + 1) + 1 from by ring,
      show (1 : ℕ) = 0 + 1 from by ring]
  apply stepStar_trans (step_stepStar hr1)
  -- Now: (m+2, 1, 0, m, m+3)
  rw [show m + 1 + 1 = m + 2 from by ring,
      show (0 : ℕ) + 1 = 1 from by ring,
      show m + 2 + 1 = m + 3 from by ring]
  -- Phase 5: r2_drain k=m: (m+2, 1, 0, m, m+3) ⊢* (2, 2m+1, 0, 0, 2m+3)
  apply stepStar_trans (c₂ := ⟨2, 2*m+1, 0, 0, 2*m+3⟩)
  · have h := r2_drain m 2 1 0 (m+3)
    simp only [Nat.zero_add,
               (by ring : 2 + m = m + 2),
               (by ring : 1 + 2 * m = 2 * m + 1),
               (by ring : m + 3 + m = 2 * m + 3)] at h
    exact h
  -- Phase 6: tail: (2, 2m+1, 0, 0, 2m+3) ⊢* (0, 0, 2m+5, 0, 2m+3)
  have h := tail (2*m+1) 1 (2*m+3)
  simp only [(by ring : 1 + 1 = 2),
             (by ring : 2 * (1 + 1) + (2 * m + 1) = 2 * m + 5)] at h
  exact h

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨0, 0, 2, 0, 0⟩) (by execute fm 1)
  apply progress_nonhalt_simple (fm := fm) (A := ℕ) (fun n ↦ ⟨0, 0, n+2, 0, n⟩) 0
  intro n
  rcases n with _ | n
  · exact ⟨1, trans_base⟩
  rcases Nat.even_or_odd n with ⟨m, hm⟩ | ⟨m, hm⟩
  · -- n = 2m, so n+1 = 2m+1 (odd)
    subst hm
    exists m + m + 2
    show ⟨0, 0, m + m + 1 + 2, 0, m + m + 1⟩ [fm]⊢⁺ ⟨0, 0, (m + m + 2) + 2, 0, m + m + 2⟩
    simp only [(by ring : m + m + 1 = 2 * m + 1),
               (by ring : m + m + 2 = 2 * m + 2)]
    exact trans_odd m
  · -- n = 2m+1, so n+1 = 2m+2 = 2*(m+1) (even)
    subst hm
    exists 2 * m + 1 + 2
    show ⟨0, 0, 2 * m + 1 + 1 + 2, 0, 2 * m + 1 + 1⟩ [fm]⊢⁺
         ⟨0, 0, (2 * m + 1 + 2) + 2, 0, 2 * m + 1 + 2⟩
    simp only [(by ring : 2 * m + 1 + 1 + 2 = 2 * m + 4),
               (by ring : 2 * m + 1 + 1 = 2 * m + 2),
               (by ring : 2 * m + 1 + 2 + 2 = 2 * m + 5),
               (by ring : 2 * m + 1 + 2 = 2 * m + 3)]
    exact trans_even m

end Sz22_2003_unofficial_384
