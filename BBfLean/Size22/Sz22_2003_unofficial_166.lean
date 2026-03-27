import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #166: [1/45, 5/77, 182/5, 1/7, 33/13, 5/2]

Vector representation:
```
 0 -2 -1  0  0  0
 0  0  1 -1 -1  0
 1  0 -1  1  0  1
 0  0  0 -1  0  0
 0  1  0  0  1 -1
-1  0  1  0  0  0
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_166

def Q := ℕ × ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a, b+2, c+1, d, e, f⟩ => some ⟨a, b, c, d, e, f⟩
  | ⟨a, b, c, d+1, e+1, f⟩ => some ⟨a, b, c+1, d, e, f⟩
  | ⟨a, b, c+1, d, e, f⟩ => some ⟨a+1, b, c, d+1, e, f+1⟩
  | ⟨a, b, c, d+1, e, f⟩ => some ⟨a, b, c, d, e, f⟩
  | ⟨a, b, c, d, e, f+1⟩ => some ⟨a, b+1, c, d, e+1, f⟩
  | ⟨a+1, b, c, d, e, f⟩ => some ⟨a, b, c+1, d, e, f⟩
  | _ => none

-- Inner pump with b=0: interleaved R2/R3.
theorem inner_pump_0 : ∀ k a e f,
    ⟨a, 0, 0, 1, e + k, f⟩ [fm]⊢* ⟨a + k, (0 : ℕ), 0, 1, e, f + k⟩ := by
  intro k; induction k with
  | zero => intro a e f; exists 0
  | succ k ih =>
    intro a e f
    rw [show e + (k + 1) = (e + k) + 1 from by ring]
    step fm; step fm
    apply stepStar_trans (ih _ _ _)
    ring_nf; finish

-- Inner pump with b=1: interleaved R2/R3.
theorem inner_pump_1 : ∀ k a e f,
    ⟨a, 1, 0, 1, e + k, f⟩ [fm]⊢* ⟨a + k, (1 : ℕ), 0, 1, e, f + k⟩ := by
  intro k; induction k with
  | zero => intro a e f; exists 0
  | succ k ih =>
    intro a e f
    rw [show e + (k + 1) = (e + k) + 1 from by ring]
    step fm; step fm
    apply stepStar_trans (ih _ _ _)
    ring_nf; finish

-- Full pump with b=0: (a+1, 0, 0, 0, e, 0) ->* (a+e+1, 0, 0, 0, 0, e+1)
theorem pump_0 (a e : ℕ) :
    ⟨a + 1, 0, 0, 0, e, 0⟩ [fm]⊢* ⟨a + e + 1, (0 : ℕ), 0, 0, 0, e + 1⟩ := by
  apply stepStar_trans (c₂ := ⟨a, 0, 1, 0, e, 0⟩)
  · step fm; finish
  apply stepStar_trans (c₂ := ⟨a + 1, 0, 0, 1, e, 1⟩)
  · step fm; finish
  apply stepStar_trans (c₂ := ⟨a + 1 + e, 0, 0, 1, 0, 1 + e⟩)
  · have h := inner_pump_0 e (a + 1) 0 1
    simp only [Nat.zero_add] at h; exact h
  step fm; ring_nf; finish

-- Full pump with b=1: (a+1, 1, 0, 0, e, 0) ->* (a+e+1, 1, 0, 0, 0, e+1)
theorem pump_1 (a e : ℕ) :
    ⟨a + 1, 1, 0, 0, e, 0⟩ [fm]⊢* ⟨a + e + 1, (1 : ℕ), 0, 0, 0, e + 1⟩ := by
  apply stepStar_trans (c₂ := ⟨a, 1, 1, 0, e, 0⟩)
  · step fm; finish
  apply stepStar_trans (c₂ := ⟨a + 1, 1, 0, 1, e, 1⟩)
  · step fm; finish
  apply stepStar_trans (c₂ := ⟨a + 1 + e, 1, 0, 1, 0, 1 + e⟩)
  · have h := inner_pump_1 e (a + 1) 0 1
    simp only [Nat.zero_add] at h; exact h
  step fm; ring_nf; finish

-- f -> b, e: R5 repeated. (A, b, 0, 0, e, f+k) ->* (A, b+k, 0, 0, e+k, f)
theorem f_to_be : ∀ k A b e f,
    ⟨A, b, 0, 0, e, f + k⟩ [fm]⊢* ⟨A, b + k, (0 : ℕ), 0, e + k, f⟩ := by
  intro k; induction k with
  | zero => intro A b e f; exists 0
  | succ k ih =>
    intro A b e f
    rw [show f + (k + 1) = (f + k) + 1 from by ring]
    step fm
    apply stepStar_trans (ih _ _ _ _)
    ring_nf; finish

-- Descend with even b: (a+k, 2*k, 0, 0, e, 0) ->* (a, 0, 0, 0, e, 0)
theorem descend : ∀ k a e,
    ⟨a + k, 2 * k, 0, 0, e, 0⟩ [fm]⊢* ⟨a, (0 : ℕ), 0, 0, e, 0⟩ := by
  intro k; induction k with
  | zero => intro a e; exists 0
  | succ k ih =>
    intro a e
    rw [show a + (k + 1) = (a + k) + 1 from by ring,
        show 2 * (k + 1) = 2 * k + 1 + 1 from by ring]
    step fm
    rw [show 2 * k + 1 = (2 * k) + 1 from by ring]
    step fm
    apply stepStar_trans (ih _ _)
    ring_nf; finish

-- Descend with odd b: (a+k, 2*k+1, 0, 0, e, 0) ->* (a, 1, 0, 0, e, 0)
theorem descend_odd : ∀ k a e,
    ⟨a + k, 2 * k + 1, 0, 0, e, 0⟩ [fm]⊢* ⟨a, (1 : ℕ), 0, 0, e, 0⟩ := by
  intro k; induction k with
  | zero => intro a e; exists 0
  | succ k ih =>
    intro a e
    rw [show a + (k + 1) = (a + k) + 1 from by ring,
        show 2 * (k + 1) + 1 = 2 * k + 1 + 1 + 1 from by ring]
    step fm
    rw [show 2 * k + 1 + 1 = (2 * k + 1) + 1 from by ring]
    step fm
    apply stepStar_trans (ih _ _)
    ring_nf; finish

-- Main transition: C(n) ⊢⁺ C(n+1)
-- C(n) = (4n²+3n+1, 0, 0, 0, 4n+3, 0)
theorem main_trans (n : ℕ) :
    ⟨4*n^2 + 3*n + 1, 0, 0, 0, 4*n + 3, 0⟩ [fm]⊢⁺
    ⟨4*n^2 + 11*n + 8, (0 : ℕ), 0, 0, 4*n + 7, 0⟩ := by
  -- Phase 1: pump_0
  apply stepStar_stepPlus_stepPlus (c₂ := ⟨4*n^2 + 7*n + 4, 0, 0, 0, 0, 4*n + 4⟩)
  · have h := pump_0 (4*n^2 + 3*n) (4*n + 3)
    rw [show 4 * n ^ 2 + 3 * n + (4 * n + 3) + 1 = 4 * n ^ 2 + 7 * n + 4 from by ring,
        show (4 * n + 3) + 1 = 4 * n + 4 from by ring] at h
    exact h
  -- Phase 2: first R5 step, then f_to_be
  apply step_stepStar_stepPlus (c₂ := ⟨4*n^2 + 7*n + 4, 1, 0, 0, 1, 4*n + 3⟩)
  · rw [show (4 : ℕ) * n + 4 = (4 * n + 3) + 1 from by ring]; simp [fm]
  apply stepStar_trans (c₂ := ⟨4*n^2 + 7*n + 4, 4*n + 4, 0, 0, 4*n + 4, 0⟩)
  · have h := f_to_be (4*n + 3) (4*n^2 + 7*n + 4) 1 1 0
    rw [show (0 : ℕ) + (4 * n + 3) = 4 * n + 3 from by ring,
        show 1 + (4 * n + 3) = 4 * n + 4 from by ring] at h
    exact h
  -- Phase 3: descend (even B = 4n+4 = 2*(2n+2))
  apply stepStar_trans (c₂ := ⟨4*n^2 + 5*n + 2, 0, 0, 0, 4*n + 4, 0⟩)
  · have h := descend (2*n + 2) (4*n^2 + 5*n + 2) (4*n + 4)
    rw [show 4 * n ^ 2 + 5 * n + 2 + (2 * n + 2) = 4 * n ^ 2 + 7 * n + 4 from by ring,
        show 2 * (2 * n + 2) = 4 * n + 4 from by ring] at h
    exact h
  -- Phase 4: pump_0
  apply stepStar_trans (c₂ := ⟨4*n^2 + 9*n + 6, 0, 0, 0, 0, 4*n + 5⟩)
  · have h := pump_0 (4*n^2 + 5*n + 1) (4*n + 4)
    rw [show 4 * n ^ 2 + 5 * n + 1 + 1 = 4 * n ^ 2 + 5 * n + 2 from by ring,
        show 4 * n ^ 2 + 5 * n + 1 + (4 * n + 4) + 1 = 4 * n ^ 2 + 9 * n + 6 from by ring,
        show (4 * n + 4) + 1 = 4 * n + 5 from by ring] at h
    exact h
  -- Phase 5: f_to_be
  apply stepStar_trans (c₂ := ⟨4*n^2 + 9*n + 6, 4*n + 5, 0, 0, 4*n + 5, 0⟩)
  · have h := f_to_be (4*n + 5) (4*n^2 + 9*n + 6) 0 0 0
    simp only [Nat.zero_add] at h; exact h
  -- Phase 6: descend_odd (odd B = 4n+5 = 2*(2n+2)+1)
  apply stepStar_trans (c₂ := ⟨4*n^2 + 7*n + 4, 1, 0, 0, 4*n + 5, 0⟩)
  · have h := descend_odd (2*n + 2) (4*n^2 + 7*n + 4) (4*n + 5)
    rw [show 4 * n ^ 2 + 7 * n + 4 + (2 * n + 2) = 4 * n ^ 2 + 9 * n + 6 from by ring,
        show 2 * (2 * n + 2) + 1 = 4 * n + 5 from by ring] at h
    exact h
  -- Phase 7: pump_1
  apply stepStar_trans (c₂ := ⟨4*n^2 + 11*n + 9, 1, 0, 0, 0, 4*n + 6⟩)
  · have h := pump_1 (4*n^2 + 7*n + 3) (4*n + 5)
    rw [show 4 * n ^ 2 + 7 * n + 3 + 1 = 4 * n ^ 2 + 7 * n + 4 from by ring,
        show 4 * n ^ 2 + 7 * n + 3 + (4 * n + 5) + 1 = 4 * n ^ 2 + 11 * n + 9 from by ring,
        show (4 * n + 5) + 1 = 4 * n + 6 from by ring] at h
    exact h
  -- Phase 8: f_to_be (from b=1)
  apply stepStar_trans (c₂ := ⟨4*n^2 + 11*n + 9, 4*n + 7, 0, 0, 4*n + 6, 0⟩)
  · have h := f_to_be (4*n + 6) (4*n^2 + 11*n + 9) 1 0 0
    simp only [Nat.zero_add] at h
    rw [show 1 + (4 * n + 6) = 4 * n + 7 from by ring] at h
    exact h
  -- Phase 9: descend_odd (odd B = 4n+7 = 2*(2n+3)+1)
  apply stepStar_trans (c₂ := ⟨4*n^2 + 9*n + 6, 1, 0, 0, 4*n + 6, 0⟩)
  · have h := descend_odd (2*n + 3) (4*n^2 + 9*n + 6) (4*n + 6)
    rw [show 4 * n ^ 2 + 9 * n + 6 + (2 * n + 3) = 4 * n ^ 2 + 11 * n + 9 from by ring,
        show 2 * (2 * n + 3) + 1 = 4 * n + 7 from by ring] at h
    exact h
  -- Phase 10: pump_1
  apply stepStar_trans (c₂ := ⟨4*n^2 + 13*n + 12, 1, 0, 0, 0, 4*n + 7⟩)
  · have h := pump_1 (4*n^2 + 9*n + 5) (4*n + 6)
    rw [show 4 * n ^ 2 + 9 * n + 5 + 1 = 4 * n ^ 2 + 9 * n + 6 from by ring,
        show 4 * n ^ 2 + 9 * n + 5 + (4 * n + 6) + 1 = 4 * n ^ 2 + 13 * n + 12 from by ring,
        show (4 * n + 6) + 1 = 4 * n + 7 from by ring] at h
    exact h
  -- Phase 11: f_to_be (from b=1)
  apply stepStar_trans (c₂ := ⟨4*n^2 + 13*n + 12, 4*n + 8, 0, 0, 4*n + 7, 0⟩)
  · have h := f_to_be (4*n + 7) (4*n^2 + 13*n + 12) 1 0 0
    simp only [Nat.zero_add] at h
    rw [show 1 + (4 * n + 7) = 4 * n + 8 from by ring] at h
    exact h
  -- Phase 12: descend (even B = 4n+8 = 2*(2n+4))
  · have h := descend (2*n + 4) (4*n^2 + 11*n + 8) (4*n + 7)
    rw [show 4 * n ^ 2 + 11 * n + 8 + (2 * n + 4) = 4 * n ^ 2 + 13 * n + 12 from by ring,
        show 2 * (2 * n + 4) = 4 * n + 8 from by ring] at h
    exact h

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨1, 0, 0, 0, 3, 0⟩) (by execute fm 27)
  have key : ∀ n : ℕ, ∃ n', (⟨4*n^2 + 3*n + 1, 0, 0, 0, 4*n + 3, 0⟩ : Q) [fm]⊢⁺
      ⟨4*n'^2 + 3*n' + 1, 0, 0, 0, 4*n' + 3, 0⟩ := by
    intro n
    refine ⟨n + 1, ?_⟩
    rw [show 4 * (n + 1) ^ 2 + 3 * (n + 1) + 1 = 4 * n ^ 2 + 11 * n + 8 from by ring,
        show 4 * (n + 1) + 3 = 4 * n + 7 from by ring]
    exact main_trans n
  have h := progress_nonhalt_simple (fm := fm) (A := ℕ)
    (fun n ↦ ⟨4*n^2 + 3*n + 1, 0, 0, 0, 4*n + 3, 0⟩) 0 key
  simp only [Nat.mul_zero, Nat.zero_add, Nat.add_zero] at h
  exact h

end Sz22_2003_unofficial_166
