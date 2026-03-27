import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #245: [11/105, 5/33, 294/11, 3/7, 121/2]

Vector representation:
```
 0 -1 -1 -1  1
 0 -1  1  0 -1
 1  1  0  2 -1
 0  1  0 -1  0
-1  0  0  0  2
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_245

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a, b+1, c+1, d+1, e⟩ => some ⟨a, b, c, d, e+1⟩
  | ⟨a, b+1, c, d, e+1⟩ => some ⟨a, b, c+1, d, e⟩
  | ⟨a, b, c, d, e+1⟩ => some ⟨a+1, b+1, c, d+2, e⟩
  | ⟨a, b, c, d+1, e⟩ => some ⟨a, b+1, c, d, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b, c, d, e+2⟩
  | _ => none

-- R4 chain: d → b (when c = 0, e = 0)
theorem r4_chain : ∀ k a b d, ⟨a, b, 0, d + k, 0⟩ [fm]⊢* ⟨a, b + k, 0, d, 0⟩ := by
  intro k; induction k with
  | zero => intro a b d; exists 0
  | succ k ih =>
    intro a b d
    rw [show d + (k + 1) = (d + k) + 1 from by ring]
    step fm
    apply stepStar_trans (ih a (b + 1) d)
    rw [show b + 1 + k = b + (k + 1) from by ring]; finish

-- R1/R3 loop with e=1: consumes c, increases a and d
theorem r13_loop : ∀ k a c d, d ≥ 1 →
    ⟨a, 1, c + k, d, 1⟩ [fm]⊢* ⟨a + k, 1, c, d + k, 1⟩ := by
  intro k; induction k with
  | zero => intro a c d _; exists 0
  | succ k ih =>
    intro a c d hd
    rw [show c + (k + 1) = (c + k) + 1 from by ring]
    obtain ⟨d', rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : d ≠ 0)
    rw [show (1 : ℕ) = 0 + 1 from by ring]
    step fm
    rw [show (2 : ℕ) = 1 + 1 from by ring]
    step fm
    have h := ih (a + 1) c (d' + 2) (by omega)
    rw [show a + 1 + k = a + (k + 1) from by ring,
        show d' + 2 + k = d' + 1 + (k + 1) from by ring] at h
    exact h

-- R1/R3 loop with e=0: consumes c, increases a and d
theorem r13_loop_e0 : ∀ k a c d, d ≥ 1 →
    ⟨a, 1, c + k, d, 0⟩ [fm]⊢* ⟨a + k, 1, c, d + k, 0⟩ := by
  intro k; induction k with
  | zero => intro a c d _; exists 0
  | succ k ih =>
    intro a c d hd
    rw [show c + (k + 1) = (c + k) + 1 from by ring]
    obtain ⟨d', rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : d ≠ 0)
    rw [show (1 : ℕ) = 0 + 1 from by ring]
    step fm
    step fm
    have h := ih (a + 1) c (d' + 2) (by omega)
    rw [show a + 1 + k = a + (k + 1) from by ring,
        show d' + 2 + k = d' + 1 + (k + 1) from by ring] at h
    exact h

-- R5/R2/R2 loop: consumes a and b, increases c
theorem r52_loop : ∀ k a b c, ⟨a + k, 2 * k + b, c, 0, 0⟩ [fm]⊢* ⟨a, b, c + 2 * k, 0, 0⟩ := by
  intro k; induction k with
  | zero => intro a b c; simp; exists 0
  | succ k ih =>
    intro a b c
    rw [show a + (k + 1) = (a + k) + 1 from by ring,
        show 2 * (k + 1) + b = (2 * k + b) + 1 + 1 from by ring]
    -- R5
    step fm
    -- R2
    rw [show (2 : ℕ) = 0 + 1 + 1 from by ring]
    step fm
    -- R2
    step fm
    -- now at (a+k, 2k+b, c+2, 0, 0)
    have h := ih a b (c + 2)
    rw [show c + 2 + 2 * k = c + 2 * (k + 1) from by ring] at h
    exact h

-- Main transition: (a+1, 0, 2*m, 0, 0) ⊢⁺ (a+2*m+1, 0, 2*m+6, 0, 0)
theorem main_trans (a m : ℕ) :
    ⟨a + 1, 0, 2 * m, 0, 0⟩ [fm]⊢⁺ ⟨a + 2 * m + 1, 0, 2 * m + 6, 0, 0⟩ := by
  -- Phase 1: R5
  apply step_stepStar_stepPlus (c₂ := ⟨a, 0, 2 * m, 0, 2⟩)
  · simp [fm]
  -- R3
  apply stepStar_trans (c₂ := ⟨a + 1, 1, 2 * m, 2, 1⟩)
  · rw [show (2 : ℕ) = 1 + 1 from by ring]; step fm; finish
  -- r13_loop(2m)
  apply stepStar_trans (c₂ := ⟨a + 2 * m + 1, 1, 0, 2 * m + 2, 1⟩)
  · have h := r13_loop (2 * m) (a + 1) 0 2 (by omega)
    simp only [Nat.zero_add] at h
    rw [show a + 1 + 2 * m = a + 2 * m + 1 from by ring,
        show 2 + 2 * m = 2 * m + 2 from by ring] at h
    exact h
  -- R2
  apply stepStar_trans (c₂ := ⟨a + 2 * m + 1, 0, 1, 2 * m + 2, 0⟩)
  · rw [show (1 : ℕ) = 0 + 1 from by ring]
    step fm; finish
  -- R4
  apply stepStar_trans (c₂ := ⟨a + 2 * m + 1, 1, 1, 2 * m + 1, 0⟩)
  · rw [show 2 * m + 2 = (2 * m + 1) + 1 from by ring]
    step fm; finish
  -- R1
  apply stepStar_trans (c₂ := ⟨a + 2 * m + 1, 0, 0, 2 * m, 1⟩)
  · rw [show (1 : ℕ) = 0 + 1 from by ring,
        show 2 * m + 1 = (2 * m) + 1 from by ring]
    step fm; finish
  -- R3
  apply stepStar_trans (c₂ := ⟨a + 2 * m + 2, 1, 0, 2 * m + 2, 0⟩)
  · step fm
    rw [show a + 2 * m + 1 + 1 = a + 2 * m + 2 from by ring,
        show 2 * m + 2 = 2 * m + 2 from rfl]; finish
  -- r4_chain(2m+2)
  apply stepStar_trans (c₂ := ⟨a + 2 * m + 2, 2 * m + 3, 0, 0, 0⟩)
  · have h := r4_chain (2 * m + 2) (a + 2 * m + 2) 1 0
    simp only [Nat.zero_add] at h
    rw [show 1 + (2 * m + 2) = 2 * m + 3 from by ring] at h
    exact h
  -- Phase 2: r52_loop (k=m+1, b=1)
  apply stepStar_trans (c₂ := ⟨a + m + 1, 1, 2 * m + 2, 0, 0⟩)
  · have h := r52_loop (m + 1) (a + m + 1) 1 0
    simp only [Nat.zero_add] at h
    rw [show a + m + 1 + (m + 1) = a + 2 * m + 2 from by ring,
        show 2 * (m + 1) + 1 = 2 * m + 3 from by ring,
        show 2 * (m + 1) = 2 * m + 2 from by ring] at h
    exact h
  -- Phase 3: R5
  apply stepStar_trans (c₂ := ⟨a + m, 1, 2 * m + 2, 0, 2⟩)
  · rw [show a + m + 1 = (a + m) + 1 from by ring]
    step fm; finish
  -- R2
  apply stepStar_trans (c₂ := ⟨a + m, 0, 2 * m + 3, 0, 1⟩)
  · rw [show (1 : ℕ) = 0 + 1 from by ring,
        show (2 : ℕ) = 1 + 1 from by ring]
    step fm
    rw [show 2 * m + 2 + 1 = 2 * m + 3 from by ring]; finish
  -- R3
  apply stepStar_trans (c₂ := ⟨a + m + 1, 1, 2 * m + 3, 2, 0⟩)
  · step fm
    rw [show a + m + 1 = a + m + 1 from rfl]; finish
  -- r13_loop_e0(2m+3)
  apply stepStar_trans (c₂ := ⟨a + 3 * m + 4, 1, 0, 2 * m + 5, 0⟩)
  · have h := r13_loop_e0 (2 * m + 3) (a + m + 1) 0 2 (by omega)
    simp only [Nat.zero_add] at h
    rw [show a + m + 1 + (2 * m + 3) = a + 3 * m + 4 from by ring,
        show 2 + (2 * m + 3) = 2 * m + 5 from by ring] at h
    exact h
  -- r4_chain(2m+5)
  apply stepStar_trans (c₂ := ⟨a + 3 * m + 4, 2 * m + 6, 0, 0, 0⟩)
  · have h := r4_chain (2 * m + 5) (a + 3 * m + 4) 1 0
    simp only [Nat.zero_add] at h
    rw [show 1 + (2 * m + 5) = 2 * m + 6 from by ring] at h
    exact h
  -- Phase 4: r52_loop (k=m+3, b=0)
  · have h := r52_loop (m + 3) (a + 2 * m + 1) 0 0
    simp only [Nat.zero_add] at h
    rw [show a + 2 * m + 1 + (m + 3) = a + 3 * m + 4 from by ring,
        show 2 * (m + 3) + 0 = 2 * m + 6 from by ring,
        show 2 * (m + 3) = 2 * m + 6 from by ring] at h
    exact h

theorem nonhalt : ¬halts fm c₀ := by
  apply progress_nonhalt_simple (fm := fm) (A := ℕ × ℕ)
    (fun ⟨a, m⟩ ↦ ⟨a + 1, 0, 2 * m, 0, 0⟩) ⟨0, 0⟩
  intro ⟨a, m⟩
  refine ⟨⟨a + 2 * m, m + 3⟩, ?_⟩
  show ⟨a + 1, 0, 2 * m, 0, 0⟩ [fm]⊢⁺ ⟨(a + 2 * m) + 1, 0, 2 * (m + 3), 0, 0⟩
  rw [show (a + 2 * m) + 1 = a + 2 * m + 1 from by ring,
      show 2 * (m + 3) = 2 * m + 6 from by ring]
  exact main_trans a m

end Sz22_2003_unofficial_245
