import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #1122: [5/6, 44/245, 343/2, 3/11, 5/7]

Vector representation:
```
-1 -1  1  0  0
 2  0 -1 -2  1
-1  0  0  3  0
 0  1  0  0 -1
 0  0  1 -1  0
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_1122

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a+1, b+1, c, d, e⟩ => some ⟨a, b, c+1, d, e⟩
  | ⟨a, b, c+1, d+2, e⟩ => some ⟨a+2, b, c, d, e+1⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b, c, d+3, e⟩
  | ⟨a, b, c, d, e+1⟩ => some ⟨a, b+1, c, d, e⟩
  | ⟨a, b, c, d+1, e⟩ => some ⟨a, b, c+1, d, e⟩
  | _ => none

-- R3 chain: drain a into d.
theorem a_to_d : ∀ k, ⟨a + k, 0, 0, d, e⟩ [fm]⊢* ⟨a, 0, 0, d + 3 * k, e⟩ := by
  intro k; induction' k with k ih generalizing a d e
  · exists 0
  · rw [show a + (k + 1) = (a + k) + 1 from by ring]
    step fm
    apply stepStar_trans (ih (a := a) (d := d + 3) (e := e))
    ring_nf; finish

-- R4 chain: drain e into b.
theorem e_to_b : ∀ k, ⟨0, b, 0, d, e + k⟩ [fm]⊢* ⟨0, b + k, 0, d, e⟩ := by
  intro k; induction' k with k ih generalizing b d e
  · exists 0
  · rw [show e + (k + 1) = (e + k) + 1 from by ring]
    step fm
    apply stepStar_trans (ih (b := b + 1) (d := d) (e := e))
    ring_nf; finish

-- R2 chain: with b=0, drain c into a and e.
theorem r2_chain : ∀ k, ∀ a c d e, ⟨a, 0, c + k, d + 2 * k, e⟩ [fm]⊢*
    ⟨a + 2 * k, 0, c, d, e + k⟩ := by
  intro k; induction' k with k ih <;> intro a c d e
  · exists 0
  · rw [show c + (k + 1) = (c + k) + 1 from by ring,
        show d + 2 * (k + 1) = (d + 2 * k) + 2 from by ring]
    step fm
    apply stepStar_trans (ih (a + 2) c d (e + 1))
    ring_nf; finish

-- Iterated R1-R1-R2 rounds.
theorem r112_chain : ∀ k, ∀ b c d e, ⟨2, 2 * k + b, c, d + 2 * k, e⟩ [fm]⊢*
    ⟨2, b, c + k, d, e + k⟩ := by
  intro k; induction' k with k ih <;> intro b c d e
  · simp
    exists 0
  · rw [show 2 * (k + 1) + b = (2 * k + b) + 1 + 1 from by ring,
        show d + 2 * (k + 1) = (d + 2 * k) + 2 from by ring]
    step fm; step fm; step fm
    apply stepStar_trans (ih b (c + 1) d (e + 1))
    ring_nf; finish

-- Even spiral: (2, 2*m, 0, d + 4*m, 1) →* (2*m+2, 0, 0, d, 2*m+1)
theorem spiral_even : ∀ m, ∀ d, ⟨2, 2 * m, 0, d + 4 * m, 1⟩ [fm]⊢*
    ⟨2 * m + 2, 0, 0, d, 2 * m + 1⟩ := by
  intro m d
  -- r112_chain m rounds: (2, 2*m, 0, d+4*m, 1) with b=0, consuming 2m from d.
  -- (2, 2*m+0, 0, (d+2*m)+2*m, 1) →* (2, 0, 0+m, d+2*m, 1+m)
  rw [show (2 : ℕ) * m = 2 * m + 0 from by ring,
      show d + 4 * m = (d + 2 * m) + 2 * m from by ring]
  apply stepStar_trans (r112_chain m 0 0 (d + 2 * m) 1)
  -- Now at (2, 0, m, d+2*m, m+1). r2_chain m steps.
  rw [show (0 : ℕ) + m = 0 + m from by ring]
  apply stepStar_trans (r2_chain m 2 0 d (1 + m))
  ring_nf; finish

-- Odd spiral: (2, 2*m+1, 0, d + 4*m + 2, 1) →* (2*m+3, 0, 0, d, 2*m+2)
theorem spiral_odd : ∀ m, ∀ d, ⟨2, 2 * m + 1, 0, d + 4 * m + 2, 1⟩ [fm]⊢*
    ⟨2 * m + 3, 0, 0, d, 2 * m + 2⟩ := by
  intro m d
  -- r112_chain m rounds: (2, 2*m+1, 0, d+4*m+2, 1)
  -- = (2, 2*m+1, 0, (d+2*m+2)+2*m, 1) →* (2, 1, m, d+2*m+2, m+1)
  rw [show d + 4 * m + 2 = (d + 2 * m + 2) + 2 * m from by ring]
  apply stepStar_trans (r112_chain m 1 0 (d + 2 * m + 2) 1)
  -- Now at (2, 1, m, d+2*m+2, m+1). R1 step.
  rw [show d + 2 * m + 2 = (d + 2 * (m + 1)) from by ring,
      show (0 : ℕ) + m = m from by ring,
      show (1 : ℕ) + m = m + 1 from by ring,
      show (m : ℕ) = 0 + m from by ring]
  step fm
  -- Now at (1, 0, m+1, d+2*(m+1), m+1). r2_chain (m+1) steps.
  simp only [Nat.zero_add]
  have h := r2_chain (m + 1) 1 0 d (m + 1)
  rw [show (0 : ℕ) + (m + 1) = m + 1 from by ring,
      show (1 : ℕ) + 2 * (m + 1) = 2 * m + 3 from by ring,
      show m + 1 + (m + 1) = 2 * m + 2 from by ring] at h
  exact h

-- Main transition: (n+2, 0, 0, T, n+1) →⁺ (n+3, 0, 0, T+n+1, n+2)
theorem main_transition : ∀ n T, ⟨n + 2, 0, 0, T, n + 1⟩ [fm]⊢⁺
    ⟨n + 3, 0, 0, T + n + 1, n + 2⟩ := by
  intro n T
  -- Phase 1: R3 drain a.
  apply stepStar_stepPlus_stepPlus
  · rw [show (n : ℕ) + 2 = 0 + (n + 2) from by ring]
    exact a_to_d (n + 2) (a := 0) (d := T) (e := n + 1)
  -- Phase 2: R4 drain e.
  apply stepStar_stepPlus_stepPlus
  · rw [show (n : ℕ) + 1 = 0 + (n + 1) from by ring]
    exact e_to_b (n + 1) (b := 0) (d := T + 3 * (n + 2)) (e := 0)
  -- Phases 3+4: R5 then R2.
  rw [show T + 3 * (n + 2) = (T + n + 1 + 2 * (n + 1)) + 1 + 2 from by ring]
  step fm  -- R5
  step fm  -- R2
  -- State: (2, 0+(n+1), 0, T+n+1+2*(n+1), 1). Need to rewrite 0+(n+1) to match spiral.
  rcases Nat.even_or_odd (n + 1) with ⟨m, hm⟩ | ⟨m, hm⟩
  · -- n+1 even: n+1 = m+m
    have hm' : n + 1 = 2 * m := by omega
    rw [show (0 : ℕ) + (n + 1) = 2 * m from by omega,
        show T + n + 1 + 2 * (n + 1) = (T + n + 1) + 4 * m from by omega]
    apply stepStar_trans (spiral_even m (T + n + 1))
    rw [show 2 * m + 2 = n + 3 from by omega,
        show 2 * m + 1 = n + 2 from by omega]
    finish
  · -- n+1 odd: n+1 = 2*m+1
    have hm' : n + 1 = 2 * m + 1 := by omega
    rw [show (0 : ℕ) + (n + 1) = 2 * m + 1 from by omega,
        show T + n + 1 + 2 * (n + 1) = (T + n + 1) + 4 * m + 2 from by omega]
    apply stepStar_trans (spiral_odd m (T + n + 1))
    rw [show 2 * m + 3 = n + 3 from by omega,
        show 2 * m + 2 = n + 2 from by omega]
    finish

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨2, 0, 0, 0, 1⟩)
  · execute fm 3
  apply progress_nonhalt_simple (fm := fm) (A := ℕ × ℕ)
    (fun ⟨n, T⟩ ↦ ⟨n + 2, 0, 0, T, n + 1⟩) ⟨0, 0⟩
  intro ⟨n, T⟩
  exact ⟨⟨n + 1, T + n + 1⟩, main_transition n T⟩

end Sz22_2003_unofficial_1122
