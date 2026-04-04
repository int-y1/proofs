import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #1893: [9/35, 5/363, 98/3, 11/7, 21/2]

Vector representation:
```
 0  2 -1 -1  0
 0 -1  1  0 -2
 1 -1  0  2  0
 0  0  0 -1  1
-1  1  0  1  0
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_1893

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a, b, c+1, d+1, e⟩ => some ⟨a, b+2, c, d, e⟩
  | ⟨a, b+1, c, d, e+2⟩ => some ⟨a, b, c+1, d, e⟩
  | ⟨a, b+1, c, d, e⟩ => some ⟨a+1, b, c, d+2, e⟩
  | ⟨a, b, c, d+1, e⟩ => some ⟨a, b, c, d, e+1⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b+1, c, d+1, e⟩
  | _ => none

theorem d_to_e : ∀ k, ⟨a, 0, 0, d + k, e⟩ [fm]⊢* ⟨a, 0, 0, d, e + k⟩ := by
  intro k; induction' k with k ih generalizing d e
  · exists 0
  · rw [show d + (k + 1) = (d + k) + 1 from by ring]
    step fm
    apply stepStar_trans (ih (d := d) (e := e + 1))
    ring_nf; finish

theorem r3_chain_e1 : ∀ k, ⟨a, b + k, 0, d, 1⟩ [fm]⊢* ⟨a + k, b, 0, d + 2 * k, 1⟩ := by
  intro k; induction' k with k ih generalizing a b d
  · exists 0
  · rw [show b + (k + 1) = (b + k) + 1 from by ring]
    step fm
    apply stepStar_trans (ih (a := a + 1) (b := b) (d := d + 2))
    ring_nf; finish

theorem r3_chain_e0 : ∀ k, ⟨a, b + k, 0, d, 0⟩ [fm]⊢* ⟨a + k, b, 0, d + 2 * k, 0⟩ := by
  intro k; induction' k with k ih generalizing a b d
  · exists 0
  · rw [show b + (k + 1) = (b + k) + 1 from by ring]
    step fm
    apply stepStar_trans (ih (a := a + 1) (b := b) (d := d + 2))
    ring_nf; finish

theorem drain_step_c0 : ⟨a + 1, 0, 0, 0, r + 6⟩ [fm]⊢* ⟨a, 0, 2, 0, r⟩ := by
  step fm; step fm; step fm; step fm; step fm; finish

theorem drain_step_cpos : ⟨a + 1, 0, c + 1, 0, r + 6⟩ [fm]⊢* ⟨a, 0, c + 3, 0, r⟩ := by
  step fm; step fm; step fm; step fm; step fm; finish

theorem drain : ∀ k, ∀ a s, ⟨a + k, 0, 0, 0, 6 * k + s⟩ [fm]⊢* ⟨a, 0, 2 * k, 0, s⟩ := by
  intro k; induction' k with k ih
  · intro a s; ring_nf; exists 0
  · intro a s
    rw [show a + (k + 1) = (a + 1) + k from by ring,
        show 6 * (k + 1) + s = 6 * k + (s + 6) from by ring]
    apply stepStar_trans (ih (a + 1) (s + 6))
    rcases k with _ | k
    · show ⟨a + 1, 0, 0, 0, s + 6⟩ [fm]⊢* ⟨a, 0, 2, 0, s⟩
      exact drain_step_c0
    · show ⟨a + 1, 0, 2 * (k + 1), 0, s + 6⟩ [fm]⊢* ⟨a, 0, 2 * (k + 1) + 2, 0, s⟩
      rw [show 2 * (k + 1) = (2 * k + 1) + 1 from by ring,
          show (2 * k + 1) + 1 + 2 = (2 * k + 1) + 3 from by ring]
      exact drain_step_cpos

theorem base_e3_c0 : ⟨a + 1, 0, 0, 0, 3⟩ [fm]⊢* ⟨a, 2, 0, 0, 1⟩ := by
  step fm; step fm; step fm; finish

theorem base_e3_cpos : ⟨a + 1, 0, c + 1, 0, 3⟩ [fm]⊢* ⟨a, 2, c + 1, 0, 1⟩ := by
  step fm; step fm; step fm; finish

theorem full_drain_e3 : ∀ k, ⟨a + k + 1, 0, 0, 0, 6 * k + 3⟩ [fm]⊢* ⟨a, 2, 2 * k, 0, 1⟩ := by
  intro k
  rw [show a + k + 1 = (a + 1) + k from by ring]
  apply stepStar_trans (drain k (a + 1) 3)
  rcases k with _ | k
  · exact base_e3_c0
  · show ⟨a + 1, 0, 2 * (k + 1), 0, 3⟩ [fm]⊢* ⟨a, 2, 2 * (k + 1), 0, 1⟩
    rw [show 2 * (k + 1) = (2 * k + 1) + 1 from by ring]
    exact base_e3_cpos

theorem base_e5_c0 : ⟨a + 1, 0, 0, 0, 5⟩ [fm]⊢* ⟨a, 1, 1, 0, 1⟩ := by
  step fm; step fm; step fm; step fm; finish

theorem base_e5_cpos : ⟨a + 1, 0, c + 1, 0, 5⟩ [fm]⊢* ⟨a, 1, c + 2, 0, 1⟩ := by
  step fm; step fm; step fm; step fm; finish

theorem full_drain_e5 : ∀ k, ⟨a + k + 1, 0, 0, 0, 6 * k + 5⟩ [fm]⊢* ⟨a, 1, 2 * k + 1, 0, 1⟩ := by
  intro k
  rw [show a + k + 1 = (a + 1) + k from by ring]
  apply stepStar_trans (drain k (a + 1) 5)
  rcases k with _ | k
  · exact base_e5_c0
  · show ⟨a + 1, 0, 2 * (k + 1), 0, 5⟩ [fm]⊢* ⟨a, 1, 2 * (k + 1) + 1, 0, 1⟩
    rw [show 2 * (k + 1) = (2 * k + 1) + 1 from by ring,
        show (2 * k + 1) + 1 + 1 = (2 * k + 1) + 2 from by ring]
    exact base_e5_cpos

theorem base_e6_c0 : ⟨a + 2, 0, 0, 0, 6⟩ [fm]⊢* ⟨a + 1, 0, 2, 0, 0⟩ := by
  step fm; step fm; step fm; step fm; step fm; finish

theorem base_e6_cpos : ⟨a + 2, 0, c + 1, 0, 6⟩ [fm]⊢* ⟨a + 1, 0, c + 3, 0, 0⟩ := by
  step fm; step fm; step fm; step fm; step fm; finish

theorem full_drain_e6 : ∀ k, ⟨a + k + 2, 0, 0, 0, 6 * k + 6⟩ [fm]⊢* ⟨a + 1, 0, 2 * k + 2, 0, 0⟩ := by
  intro k
  rw [show a + k + 2 = (a + 2) + k from by ring]
  apply stepStar_trans (drain k (a + 2) 6)
  rcases k with _ | k
  · exact base_e6_c0
  · show ⟨a + 2, 0, 2 * (k + 1), 0, 6⟩ [fm]⊢* ⟨a + 1, 0, 2 * (k + 1) + 2, 0, 0⟩
    rw [show 2 * (k + 1) = (2 * k + 1) + 1 from by ring,
        show (2 * k + 1) + 1 + 2 = (2 * k + 1) + 3 from by ring]
    exact base_e6_cpos

-- Resolution round: R3+R1+R1 takes (a, b+1, c+2, 0, 1) to (a+1, b+4, c, 0, 1)
-- Iterated k times for even c: (a, b+1, 2k, 0, 1) ->* (a+k, b+3k+1, 0, 0, 1)
theorem resolve_even : ∀ k, ⟨a, b + 1, 2 * k, 0, 1⟩ [fm]⊢* ⟨a + k, b + 3 * k + 1, 0, 0, 1⟩ := by
  intro k; induction' k with k ih generalizing a b
  · ring_nf; exists 0
  · rw [show 2 * (k + 1) = 2 * k + 2 from by ring]
    step fm; step fm; step fm
    show ⟨a + 1, b + 4, 2 * k, 0, 1⟩ [fm]⊢* ⟨a + (k + 1), b + 3 * (k + 1) + 1, 0, 0, 1⟩
    rw [show b + 4 = (b + 3) + 1 from by ring]
    apply stepStar_trans (ih (a := a + 1) (b := b + 3))
    rw [show a + 1 + k = a + (k + 1) from by ring,
        show b + 3 + 3 * k + 1 = b + 3 * (k + 1) + 1 from by ring]
    finish

-- Iterated k times for odd c: (a, b+1, 2k+1, 0, 1) ->* (a+k, b+3k+1, 1, 0, 1)
theorem resolve_odd : ∀ k, ⟨a, b + 1, 2 * k + 1, 0, 1⟩ [fm]⊢* ⟨a + k, b + 3 * k + 1, 1, 0, 1⟩ := by
  intro k; induction' k with k ih generalizing a b
  · ring_nf; exists 0
  · rw [show 2 * (k + 1) + 1 = (2 * k + 1) + 2 from by ring]
    step fm; step fm; step fm
    show ⟨a + 1, b + 4, 2 * k + 1, 0, 1⟩ [fm]⊢* ⟨a + (k + 1), b + 3 * (k + 1) + 1, 1, 0, 1⟩
    rw [show b + 4 = (b + 3) + 1 from by ring]
    apply stepStar_trans (ih (a := a + 1) (b := b + 3))
    rw [show a + 1 + k = a + (k + 1) from by ring,
        show b + 3 + 3 * k + 1 = b + 3 * (k + 1) + 1 from by ring]
    finish

-- Same for e=0
theorem resolve_even_e0 : ∀ k, ⟨a, b + 1, 2 * k, 0, 0⟩ [fm]⊢* ⟨a + k, b + 3 * k + 1, 0, 0, 0⟩ := by
  intro k; induction' k with k ih generalizing a b
  · ring_nf; exists 0
  · rw [show 2 * (k + 1) = 2 * k + 2 from by ring]
    step fm; step fm; step fm
    show ⟨a + 1, b + 4, 2 * k, 0, 0⟩ [fm]⊢* ⟨a + (k + 1), b + 3 * (k + 1) + 1, 0, 0, 0⟩
    rw [show b + 4 = (b + 3) + 1 from by ring]
    apply stepStar_trans (ih (a := a + 1) (b := b + 3))
    rw [show a + 1 + k = a + (k + 1) from by ring,
        show b + 3 + 3 * k + 1 = b + 3 * (k + 1) + 1 from by ring]
    finish

theorem resolve_odd_e0 : ∀ k, ⟨a, b + 1, 2 * k + 1, 0, 0⟩ [fm]⊢* ⟨a + k, b + 3 * k + 1, 1, 0, 0⟩ := by
  intro k; induction' k with k ih generalizing a b
  · ring_nf; exists 0
  · rw [show 2 * (k + 1) + 1 = (2 * k + 1) + 2 from by ring]
    step fm; step fm; step fm
    show ⟨a + 1, b + 4, 2 * k + 1, 0, 0⟩ [fm]⊢* ⟨a + (k + 1), b + 3 * (k + 1) + 1, 1, 0, 0⟩
    rw [show b + 4 = (b + 3) + 1 from by ring]
    apply stepStar_trans (ih (a := a + 1) (b := b + 3))
    rw [show a + 1 + k = a + (k + 1) from by ring,
        show b + 3 + 3 * k + 1 = b + 3 * (k + 1) + 1 from by ring]
    finish

-- resolve_e3: (a, 2, 2k, 0, 1) -> (a+k, 3k+2, 0, 0, 1)
theorem resolve_e3 : ∀ k, ⟨a, 2, 2 * k, 0, 1⟩ [fm]⊢* ⟨a + k, 3 * k + 2, 0, 0, 1⟩ := by
  intro k
  rw [show (2 : ℕ) = 1 + 1 from by ring]
  apply stepStar_trans (resolve_even k (a := a) (b := 1))
  rw [show 1 + 3 * k + 1 = 3 * k + 2 from by ring]
  finish

-- resolve_e5: (a, 1, 2k+1, 0, 1) -> (a+k+1, 3k+2, 0, 1, 1)
-- k rounds of R3+R1+R1 giving (a+k, 3k+1, 1, 0, 1), then R3+R1
theorem resolve_e5 : ∀ k, ⟨a, 1, 2 * k + 1, 0, 1⟩ [fm]⊢* ⟨a + k + 1, 3 * k + 2, 0, 1, 1⟩ := by
  intro k
  rw [show (1 : ℕ) = 0 + 1 from by ring]
  apply stepStar_trans (resolve_odd k (a := a) (b := 0))
  rw [show 0 + 3 * k + 1 = 3 * k + 1 from by ring]
  step fm; step fm
  rw [show a + k + 1 = a + k + 1 from rfl]
  finish

-- resolve_e6: (a+1, 0, 2k+2, 0, 0) -> (a+k+2, 3k+3, 0, 3, 0)
-- R5: (a, 1, 2k+2, 1, 0) -> R1: (a, 3, 2k+1, 0, 0)
-- k rounds of R3+R1+R1: (a+k, 3k+3, 1, 0, 0)
-- R3: (a+k+1, 3k+2, 1, 2, 0) -> R1: (a+k+1, 3k+4, 0, 1, 0) -> R3: (a+k+2, 3k+3, 0, 3, 0)
theorem resolve_e6 : ∀ k, ⟨a + 1, 0, 2 * k + 2, 0, 0⟩ [fm]⊢* ⟨a + k + 2, 3 * k + 3, 0, 3, 0⟩ := by
  intro k
  rw [show 2 * k + 2 = (2 * k + 1) + 1 from by ring]
  step fm; step fm
  show ⟨a, 3, 2 * k + 1, 0, 0⟩ [fm]⊢* ⟨a + k + 2, 3 * k + 3, 0, 3, 0⟩
  rw [show (3 : ℕ) = 2 + 1 from by ring]
  apply stepStar_trans (resolve_odd_e0 k (a := a) (b := 2))
  rw [show 2 + 3 * k + 1 = 3 * k + 3 from by ring]
  step fm; step fm; step fm
  rw [show a + k + 2 = a + k + 1 + 1 from by ring]
  finish

theorem macro_star : ⟨m + k + 1, 0, 0, 0, 6 * k + 3⟩ [fm]⊢* ⟨m + 10 * k + 7, 0, 0, 0, 6 * k + 9⟩ := by
  -- Step 1: drain + resolve + R3 chain + R4 drain
  apply stepStar_trans (full_drain_e3 k (a := m))
  apply stepStar_trans (resolve_e3 k (a := m))
  rw [show 3 * k + 2 = 0 + (3 * k + 2) from by ring]
  apply stepStar_trans (r3_chain_e1 (3 * k + 2) (a := m + k) (b := 0) (d := 0))
  rw [show m + k + (3 * k + 2) = m + 4 * k + 2 from by ring,
      show 0 + 2 * (3 * k + 2) = 6 * k + 4 from by ring,
      show 6 * k + 4 = 0 + (6 * k + 4) from by ring]
  apply stepStar_trans (d_to_e (6 * k + 4) (a := m + 4 * k + 2) (d := 0) (e := 1))
  rw [show 1 + (6 * k + 4) = 6 * k + 5 from by ring]
  -- Step 2: drain + resolve + R3 chain + R4 drain
  rw [show m + 4 * k + 2 = (m + 3 * k + 1) + k + 1 from by ring]
  apply stepStar_trans (full_drain_e5 k (a := m + 3 * k + 1))
  apply stepStar_trans (resolve_e5 k (a := m + 3 * k + 1))
  rw [show m + 3 * k + 1 + k + 1 = m + 4 * k + 2 from by ring,
      show 3 * k + 2 = 0 + (3 * k + 2) from by ring]
  apply stepStar_trans (r3_chain_e1 (3 * k + 2) (a := m + 4 * k + 2) (b := 0) (d := 1))
  rw [show m + 4 * k + 2 + (3 * k + 2) = m + 7 * k + 4 from by ring,
      show 1 + 2 * (3 * k + 2) = 6 * k + 5 from by ring,
      show 6 * k + 5 = 0 + (6 * k + 5) from by ring]
  apply stepStar_trans (d_to_e (6 * k + 5) (a := m + 7 * k + 4) (d := 0) (e := 1))
  rw [show 1 + (6 * k + 5) = 6 * k + 6 from by ring]
  -- Step 3: drain + resolve + R3 chain + R4 drain
  rw [show m + 7 * k + 4 = (m + 6 * k + 2) + k + 2 from by ring]
  apply stepStar_trans (full_drain_e6 k (a := m + 6 * k + 2))
  apply stepStar_trans (resolve_e6 k (a := m + 6 * k + 2))
  rw [show m + 6 * k + 2 + k + 2 = m + 7 * k + 4 from by ring,
      show 3 * k + 3 = 0 + (3 * k + 3) from by ring]
  apply stepStar_trans (r3_chain_e0 (3 * k + 3) (a := m + 7 * k + 4) (b := 0) (d := 3))
  rw [show m + 7 * k + 4 + (3 * k + 3) = m + 10 * k + 7 from by ring,
      show 3 + 2 * (3 * k + 3) = 6 * k + 9 from by ring,
      show 6 * k + 9 = 0 + (6 * k + 9) from by ring]
  apply stepStar_trans (d_to_e (6 * k + 9) (a := m + 10 * k + 7) (d := 0) (e := 0))
  rw [show 0 + (6 * k + 9) = 6 * k + 9 from by ring]
  finish

theorem main_trans (k : ℕ) :
    ⟨m + k + 1, 0, 0, 0, 6 * k + 3⟩ [fm]⊢⁺ ⟨m + 10 * k + 7, 0, 0, 0, 6 * k + 9⟩ := by
  apply stepStar_stepPlus macro_star
  simp [Q]

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨1, 0, 0, 0, 3⟩) (by execute fm 5)
  apply progress_nonhalt_simple (fm := fm) (A := ℕ × ℕ)
    (fun ⟨m, k⟩ ↦ ⟨m + k + 1, 0, 0, 0, 6 * k + 3⟩) ⟨0, 0⟩
  intro ⟨m, k⟩
  refine ⟨⟨m + 9 * k + 5, k + 1⟩, ?_⟩
  show ⟨m + k + 1, 0, 0, 0, 6 * k + 3⟩ [fm]⊢⁺ ⟨m + 9 * k + 5 + (k + 1) + 1, 0, 0, 0, 6 * (k + 1) + 3⟩
  rw [show m + 9 * k + 5 + (k + 1) + 1 = m + 10 * k + 7 from by ring,
      show 6 * (k + 1) + 3 = 6 * k + 9 from by ring]
  exact main_trans k
