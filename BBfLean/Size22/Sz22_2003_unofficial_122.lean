import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #122: [1/405, 7/15, 18/7, 25/2, 3/5]

Vector representation:
```
 0 -4 -1  0
 0 -1 -1  1
 1  2  0 -1
-1  0  2  0
 0  1 -1  0
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_122

def Q := ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a, b+4, c+1, d⟩ => some ⟨a, b, c, d⟩
  | ⟨a, b+1, c+1, d⟩ => some ⟨a, b, c, d+1⟩
  | ⟨a, b, c, d+1⟩ => some ⟨a+1, b+2, c, d⟩
  | ⟨a+1, b, c, d⟩ => some ⟨a, b, c+2, d⟩
  | ⟨a, b, c+1, d⟩ => some ⟨a, b+1, c, d⟩
  | _ => none

-- R4 chain: transfer a to c
theorem a_to_c : ∀ k, ⟨a+k, 0, c, 0⟩ [fm]⊢* ⟨a, 0, c+2*k, 0⟩ := by
  intro k; induction' k with k ih generalizing a c
  · simp; exists 0
  rw [show a + (k + 1) = (a + k) + 1 from by ring]
  step fm
  apply stepStar_trans (ih (a := a) (c := c + 2))
  ring_nf; finish

-- Consume loop: interleaved R2/R3
theorem consume_loop : ∀ k, ⟨j+1, 2, 2*k+r, j⟩ [fm]⊢* ⟨j+k+1, 2, r, j+k⟩ := by
  intro k; induction' k with k ih generalizing j r
  · simp; exists 0
  rw [show 2 * (k + 1) + r = 2 * k + (r + 2) from by ring]
  step fm; step fm; step fm
  apply stepStar_trans (ih (j := j + 1) (r := r))
  ring_nf; finish

-- R3 chain: transfer d to a and b
theorem r3_chain : ∀ k, ⟨a, b, 0, d+k⟩ [fm]⊢* ⟨a+k, b+2*k, 0, d⟩ := by
  intro k; induction' k with k ih generalizing a b d
  · simp; exists 0
  rw [show d + (k + 1) = (d + k) + 1 from by ring]
  step fm
  apply stepStar_trans (ih (a := a + 1) (b := b + 2) (d := d))
  ring_nf; finish

-- Phase A: (0, 0, 2n+3, 0) →* (2n+2, 2n+3, 0, 0)
theorem phase_a (n : ℕ) :
    ⟨0, 0, 2*n+3, 0⟩ [fm]⊢* ⟨2*n+2, 2*n+3, 0, 0⟩ := by
  step fm; step fm; step fm
  apply stepStar_trans (consume_loop (j := 0) (r := 1) n)
  simp only [Nat.zero_add]
  step fm
  have h := r3_chain (a := n+1) (b := 1) (d := 0) (n+1)
  simp only [Nat.zero_add] at h
  apply stepStar_trans h
  ring_nf; finish

-- Phase C: (m+2, 4, 0, 0) →* (0, 0, 2m+3, 0)
theorem phase_c (m : ℕ) :
    ⟨m+2, 4, 0, 0⟩ [fm]⊢* ⟨0, 0, 2*m+3, 0⟩ := by
  step fm; step fm
  have h := a_to_c (a := 0) (c := 1) (m+1)
  simp only [Nat.zero_add] at h
  apply stepStar_trans h
  ring_nf; finish

-- B1 single: (a+1, b+8, 0, 0) →* (a, b, 0, 0)
theorem b8_step : ⟨a+1, b+8, 0, 0⟩ [fm]⊢* ⟨a, b, 0, 0⟩ := by
  execute fm 3

-- B1 iterated
theorem b8_iter : ∀ k, ⟨a+k, b+8*k, 0, 0⟩ [fm]⊢* ⟨a, b, 0, 0⟩ := by
  intro k; induction' k with k ih generalizing a b
  · simp; exists 0
  rw [show a + (k + 1) = (a + 1) + k from by ring,
      show b + 8 * (k + 1) = (b + 8) + 8 * k from by ring]
  apply stepStar_trans (ih (a := a + 1) (b := b + 8))
  exact b8_step

-- Tail lemmas
theorem tail_7 : ⟨a+1, 7, 0, 0⟩ [fm]⊢* ⟨a+1, 4, 0, 0⟩ := by execute fm 4
theorem tail_2 : ⟨a+1, 2, 0, 0⟩ [fm]⊢* ⟨a+2, 4, 0, 0⟩ := by execute fm 5

theorem tail_5 : ⟨a+1, 5, 0, 0⟩ [fm]⊢* ⟨a+2, 4, 0, 0⟩ := by
  step fm; step fm; step fm; step fm; exact tail_2

theorem tail_3 : ⟨a+1, 3, 0, 0⟩ [fm]⊢* ⟨a+3, 4, 0, 0⟩ := by
  step fm; step fm; step fm; step fm; step fm
  apply stepStar_trans (tail_5 (a := a+1))
  ring_nf; finish

theorem tail_1 : ⟨a+1, 1, 0, 0⟩ [fm]⊢* ⟨a+4, 4, 0, 0⟩ := by
  step fm; step fm; step fm; step fm; step fm
  apply stepStar_trans (tail_3 (a := a+1))
  ring_nf; finish

-- Helper: Phase A remainder for the main cases.
-- (0, 0, 2*N+3, 0) → 3 steps → (1, 2, 2*N+1, 0) → consume_loop →
-- (N+1, 2, 1, N) → R2 → (N+1, 1, 0, N+1) → r3_chain →
-- (2*N+2, 2*N+3, 0, 0)
-- We inline this into each main case.

-- Case n ≡ 0 (mod 4): n = 4j
theorem main_case0 (j : ℕ) :
    ⟨0, 0, 2*(4*j)+3, 0⟩ [fm]⊢⁺ ⟨0, 0, 2*(7*j+2)+3, 0⟩ := by
  apply step_stepStar_stepPlus
  · show fm ⟨0, 0, 2*(4*j)+3, 0⟩ = some ⟨0, 1, 2*(4*j)+2, 0⟩; rfl
  step fm; step fm
  apply stepStar_trans (consume_loop (j := 0) (r := 1) (4*j))
  simp only [Nat.zero_add]
  step fm
  have h1 := r3_chain (a := 4*j+1) (b := 1) (d := 0) (4*j+1)
  simp only [Nat.zero_add] at h1
  apply stepStar_trans h1
  rw [show 4 * j + 1 + (4 * j + 1) = (7 * j + 2) + j from by ring,
      show 1 + 2 * (4 * j + 1) = 3 + 8 * j from by ring]
  apply stepStar_trans (b8_iter (a := 7*j+2) (b := 3) j)
  rw [show 7 * j + 2 = (7 * j + 1) + 1 from by ring]
  apply stepStar_trans tail_3
  rw [show 7 * j + 1 + 3 = (7 * j + 2) + 2 from by ring]
  exact phase_c (7*j+2)

-- Case n ≡ 1 (mod 4): n = 4j+1
theorem main_case1 (j : ℕ) :
    ⟨0, 0, 2*(4*j+1)+3, 0⟩ [fm]⊢⁺ ⟨0, 0, 2*(7*j+3)+3, 0⟩ := by
  apply step_stepStar_stepPlus
  · show fm ⟨0, 0, 2*(4*j+1)+3, 0⟩ = some ⟨0, 1, 2*(4*j+1)+2, 0⟩; rfl
  step fm; step fm
  apply stepStar_trans (consume_loop (j := 0) (r := 1) (4*j+1))
  simp only [Nat.zero_add]
  step fm
  have h1 := r3_chain (a := 4*j+2) (b := 1) (d := 0) (4*j+2)
  simp only [Nat.zero_add] at h1
  apply stepStar_trans h1
  rw [show 4 * j + 2 + (4 * j + 2) = (7 * j + 4) + j from by ring,
      show 1 + 2 * (4 * j + 2) = 5 + 8 * j from by ring]
  apply stepStar_trans (b8_iter (a := 7*j+4) (b := 5) j)
  rw [show 7 * j + 4 = (7 * j + 3) + 1 from by ring]
  apply stepStar_trans tail_5
  rw [show 7 * j + 3 + 2 = (7 * j + 3) + 2 from by ring]
  exact phase_c (7*j+3)

-- Case n ≡ 2 (mod 4): n = 4j+2
theorem main_case2 (j : ℕ) :
    ⟨0, 0, 2*(4*j+2)+3, 0⟩ [fm]⊢⁺ ⟨0, 0, 2*(7*j+4)+3, 0⟩ := by
  apply step_stepStar_stepPlus
  · show fm ⟨0, 0, 2*(4*j+2)+3, 0⟩ = some ⟨0, 1, 2*(4*j+2)+2, 0⟩; rfl
  step fm; step fm
  apply stepStar_trans (consume_loop (j := 0) (r := 1) (4*j+2))
  simp only [Nat.zero_add]
  step fm
  have h1 := r3_chain (a := 4*j+3) (b := 1) (d := 0) (4*j+3)
  simp only [Nat.zero_add] at h1
  apply stepStar_trans h1
  rw [show 4 * j + 3 + (4 * j + 3) = (7 * j + 6) + j from by ring,
      show 1 + 2 * (4 * j + 3) = 7 + 8 * j from by ring]
  apply stepStar_trans (b8_iter (a := 7*j+6) (b := 7) j)
  rw [show 7 * j + 6 = (7 * j + 5) + 1 from by ring]
  apply stepStar_trans tail_7
  rw [show 7 * j + 5 + 1 = (7 * j + 4) + 2 from by ring]
  exact phase_c (7*j+4)

-- Case n ≡ 3 (mod 4): n = 4j+3
theorem main_case3 (j : ℕ) :
    ⟨0, 0, 2*(4*j+3)+3, 0⟩ [fm]⊢⁺ ⟨0, 0, 2*(7*j+8)+3, 0⟩ := by
  apply step_stepStar_stepPlus
  · show fm ⟨0, 0, 2*(4*j+3)+3, 0⟩ = some ⟨0, 1, 2*(4*j+3)+2, 0⟩; rfl
  step fm; step fm
  apply stepStar_trans (consume_loop (j := 0) (r := 1) (4*j+3))
  simp only [Nat.zero_add]
  step fm
  have h1 := r3_chain (a := 4*j+4) (b := 1) (d := 0) (4*j+4)
  simp only [Nat.zero_add] at h1
  apply stepStar_trans h1
  rw [show 4 * j + 4 + (4 * j + 4) = (7 * j + 7) + (j + 1) from by ring,
      show 1 + 2 * (4 * j + 4) = 1 + 8 * (j + 1) from by ring]
  apply stepStar_trans (b8_iter (a := 7*j+7) (b := 1) (j+1))
  rw [show 7 * j + 7 = (7 * j + 6) + 1 from by ring]
  apply stepStar_trans tail_1
  rw [show 7 * j + 6 + 4 = (7 * j + 8) + 2 from by ring]
  exact phase_c (7*j+8)

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨0, 0, 3, 0⟩) (by execute fm 12)
  apply progress_nonhalt_simple (fm := fm) (A := ℕ)
    (fun n ↦ ⟨0, 0, 2*n+3, 0⟩) 0
  intro n
  rcases Nat.even_or_odd n with ⟨m, hm⟩ | ⟨m, hm⟩ <;>
    rcases Nat.even_or_odd m with ⟨q, hq⟩ | ⟨q, hq⟩
  · -- n = 2*(2*q) = 4*q
    rw [show n = 4 * q from by omega]
    exact ⟨7 * q + 2, main_case0 q⟩
  · -- n = 2*(2*q+1) = 4*q+2
    rw [show n = 4 * q + 2 from by omega]
    exact ⟨7 * q + 4, main_case2 q⟩
  · -- n = 2*m+1, m = 2*q, so n = 4*q+1
    rw [show n = 4 * q + 1 from by omega]
    exact ⟨7 * q + 3, main_case1 q⟩
  · -- n = 2*m+1, m = 2*q+1, so n = 4*q+3
    rw [show n = 4 * q + 3 from by omega]
    exact ⟨7 * q + 8, main_case3 q⟩

end Sz22_2003_unofficial_122
