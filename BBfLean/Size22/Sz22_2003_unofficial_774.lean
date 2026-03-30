import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #774: [35/6, 55/2, 4/231, 3/5, 4/11]

Vector representation:
```
-1 -1  1  1  0
-1  0  1  0  1
 2 -1  0 -1 -1
 0  1 -1  0  0
 2  0  0  0 -1
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_774

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a+1, b+1, c, d, e⟩ => some ⟨a, b, c+1, d+1, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b, c+1, d, e+1⟩
  | ⟨a, b+1, c, d+1, e+1⟩ => some ⟨a+2, b, c, d, e⟩
  | ⟨a, b, c+1, d, e⟩ => some ⟨a, b+1, c, d, e⟩
  | ⟨a, b, c, d, e+1⟩ => some ⟨a+2, b, c, d, e⟩
  | _ => none

-- R4 chain: move c to b when a=0, d=0.
theorem c_to_b : ∀ k, ⟨0, b, c + k, 0, e⟩ [fm]⊢* ⟨0, b + k, c, 0, e⟩ := by
  intro k; induction' k with k ih generalizing b
  · exists 0
  · rw [show c + (k + 1) = (c + k) + 1 from by ring]
    step fm
    apply stepStar_trans (ih (b := b + 1))
    ring_nf; finish

-- R3+R1+R1 loop: each cycle b-=3, c+=2, d+=1, e-=1.
theorem r3r1r1_loop : ∀ k, ∀ b c d e,
    ⟨0, b + 3 * k, c, d + 1, e + k⟩ [fm]⊢*
    ⟨0, b, c + 2 * k, d + 1 + k, e⟩ := by
  intro k; induction' k with k ih <;> intro b c d e
  · exists 0
  · rw [show b + 3 * (k + 1) = (b + 3 * k) + 3 from by ring,
        show e + (k + 1) = (e + k) + 1 from by ring,
        show (b + 3 * k) + 3 = (b + 3 * k) + 1 + 1 + 1 from by ring,
        show (e + k) + 1 = (e + k) + 1 from rfl]
    step fm
    step fm
    step fm
    rw [show c + 2 * (k + 1) = (c + 2) + 2 * k from by ring,
        show d + 1 + (k + 1) = (d + 1) + 1 + k from by ring]
    exact ih b (c + 2) (d + 1) e

-- R4+R3+R2+R2 loop: drain d, each cycle c+=1, e+=1.
theorem r4r3r2r2_loop : ∀ k, ∀ c d e,
    ⟨0, 0, c + 1, d + k, e + 1⟩ [fm]⊢*
    ⟨0, 0, c + 1 + k, d, e + 1 + k⟩ := by
  intro k; induction' k with k ih <;> intro c d e
  · exists 0
  · rw [show d + (k + 1) = (d + k) + 1 from by ring,
        show (d + k) + 1 = (d + k) + 1 from rfl]
    step fm
    step fm
    step fm
    step fm
    rw [show c + 1 + (k + 1) = (c + 1) + 1 + k from by ring,
        show e + 1 + (k + 1) = (e + 1) + 1 + k from by ring]
    exact ih (c + 1) d (e + 1)

-- Exit b=1: R3+R2+R2
theorem exit_b1 : ⟨0, 1, c, d + 1, e + 1⟩ [fm]⊢* ⟨0, 0, c + 2, d, e + 2⟩ := by
  step fm
  step fm
  step fm
  ring_nf; finish

-- Exit b=2: R3+R1+R2
theorem exit_b2 : ⟨0, 2, c, d + 1, e + 1⟩ [fm]⊢* ⟨0, 0, c + 2, d + 1, e + 1⟩ := by
  step fm
  step fm
  step fm
  ring_nf; finish

-- Transition for n=0: (0, 1, 0, 0, 1) ⊢⁺ (0, 3, 0, 0, 2)
theorem main_trans_0 : ⟨0, 1, 0, 0, 1⟩ [fm]⊢⁺ ⟨0, 3, 0, 0, 2⟩ := by
  execute fm 10

-- Case n ≡ 2 mod 3, n = 3m+2, m ≥ 0: C(3m+2) ⊢⁺ C(3m+3)
-- (0, 6m+5, 0, 0, 3m+3) ⊢⁺ (0, 6m+7, 0, 0, 3m+4)
theorem main_trans_mod2 (m : ℕ) :
    ⟨0, 6 * m + 5, 0, 0, 3 * m + 3⟩ [fm]⊢⁺ ⟨0, 6 * m + 7, 0, 0, 3 * m + 4⟩ := by
  -- R5+R1+R1: (0, 6m+5, 0, 0, 3m+3) → (0, 6m+3, 2, 2, 3m+2)
  step fm
  step fm
  step fm
  -- R3+R1+R1 loop: 2m+1 cycles
  rw [show (6 * m + 3 : ℕ) = 0 + 3 * (2 * m + 1) from by ring,
      show (3 * m + 2 : ℕ) = (m + 1) + (2 * m + 1) from by ring]
  apply stepStar_trans (r3r1r1_loop (2 * m + 1) 0 2 1 (m + 1))
  -- State: (0, 0, 4m+4, 2m+3, m+1)
  -- R4+R3+R2+R2 loop: 2m+3 cycles
  rw [show 2 + 2 * (2 * m + 1) = (4 * m + 3) + 1 from by ring,
      show 1 + 1 + (2 * m + 1) = 0 + (2 * m + 3) from by ring,
      show (m + 1 : ℕ) = m + 1 from rfl]
  apply stepStar_trans (r4r3r2r2_loop (2 * m + 3) (4 * m + 3) 0 m)
  -- State: (0, 0, 6m+7, 0, 3m+4)
  -- R4 drain
  rw [show 4 * m + 3 + 1 + (2 * m + 3) = 6 * m + 7 from by ring,
      show m + 1 + (2 * m + 3) = 3 * m + 4 from by ring]
  have := c_to_b (6 * m + 7) (b := 0) (c := 0) (e := 3 * m + 4)
  simp only [Nat.zero_add] at this
  exact this

-- Case n ≡ 1 mod 3, n = 3m+1, m ≥ 0: C(3m+1) ⊢⁺ C(3m+2)
-- (0, 6m+3, 0, 0, 3m+2) ⊢⁺ (0, 6m+5, 0, 0, 3m+3)
theorem main_trans_mod1 (m : ℕ) :
    ⟨0, 6 * m + 3, 0, 0, 3 * m + 2⟩ [fm]⊢⁺ ⟨0, 6 * m + 5, 0, 0, 3 * m + 3⟩ := by
  step fm
  step fm
  step fm
  -- State: (0, 6m+1, 2, 2, 3m+1)
  rw [show (6 * m + 1 : ℕ) = 1 + 3 * (2 * m) from by ring,
      show (3 * m + 1 : ℕ) = (m + 1) + 2 * m from by ring]
  apply stepStar_trans (r3r1r1_loop (2 * m) 1 2 1 (m + 1))
  -- State: (0, 1, 4m+2, 2m+2, m+1)
  rw [show 2 + 2 * (2 * m) = 4 * m + 2 from by ring,
      show 1 + 1 + 2 * m = (2 * m + 1) + 1 from by ring,
      show (m + 1 : ℕ) = m + 1 from rfl]
  apply stepStar_trans (exit_b1 (c := 4 * m + 2) (d := 2 * m + 1) (e := m))
  -- State: (0, 0, 4m+4, 2m+1, m+2)
  rw [show 4 * m + 2 + 2 = (4 * m + 3) + 1 from by ring,
      show (2 * m + 1 : ℕ) = 0 + (2 * m + 1) from by ring,
      show m + 2 = (m + 1) + 1 from by ring]
  apply stepStar_trans (r4r3r2r2_loop (2 * m + 1) (4 * m + 3) 0 (m + 1))
  -- State: (0, 0, 6m+5, 0, 3m+3)
  rw [show 4 * m + 3 + 1 + (2 * m + 1) = 6 * m + 5 from by ring,
      show m + 1 + 1 + (2 * m + 1) = 3 * m + 3 from by ring]
  have := c_to_b (6 * m + 5) (b := 0) (c := 0) (e := 3 * m + 3)
  simp only [Nat.zero_add] at this
  exact this

-- Case n ≡ 0 mod 3, n = 3(m+1), m ≥ 0: C(3m+3) ⊢⁺ C(3m+4)
-- (0, 6m+7, 0, 0, 3m+4) ⊢⁺ (0, 6m+9, 0, 0, 3m+5)
theorem main_trans_mod0 (m : ℕ) :
    ⟨0, 6 * m + 7, 0, 0, 3 * m + 4⟩ [fm]⊢⁺ ⟨0, 6 * m + 9, 0, 0, 3 * m + 5⟩ := by
  step fm
  step fm
  step fm
  -- State: (0, 6m+5, 2, 2, 3m+3)
  rw [show (6 * m + 5 : ℕ) = 2 + 3 * (2 * m + 1) from by ring,
      show (3 * m + 3 : ℕ) = (m + 2) + (2 * m + 1) from by ring]
  apply stepStar_trans (r3r1r1_loop (2 * m + 1) 2 2 1 (m + 2))
  -- State: (0, 2, 4m+4, 2m+3, m+2)
  rw [show 2 + 2 * (2 * m + 1) = 4 * m + 4 from by ring,
      show 1 + 1 + (2 * m + 1) = (2 * m + 2) + 1 from by ring,
      show (m + 2 : ℕ) = (m + 1) + 1 from by ring]
  apply stepStar_trans (exit_b2 (c := 4 * m + 4) (d := 2 * m + 2) (e := m + 1))
  -- State: (0, 0, 4m+6, 2m+3, m+2)
  rw [show 4 * m + 4 + 2 = (4 * m + 5) + 1 from by ring,
      show (2 * m + 2) + 1 = 0 + (2 * m + 3) from by ring,
      show (m + 1) + 1 = (m + 1) + 1 from rfl]
  apply stepStar_trans (r4r3r2r2_loop (2 * m + 3) (4 * m + 5) 0 (m + 1))
  -- State: (0, 0, 6m+9, 0, 3m+5)
  rw [show 4 * m + 5 + 1 + (2 * m + 3) = 6 * m + 9 from by ring,
      show m + 1 + 1 + (2 * m + 3) = 3 * m + 5 from by ring]
  have := c_to_b (6 * m + 9) (b := 0) (c := 0) (e := 3 * m + 5)
  simp only [Nat.zero_add] at this
  exact this

-- Main transition: C(n) ⊢⁺ C(n+1) for all n
theorem main_trans (n : ℕ) :
    ⟨0, 2 * n + 1, 0, 0, n + 1⟩ [fm]⊢⁺ ⟨0, 2 * n + 3, 0, 0, n + 2⟩ := by
  rcases n with _ | n
  · exact main_trans_0
  · obtain ⟨m, rfl | rfl | rfl⟩ : ∃ m, n = 3 * m ∨ n = 3 * m + 1 ∨ n = 3 * m + 2 :=
      ⟨n / 3, by omega⟩
    · -- n+1 = 3m+1
      have h1 : (2 * (3 * m + 1) + 1 : ℕ) = 6 * m + 3 := by ring
      have h2 : (3 * m + 1 + 1 : ℕ) = 3 * m + 2 := by ring
      have h3 : (2 * (3 * m + 1) + 3 : ℕ) = 6 * m + 5 := by ring
      have h4 : (3 * m + 1 + 2 : ℕ) = 3 * m + 3 := by ring
      rw [h1, h2, h3, h4]
      exact main_trans_mod1 m
    · -- n+1 = 3m+2
      have h1 : (2 * (3 * m + 2) + 1 : ℕ) = 6 * m + 5 := by ring
      have h2 : (3 * m + 2 + 1 : ℕ) = 3 * m + 3 := by ring
      have h3 : (2 * (3 * m + 2) + 3 : ℕ) = 6 * m + 7 := by ring
      have h4 : (3 * m + 2 + 2 : ℕ) = 3 * m + 4 := by ring
      rw [h1, h2, h3, h4]
      exact main_trans_mod2 m
    · -- n+1 = 3m+3
      have h1 : (2 * (3 * m + 3) + 1 : ℕ) = 6 * m + 7 := by ring
      have h2 : (3 * m + 3 + 1 : ℕ) = 3 * m + 4 := by ring
      have h3 : (2 * (3 * m + 3) + 3 : ℕ) = 6 * m + 9 := by ring
      have h4 : (3 * m + 3 + 2 : ℕ) = 3 * m + 5 := by ring
      rw [h1, h2, h3, h4]
      exact main_trans_mod0 m

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨0, 1, 0, 0, 1⟩) (by execute fm 2)
  apply progress_nonhalt_simple (fm := fm) (A := ℕ)
    (fun n ↦ ⟨0, 2 * n + 1, 0, 0, n + 1⟩) 0
  intro n; exact ⟨n + 1, main_trans n⟩
