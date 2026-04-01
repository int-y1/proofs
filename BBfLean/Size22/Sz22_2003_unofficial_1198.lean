import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #1198: [5/6, 539/2, 2/35, 3/7, 20/33]

Vector representation:
```
-1 -1  1  0  0
-1  0  0  2  1
 1  0 -1 -1  0
 0  1  0 -1  0
 2 -1  1  0 -1
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_1198

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a+1, b+1, c, d, e⟩ => some ⟨a, b, c+1, d, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b, c, d+2, e+1⟩
  | ⟨a, b, c+1, d+1, e⟩ => some ⟨a+1, b, c, d, e⟩
  | ⟨a, b, c, d+1, e⟩ => some ⟨a, b+1, c, d, e⟩
  | ⟨a, b+1, c, d, e+1⟩ => some ⟨a+2, b, c+1, d, e⟩
  | _ => none

-- R4 chain: move d to b (a=0, c=0)
theorem d_to_b : ∀ k, ⟨(0 : ℕ), b, 0, d + k, e⟩ [fm]⊢* ⟨0, b + k, 0, d, e⟩ := by
  intro k; induction' k with k ih generalizing b d
  · exists 0
  · rw [Nat.add_succ d k]; step fm
    apply stepStar_trans (ih (b := b + 1)); ring_nf; finish

-- R5,R1,R1 one round
theorem r5r1r1_one : ⟨(0 : ℕ), b + 3, c, 0, e + 1⟩ [fm]⊢* ⟨0, b, c + 3, 0, e⟩ := by
  step fm; step fm; step fm; ring_nf; finish

-- R5,R1,R1 chain: k rounds
theorem r5r1r1_chain : ∀ k b c e, ⟨(0 : ℕ), b + 3 * k, c, 0, e + k⟩ [fm]⊢* ⟨0, b, c + 3 * k, 0, e⟩ := by
  intro k; induction' k with k ih <;> intro b c e
  · exists 0
  · rw [show b + 3 * (k + 1) = (b + 3) + 3 * k from by ring,
        show e + (k + 1) = (e + 1) + k from by ring]
    apply stepStar_trans (ih (b + 3) c (e + 1))
    exact r5r1r1_one (b := b) (c := c + 3 * k) (e := e)

-- R3,R2 one pair
theorem r3r2_one : ⟨(0 : ℕ), 0, c + 1, d + 1, e⟩ [fm]⊢* ⟨0, 0, c, d + 2, e + 1⟩ := by
  step fm; step fm; finish

-- R3,R2 chain: k pairs
theorem r3r2_chain : ∀ k c d e, ⟨(0 : ℕ), 0, c + k, d + 1, e⟩ [fm]⊢* ⟨0, 0, c, d + 1 + k, e + k⟩ := by
  intro k; induction' k with k ih <;> intro c d e
  · exists 0
  · rw [show c + (k + 1) = (c + k) + 1 from by ring]
    apply stepStar_trans (r3r2_one (c := c + k) (d := d) (e := e))
    rw [show d + 2 = (d + 1) + 1 from by ring]
    apply stepStar_trans (ih c (d + 1) (e + 1))
    ring_nf; finish

-- R5, R1, R2 end for mod 2 case: (0, 2, c, 0, e+1) ->* (0, 0, c+2, 2, e+1)
-- We need to handle c being arbitrary (could be 0 or succ).
-- Do this by proving the 3-step transition directly.
theorem r5r1r2_end : ⟨(0 : ℕ), 2, c, 0, e + 1⟩ [fm]⊢* ⟨0, 0, c + 2, 2, e + 1⟩ := by
  step fm; step fm; step fm; ring_nf; finish

-- R5, R2, R2 end for mod 1 case: (0, 1, c, 0, e+1) ->* (0, 0, c+1, 4, e+2)
theorem r5r2r2_end : ⟨(0 : ℕ), 1, c, 0, e + 1⟩ [fm]⊢* ⟨0, 0, c + 1, 4, e + 2⟩ := by
  step fm; step fm; step fm; ring_nf; finish

-- Full mod2 transition
theorem trans_mod2 (n : ℕ) : ⟨(0 : ℕ), 0, 0, 6 * n + 2, 4 * n ^ 2 + 2 * n + 1⟩ [fm]⊢*
    ⟨0, 0, 0, 6 * n + 4, 4 * n ^ 2 + 6 * n + 3⟩ := by
  -- d_to_b
  rw [show (6 * n + 2 : ℕ) = 0 + (6 * n + 2) from by ring]
  apply stepStar_trans (d_to_b (6 * n + 2) (b := 0) (d := 0) (e := 4 * n ^ 2 + 2 * n + 1))
  -- r5r1r1_chain (2n rounds)
  rw [show (0 + (6 * n + 2) : ℕ) = 2 + 3 * (2 * n) from by ring,
      show 4 * n ^ 2 + 2 * n + 1 = (4 * n ^ 2 + 1) + 2 * n from by ring]
  apply stepStar_trans (r5r1r1_chain (2 * n) 2 0 (4 * n ^ 2 + 1))
  -- Now at (0, 2, 3*(2n), 0, 4n²+1). R5, R1, R2 end.
  rw [show (4 * n ^ 2 + 1 : ℕ) = (4 * n ^ 2) + 1 from by ring]
  apply stepStar_trans (r5r1r2_end (c := 0 + 3 * (2 * n)) (e := 4 * n ^ 2))
  -- Now at (0, 0, 6n+2, 2, 4n²+1). r3r2_chain.
  rw [show (0 + 3 * (2 * n) + 2 : ℕ) = 0 + (6 * n + 2) from by ring,
      show (2 : ℕ) = 1 + 1 from by ring,
      show (4 * n ^ 2 + 1 : ℕ) = 4 * n ^ 2 + 1 from rfl]
  apply stepStar_trans (r3r2_chain (6 * n + 2) 0 1 (4 * n ^ 2 + 1))
  ring_nf; finish

-- Full mod1 transition
theorem trans_mod1 (n : ℕ) : ⟨(0 : ℕ), 0, 0, 6 * n + 4, 4 * n ^ 2 + 6 * n + 3⟩ [fm]⊢*
    ⟨0, 0, 0, 6 * n + 8, 4 * n ^ 2 + 10 * n + 7⟩ := by
  -- d_to_b
  rw [show (6 * n + 4 : ℕ) = 0 + (6 * n + 4) from by ring]
  apply stepStar_trans (d_to_b (6 * n + 4) (b := 0) (d := 0) (e := 4 * n ^ 2 + 6 * n + 3))
  -- r5r1r1_chain (2n+1 rounds)
  rw [show (0 + (6 * n + 4) : ℕ) = 1 + 3 * (2 * n + 1) from by ring,
      show 4 * n ^ 2 + 6 * n + 3 = (4 * n ^ 2 + 4 * n + 2) + (2 * n + 1) from by ring]
  apply stepStar_trans (r5r1r1_chain (2 * n + 1) 1 0 (4 * n ^ 2 + 4 * n + 2))
  -- Now at (0, 1, 3*(2n+1), 0, 4n²+4n+2). R5, R2, R2 end.
  rw [show (4 * n ^ 2 + 4 * n + 2 : ℕ) = (4 * n ^ 2 + 4 * n + 1) + 1 from by ring]
  apply stepStar_trans (r5r2r2_end (c := 0 + 3 * (2 * n + 1)) (e := 4 * n ^ 2 + 4 * n + 1))
  -- Now at (0, 0, 6n+4, 4, 4n²+4n+3). r3r2_chain.
  rw [show (0 + 3 * (2 * n + 1) + 1 : ℕ) = 0 + (6 * n + 4) from by ring,
      show (4 : ℕ) = 3 + 1 from by ring,
      show 4 * n ^ 2 + 4 * n + 1 + 2 = 4 * n ^ 2 + 4 * n + 3 from by ring]
  apply stepStar_trans (r3r2_chain (6 * n + 4) 0 3 (4 * n ^ 2 + 4 * n + 3))
  ring_nf; finish

-- Main transition
theorem main_trans (n : ℕ) : ⟨(0 : ℕ), 0, 0, 6 * n + 2, 4 * n ^ 2 + 2 * n + 1⟩ [fm]⊢⁺
    ⟨0, 0, 0, 6 * (n + 1) + 2, 4 * (n + 1) ^ 2 + 2 * (n + 1) + 1⟩ := by
  rw [show 6 * (n + 1) + 2 = 6 * n + 8 from by ring,
      show 4 * (n + 1) ^ 2 + 2 * (n + 1) + 1 = 4 * n ^ 2 + 10 * n + 7 from by ring]
  exact stepStar_stepPlus (stepStar_trans (trans_mod2 n) (trans_mod1 n))
    (by intro h; have := congr_arg (fun q : Q ↦ q.2.2.2.1) h; simp at this)

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨0, 0, 0, 2, 1⟩)
  · execute fm 1
  · show ¬halts fm ⟨0, 0, 0, 6 * 0 + 2, 4 * 0 ^ 2 + 2 * 0 + 1⟩
    apply progress_nonhalt_simple (fm := fm) (A := ℕ)
      (fun n ↦ ⟨0, 0, 0, 6 * n + 2, 4 * n ^ 2 + 2 * n + 1⟩) 0
    intro n; exact ⟨n + 1, main_trans n⟩
