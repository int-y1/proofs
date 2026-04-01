import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #1578: [7/45, 5/77, 242/5, 3/11, 539/2]

Vector representation:
```
 0 -2 -1  1  0
 0  0  1 -1 -1
 1  0 -1  0  2
 0  1  0  0 -1
-1  0  0  2  1
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_1578

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a, b+2, c+1, d, e⟩ => some ⟨a, b, c, d+1, e⟩
  | ⟨a, b, c, d+1, e+1⟩ => some ⟨a, b, c+1, d, e⟩
  | ⟨a, b, c+1, d, e⟩ => some ⟨a+1, b, c, d, e+2⟩
  | ⟨a, b, c, d, e+1⟩ => some ⟨a, b+1, c, d, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b, c, d+2, e+1⟩
  | _ => none

-- R4 chain: transfer e to b (when c=0, d=0)
theorem e_to_b : ∀ k, ∀ a b, (⟨a, b, 0, 0, k⟩ : Q) [fm]⊢* ⟨a, b + k, 0, 0, 0⟩ := by
  intro k; induction k with
  | zero => intro a b; ring_nf; finish
  | succ k ih =>
    intro a b; step fm
    apply stepStar_trans (ih a (b + 1)); ring_nf; finish

-- R5-R2-R1 chain: each round (a+1, b+2, 0, d, 0) -> (a, b, 0, d+2, 0) in 3 steps
theorem r5r2r1_chain : ∀ k, ∀ a b d, (⟨a + k, b + 2 * k, 0, d, 0⟩ : Q) [fm]⊢* ⟨a, b, 0, d + 2 * k, 0⟩ := by
  intro k; induction k with
  | zero => intro a b d; ring_nf; finish
  | succ k ih =>
    intro a b d
    rw [show a + (k + 1) = (a + k) + 1 from by ring,
        show b + 2 * (k + 1) = (b + 2 * k) + 2 from by ring]
    step fm; step fm; step fm
    apply stepStar_trans (ih a b (d + 2)); ring_nf; finish

-- R5-R2-R3 opening: (a+1, B, 0, d, 0) -> (a+1, B, 0, d+1, 2) for B < 2
theorem r5r2r3_open_b0 : ∀ a d, (⟨a + 1, 0, 0, d, 0⟩ : Q) [fm]⊢* ⟨a + 1, 0, 0, d + 1, 2⟩ := by
  intro a d; step fm; step fm; step fm; ring_nf; finish

theorem r5r2r3_open_b1 : ∀ a d, (⟨a + 1, 1, 0, d, 0⟩ : Q) [fm]⊢* ⟨a + 1, 1, 0, d + 1, 2⟩ := by
  intro a d; step fm; step fm; step fm; ring_nf; finish

-- One round of R2-R2-R3 with b=0: (a, 0, c, d+2, 2) -> (a+1, 0, c+1, d, 2)
theorem r2r2r3_round_b0 : ∀ a c d, (⟨a, 0, c, d + 2, 2⟩ : Q) [fm]⊢* ⟨a + 1, 0, c + 1, d, 2⟩ := by
  intro a c d; step fm; step fm; step fm; ring_nf; finish

-- R2-R2-R3 chain with b=0: (a, 0, c, d+2j, 2) ⊢* (a+j, 0, c+j, d, 2)
theorem r2r2r3_chain_b0 : ∀ j, ∀ a c d, (⟨a, 0, c, d + 2 * j, 2⟩ : Q) [fm]⊢* ⟨a + j, 0, c + j, d, 2⟩ := by
  intro j; induction j with
  | zero => intro a c d; ring_nf; finish
  | succ j ih =>
    intro a c d
    rw [show d + 2 * (j + 1) = (d + 2 * j) + 2 from by ring]
    apply stepStar_trans (r2r2r3_round_b0 a c (d + 2 * j))
    apply stepStar_trans (ih (a + 1) (c + 1) d); ring_nf; finish

-- One round of R2-R2-R3 with b=1: (a, 1, c, d+2, 2) -> (a+1, 1, c+1, d, 2)
theorem r2r2r3_round_b1 : ∀ a c d, (⟨a, 1, c, d + 2, 2⟩ : Q) [fm]⊢* ⟨a + 1, 1, c + 1, d, 2⟩ := by
  intro a c d; step fm; step fm; step fm; ring_nf; finish

-- R2-R2-R3 chain with b=1: (a, 1, c, d+2j, 2) ⊢* (a+j, 1, c+j, d, 2)
theorem r2r2r3_chain_b1 : ∀ j, ∀ a c d, (⟨a, 1, c, d + 2 * j, 2⟩ : Q) [fm]⊢* ⟨a + j, 1, c + j, d, 2⟩ := by
  intro j; induction j with
  | zero => intro a c d; ring_nf; finish
  | succ j ih =>
    intro a c d
    rw [show d + 2 * (j + 1) = (d + 2 * j) + 2 from by ring]
    apply stepStar_trans (r2r2r3_round_b1 a c (d + 2 * j))
    apply stepStar_trans (ih (a + 1) (c + 1) d); ring_nf; finish

-- R2-R3 tail: (a, B, c, 1, 2) -> (a+1, B, c, 0, 3) in 2 steps
theorem r2r3_tail_b0 : ∀ a c, (⟨a, 0, c, 1, 2⟩ : Q) [fm]⊢* ⟨a + 1, 0, c, 0, 3⟩ := by
  intro a c; step fm; step fm; ring_nf; finish

theorem r2r3_tail_b1 : ∀ a c, (⟨a, 1, c, 1, 2⟩ : Q) [fm]⊢* ⟨a + 1, 1, c, 0, 3⟩ := by
  intro a c; step fm; step fm; ring_nf; finish

-- R3 chain with b=0: (a, 0, c+j, 0, e) ⊢* (a+j, 0, c, 0, e+2j)
theorem r3_chain_b0 : ∀ j, ∀ a c e, (⟨a, 0, c + j, 0, e⟩ : Q) [fm]⊢* ⟨a + j, 0, c, 0, e + 2 * j⟩ := by
  intro j; induction j with
  | zero => intro a c e; ring_nf; finish
  | succ j ih =>
    intro a c e
    rw [show c + (j + 1) = (c + j) + 1 from by ring]
    step fm
    apply stepStar_trans (ih (a + 1) c (e + 2)); ring_nf; finish

-- R3 chain with b=1: (a, 1, c+j, 0, e) ⊢* (a+j, 1, c, 0, e+2j)
theorem r3_chain_b1 : ∀ j, ∀ a c e, (⟨a, 1, c + j, 0, e⟩ : Q) [fm]⊢* ⟨a + j, 1, c, 0, e + 2 * j⟩ := by
  intro j; induction j with
  | zero => intro a c e; ring_nf; finish
  | succ j ih =>
    intro a c e
    rw [show c + (j + 1) = (c + j) + 1 from by ring]
    step fm
    apply stepStar_trans (ih (a + 1) c (e + 2)); ring_nf; finish

-- Main transition: A(k) ⊢⁺ A(k+1)
-- A(k) = (3k²+3k+2, 0, 0, 0, 6k+3)
theorem main_trans (k : ℕ) :
    (⟨3 * k ^ 2 + 3 * k + 2, 0, 0, 0, 6 * k + 3⟩ : Q) [fm]⊢⁺
    ⟨3 * (k + 1) ^ 2 + 3 * (k + 1) + 2, 0, 0, 0, 6 * (k + 1) + 3⟩ := by
  -- Step 1: R4 chain, e -> b
  have h1 : (⟨3 * k ^ 2 + 3 * k + 2, 0, 0, 0, 6 * k + 3⟩ : Q) [fm]⊢*
      ⟨3 * k ^ 2 + 3 * k + 2, 6 * k + 3, 0, 0, 0⟩ := by
    have := e_to_b (6 * k + 3) (3 * k ^ 2 + 3 * k + 2) 0
    rw [show 0 + (6 * k + 3) = 6 * k + 3 from by ring] at this; exact this
  -- Step 2: R5-R2-R1 chain (3k+1 rounds), b = 6k+3 = 1 + 2*(3k+1)
  have h2 : (⟨3 * k ^ 2 + 3 * k + 2, 6 * k + 3, 0, 0, 0⟩ : Q) [fm]⊢*
      ⟨3 * k ^ 2 + 1, 1, 0, 6 * k + 2, 0⟩ := by
    rw [show 3 * k ^ 2 + 3 * k + 2 = (3 * k ^ 2 + 1) + (3 * k + 1) from by ring,
        show 6 * k + 3 = 1 + 2 * (3 * k + 1) from by ring]
    have := r5r2r1_chain (3 * k + 1) (3 * k ^ 2 + 1) 1 0
    rw [show 0 + 2 * (3 * k + 1) = 6 * k + 2 from by ring] at this; exact this
  -- Step 3: R5-R2-R3 opening with b=1
  have h3 : (⟨3 * k ^ 2 + 1, 1, 0, 6 * k + 2, 0⟩ : Q) [fm]⊢*
      ⟨3 * k ^ 2 + 1, 1, 0, 6 * k + 3, 2⟩ := by
    rw [show 3 * k ^ 2 + 1 = (3 * k ^ 2) + 1 from by ring]
    have := r5r2r3_open_b1 (3 * k ^ 2) (6 * k + 2)
    rw [show 6 * k + 2 + 1 = 6 * k + 3 from by ring] at this; exact this
  -- Step 4: R2-R2-R3 chain with b=1 (3k+1 rounds), d = 6k+3 = 1 + 2*(3k+1)
  have h4 : (⟨3 * k ^ 2 + 1, 1, 0, 6 * k + 3, 2⟩ : Q) [fm]⊢*
      ⟨3 * k ^ 2 + 3 * k + 2, 1, 3 * k + 1, 1, 2⟩ := by
    rw [show 6 * k + 3 = 1 + 2 * (3 * k + 1) from by ring]
    have := r2r2r3_chain_b1 (3 * k + 1) (3 * k ^ 2 + 1) 0 1
    rw [show 3 * k ^ 2 + 1 + (3 * k + 1) = 3 * k ^ 2 + 3 * k + 2 from by ring,
        show 0 + (3 * k + 1) = 3 * k + 1 from by ring] at this; exact this
  -- Step 5: R2-R3 tail with b=1
  have h5 : (⟨3 * k ^ 2 + 3 * k + 2, 1, 3 * k + 1, 1, 2⟩ : Q) [fm]⊢*
      ⟨3 * k ^ 2 + 3 * k + 3, 1, 3 * k + 1, 0, 3⟩ := by
    exact r2r3_tail_b1 (3 * k ^ 2 + 3 * k + 2) (3 * k + 1)
  -- Step 6: R3 chain with b=1 (3k+1 steps)
  have h6 : (⟨3 * k ^ 2 + 3 * k + 3, 1, 3 * k + 1, 0, 3⟩ : Q) [fm]⊢*
      ⟨3 * k ^ 2 + 6 * k + 4, 1, 0, 0, 6 * k + 5⟩ := by
    rw [show 3 * k + 1 = 0 + (3 * k + 1) from by ring]
    have := r3_chain_b1 (3 * k + 1) (3 * k ^ 2 + 3 * k + 3) 0 3
    rw [show 3 * k ^ 2 + 3 * k + 3 + (3 * k + 1) = 3 * k ^ 2 + 6 * k + 4 from by ring,
        show 3 + 2 * (3 * k + 1) = 6 * k + 5 from by ring] at this; exact this
  -- Step 7: R4 chain (6k+5 steps)
  have h7 : (⟨3 * k ^ 2 + 6 * k + 4, 1, 0, 0, 6 * k + 5⟩ : Q) [fm]⊢*
      ⟨3 * k ^ 2 + 6 * k + 4, 6 * k + 6, 0, 0, 0⟩ := by
    have := e_to_b (6 * k + 5) (3 * k ^ 2 + 6 * k + 4) 1
    rw [show 1 + (6 * k + 5) = 6 * k + 6 from by ring] at this; exact this
  -- Step 8: R5-R2-R1 chain (3k+3 rounds), b = 6k+6 = 0 + 2*(3k+3)
  have h8 : (⟨3 * k ^ 2 + 6 * k + 4, 6 * k + 6, 0, 0, 0⟩ : Q) [fm]⊢*
      ⟨3 * k ^ 2 + 3 * k + 1, 0, 0, 6 * k + 6, 0⟩ := by
    have := r5r2r1_chain (3 * k + 3) (3 * k ^ 2 + 3 * k + 1) 0 0
    rw [show (3 * k ^ 2 + 3 * k + 1) + (3 * k + 3) = 3 * k ^ 2 + 6 * k + 4 from by ring,
        show 0 + 2 * (3 * k + 3) = 6 * k + 6 from by ring] at this; exact this
  -- Step 9: R5-R2-R3 opening with b=0
  have h9 : (⟨3 * k ^ 2 + 3 * k + 1, 0, 0, 6 * k + 6, 0⟩ : Q) [fm]⊢*
      ⟨3 * k ^ 2 + 3 * k + 1, 0, 0, 6 * k + 7, 2⟩ := by
    rw [show 3 * k ^ 2 + 3 * k + 1 = (3 * k ^ 2 + 3 * k) + 1 from by ring]
    have := r5r2r3_open_b0 (3 * k ^ 2 + 3 * k) (6 * k + 6)
    rw [show 6 * k + 6 + 1 = 6 * k + 7 from by ring] at this; exact this
  -- Step 10: R2-R2-R3 chain with b=0 (3k+3 rounds), d = 6k+7 = 1 + 2*(3k+3)
  have h10 : (⟨3 * k ^ 2 + 3 * k + 1, 0, 0, 6 * k + 7, 2⟩ : Q) [fm]⊢*
      ⟨3 * k ^ 2 + 6 * k + 4, 0, 3 * k + 3, 1, 2⟩ := by
    rw [show 6 * k + 7 = 1 + 2 * (3 * k + 3) from by ring]
    have := r2r2r3_chain_b0 (3 * k + 3) (3 * k ^ 2 + 3 * k + 1) 0 1
    rw [show 3 * k ^ 2 + 3 * k + 1 + (3 * k + 3) = 3 * k ^ 2 + 6 * k + 4 from by ring,
        show 0 + (3 * k + 3) = 3 * k + 3 from by ring] at this; exact this
  -- Step 11: R2-R3 tail with b=0
  have h11 : (⟨3 * k ^ 2 + 6 * k + 4, 0, 3 * k + 3, 1, 2⟩ : Q) [fm]⊢*
      ⟨3 * k ^ 2 + 6 * k + 5, 0, 3 * k + 3, 0, 3⟩ := by
    exact r2r3_tail_b0 (3 * k ^ 2 + 6 * k + 4) (3 * k + 3)
  -- Step 12: R3 chain with b=0 (3k+3 steps)
  have h12 : (⟨3 * k ^ 2 + 6 * k + 5, 0, 3 * k + 3, 0, 3⟩ : Q) [fm]⊢*
      ⟨3 * k ^ 2 + 9 * k + 8, 0, 0, 0, 6 * k + 9⟩ := by
    rw [show 3 * k + 3 = 0 + (3 * k + 3) from by ring]
    have := r3_chain_b0 (3 * k + 3) (3 * k ^ 2 + 6 * k + 5) 0 3
    rw [show 3 * k ^ 2 + 6 * k + 5 + (3 * k + 3) = 3 * k ^ 2 + 9 * k + 8 from by ring,
        show 3 + 2 * (3 * k + 3) = 6 * k + 9 from by ring] at this; exact this
  -- Compose all phases; use first R4 step as the ⊢⁺ witness
  have h1plus : (⟨3 * k ^ 2 + 3 * k + 2, 0, 0, 0, 6 * k + 3⟩ : Q) [fm]⊢⁺
      ⟨3 * k ^ 2 + 3 * k + 2, 6 * k + 3, 0, 0, 0⟩ := by
    rw [show 6 * k + 3 = (6 * k + 2) + 1 from by ring]
    step fm
    have := e_to_b (6 * k + 2) (3 * k ^ 2 + 3 * k + 2) 1
    rw [show 1 + (6 * k + 2) = 6 * k + 3 from by ring] at this; exact this
  apply stepPlus_stepStar_stepPlus h1plus
  apply stepStar_trans h2
  apply stepStar_trans h3
  apply stepStar_trans h4
  apply stepStar_trans h5
  apply stepStar_trans h6
  apply stepStar_trans h7
  apply stepStar_trans h8
  apply stepStar_trans h9
  apply stepStar_trans h10
  apply stepStar_trans h11
  have := h12
  rw [show 3 * k ^ 2 + 9 * k + 8 = 3 * (k + 1) ^ 2 + 3 * (k + 1) + 2 from by ring,
      show 6 * k + 9 = 6 * (k + 1) + 3 from by ring] at this; exact this

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨3 * 0 ^ 2 + 3 * 0 + 2, 0, 0, 0, 6 * 0 + 3⟩)
  · execute fm 5
  apply progress_nonhalt_simple (fm := fm) (A := ℕ)
    (fun k ↦ ⟨3 * k ^ 2 + 3 * k + 2, 0, 0, 0, 6 * k + 3⟩) 0
  intro k; exact ⟨k + 1, main_trans k⟩

end Sz22_2003_unofficial_1578
