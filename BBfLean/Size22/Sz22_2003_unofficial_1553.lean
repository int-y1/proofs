import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #1553: [7/30, 8/21, 55/2, 3/11, 21/5]

Vector representation:
```
-1 -1 -1  1  0
 3 -1  0 -1  0
-1  0  1  0  1
 0  1  0  0 -1
 0  1 -1  1  0
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_1553

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a+1, b+1, c+1, d, e⟩ => some ⟨a, b, c, d+1, e⟩
  | ⟨a, b+1, c, d+1, e⟩ => some ⟨a+3, b, c, d, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b, c+1, d, e+1⟩
  | ⟨a, b, c, d, e+1⟩ => some ⟨a, b+1, c, d, e⟩
  | ⟨a, b, c+1, d, e⟩ => some ⟨a, b+1, c, d+1, e⟩
  | _ => none

-- R4 chain (helper): transfer e to b when a=0, d=0
private theorem e_to_b_aux : ∀ k b c, ⟨(0 : ℕ), b, c, 0, k⟩ [fm]⊢* ⟨0, b + k, c, 0, 0⟩ := by
  intro k; induction' k with k ih <;> intro b c
  · ring_nf; finish
  · -- (0, b, c, 0, k+1): a=0, b=b, c=c, d=0, e=k+1
    -- R1 needs a>=1: no. R2 needs d>=1: no. R3 needs a>=1: no. R4 fires (e=k+1>=1).
    rcases b with _ | b
    · -- b = 0
      step fm; apply stepStar_trans (ih 1 c); ring_nf; finish
    · -- b = b+1
      step fm; apply stepStar_trans (ih (b + 2) c); ring_nf; finish

theorem e_to_b (k c : ℕ) : ⟨(0 : ℕ), 0, c, 0, k⟩ [fm]⊢* ⟨0, k, c, 0, 0⟩ := by
  have := e_to_b_aux k 0 c; simp at this; exact this

-- R3 chain: drain a, building c and e
theorem r3_drain : ∀ k, ∀ c d e,
    ⟨k, (0 : ℕ), c, d, e⟩ [fm]⊢* ⟨0, 0, c + k, d, e + k⟩ := by
  intro k; induction' k with k ih <;> intro c d e
  · exists 0
  · step fm; apply stepStar_trans (ih (c + 1) d (e + 1)); ring_nf; finish

-- R1×3 + R2 chain: each round drains b by 4 and c by 3, builds d by 2
theorem r1r2_chain : ∀ k, ∀ b c d,
    ⟨(3 : ℕ), b + 4 * k, c + 3 * k, d, 0⟩ [fm]⊢* ⟨3, b, c, d + 2 * k, 0⟩ := by
  intro k; induction' k with k ih <;> intro b c d
  · ring_nf; finish
  · rw [show b + 4 * (k + 1) = (b + 4 * k) + 3 + 1 from by ring,
        show c + 3 * (k + 1) = (c + 3 * k) + 2 + 1 from by ring,
        show d + 2 * (k + 1) = (d + 2) + 2 * k from by ring]
    step fm; step fm; step fm; step fm
    apply stepStar_trans (ih b c (d + 2)); ring_nf; finish

-- d-drain: from (3, 0, c, d+k, e), each round does R3×3, R4, R2
theorem d_drain : ∀ k, ∀ c d e,
    ⟨(3 : ℕ), 0, c, d + k, e⟩ [fm]⊢* ⟨3, 0, c + 3 * k, d, e + 2 * k⟩ := by
  intro k; induction' k with k ih <;> intro c d e
  · ring_nf; finish
  · rw [show d + (k + 1) = (d + k) + 1 from by ring,
        show c + 3 * (k + 1) = (c + 3) + 3 * k from by ring,
        show e + 2 * (k + 1) = (e + 2) + 2 * k from by ring]
    step fm; step fm; step fm; step fm; step fm
    apply stepStar_trans (ih (c + 3) d (e + 2)); ring_nf; finish

-- Case e mod 4 = 0: E = 4j+7 (E mod 4 = 3), b_rem = 3
theorem main_case0 (n j : ℕ) :
    ⟨(0 : ℕ), 0, n + 4 * j + 9, 0, 4 * j + 7⟩ [fm]⊢⁺
    ⟨0, 0, n + 7 * j + 19, 0, 4 * j + 13⟩ := by
  have h1 : ⟨(0 : ℕ), 0, n + 4 * j + 9, 0, 4 * j + 7⟩ [fm]⊢*
      ⟨0, 4 * j + 7, n + 4 * j + 9, 0, 0⟩ :=
    e_to_b (4 * j + 7) (n + 4 * j + 9)
  have h2 : ⟨(0 : ℕ), 4 * j + 7, n + 4 * j + 9, 0, 0⟩ [fm]⊢⁺
      ⟨3, 4 * j + 7, n + 4 * j + 8, 0, 0⟩ := by
    rw [show n + 4 * j + 9 = (n + 4 * j + 8) + 1 from by ring,
        show 4 * j + 7 = (4 * j + 6) + 1 from by ring]
    step fm
    rw [show (4 * j + 6) + 1 + 1 = (4 * j + 7) + 1 from by ring]
    step fm; finish
  have h3 : ⟨(3 : ℕ), 4 * j + 7, n + 4 * j + 8, 0, 0⟩ [fm]⊢*
      ⟨3, 3, n + j + 5, 2 * j + 2, 0⟩ := by
    have := r1r2_chain (j + 1) 3 (n + j + 5) 0
    rw [show 3 + 4 * (j + 1) = 4 * j + 7 from by ring,
        show (n + j + 5) + 3 * (j + 1) = n + 4 * j + 8 from by ring,
        show 0 + 2 * (j + 1) = 2 * j + 2 from by ring] at this; exact this
  have h4 : ⟨(3 : ℕ), 3, n + j + 5, 2 * j + 2, 0⟩ [fm]⊢*
      ⟨3, 0, n + j + 1, 2 * j + 5, 0⟩ := by
    rw [show n + j + 5 = (n + j + 2) + 2 + 1 from by ring,
        show (3 : ℕ) = 2 + 1 from by ring]
    step fm; step fm; step fm
    rw [show n + j + 2 = (n + j + 1) + 1 from by ring]
    step fm
    rw [show 2 * j + 6 = (2 * j + 5) + 1 from by ring]
    step fm; finish
  have h5 : ⟨(3 : ℕ), 0, n + j + 1, 2 * j + 5, 0⟩ [fm]⊢*
      ⟨3, 0, n + 7 * j + 16, 0, 4 * j + 10⟩ := by
    have := d_drain (2 * j + 5) (n + j + 1) 0 0
    rw [show 0 + (2 * j + 5) = 2 * j + 5 from by ring,
        show (n + j + 1) + 3 * (2 * j + 5) = n + 7 * j + 16 from by ring,
        show 0 + 2 * (2 * j + 5) = 4 * j + 10 from by ring] at this; exact this
  have h6 : ⟨(3 : ℕ), 0, n + 7 * j + 16, 0, 4 * j + 10⟩ [fm]⊢*
      ⟨0, 0, n + 7 * j + 19, 0, 4 * j + 13⟩ := by
    have := r3_drain 3 (n + 7 * j + 16) 0 (4 * j + 10)
    rw [show (n + 7 * j + 16) + 3 = n + 7 * j + 19 from by ring,
        show (4 * j + 10) + 3 = 4 * j + 13 from by ring] at this; exact this
  exact stepStar_stepPlus_stepPlus h1
    (stepPlus_stepStar_stepPlus h2
      (stepStar_trans h3 (stepStar_trans h4 (stepStar_trans h5 h6))))

-- Case e mod 4 = 1: E = 4j+8 (E mod 4 = 0), b_rem = 0
theorem main_case1 (n j : ℕ) :
    ⟨(0 : ℕ), 0, n + 4 * j + 10, 0, 4 * j + 8⟩ [fm]⊢⁺
    ⟨0, 0, n + 7 * j + 18, 0, 4 * j + 11⟩ := by
  have h1 : ⟨(0 : ℕ), 0, n + 4 * j + 10, 0, 4 * j + 8⟩ [fm]⊢*
      ⟨0, 4 * j + 8, n + 4 * j + 10, 0, 0⟩ :=
    e_to_b (4 * j + 8) (n + 4 * j + 10)
  have h2 : ⟨(0 : ℕ), 4 * j + 8, n + 4 * j + 10, 0, 0⟩ [fm]⊢⁺
      ⟨3, 4 * j + 8, n + 4 * j + 9, 0, 0⟩ := by
    rw [show n + 4 * j + 10 = (n + 4 * j + 9) + 1 from by ring,
        show 4 * j + 8 = (4 * j + 7) + 1 from by ring]
    step fm
    rw [show (4 * j + 7) + 1 + 1 = (4 * j + 8) + 1 from by ring]
    step fm; finish
  have h3 : ⟨(3 : ℕ), 4 * j + 8, n + 4 * j + 9, 0, 0⟩ [fm]⊢*
      ⟨3, 0, n + j + 3, 2 * j + 4, 0⟩ := by
    have := r1r2_chain (j + 2) 0 (n + j + 3) 0
    rw [show 0 + 4 * (j + 2) = 4 * j + 8 from by ring,
        show (n + j + 3) + 3 * (j + 2) = n + 4 * j + 9 from by ring,
        show 0 + 2 * (j + 2) = 2 * j + 4 from by ring] at this; exact this
  have h4 : ⟨(3 : ℕ), 0, n + j + 3, 2 * j + 4, 0⟩ [fm]⊢*
      ⟨3, 0, n + 7 * j + 15, 0, 4 * j + 8⟩ := by
    have := d_drain (2 * j + 4) (n + j + 3) 0 0
    rw [show 0 + (2 * j + 4) = 2 * j + 4 from by ring,
        show (n + j + 3) + 3 * (2 * j + 4) = n + 7 * j + 15 from by ring,
        show 0 + 2 * (2 * j + 4) = 4 * j + 8 from by ring] at this; exact this
  have h5 : ⟨(3 : ℕ), 0, n + 7 * j + 15, 0, 4 * j + 8⟩ [fm]⊢*
      ⟨0, 0, n + 7 * j + 18, 0, 4 * j + 11⟩ := by
    have := r3_drain 3 (n + 7 * j + 15) 0 (4 * j + 8)
    rw [show (n + 7 * j + 15) + 3 = n + 7 * j + 18 from by ring,
        show (4 * j + 8) + 3 = 4 * j + 11 from by ring] at this; exact this
  exact stepStar_stepPlus_stepPlus h1
    (stepPlus_stepStar_stepPlus h2
      (stepStar_trans h3 (stepStar_trans h4 h5)))

-- Case e mod 4 = 2: E = 4j+9 (E mod 4 = 1), b_rem = 1
theorem main_case2 (n j : ℕ) :
    ⟨(0 : ℕ), 0, n + 4 * j + 11, 0, 4 * j + 9⟩ [fm]⊢⁺
    ⟨0, 0, n + 7 * j + 20, 0, 4 * j + 12⟩ := by
  have h1 : ⟨(0 : ℕ), 0, n + 4 * j + 11, 0, 4 * j + 9⟩ [fm]⊢*
      ⟨0, 4 * j + 9, n + 4 * j + 11, 0, 0⟩ :=
    e_to_b (4 * j + 9) (n + 4 * j + 11)
  have h2 : ⟨(0 : ℕ), 4 * j + 9, n + 4 * j + 11, 0, 0⟩ [fm]⊢⁺
      ⟨3, 4 * j + 9, n + 4 * j + 10, 0, 0⟩ := by
    rw [show n + 4 * j + 11 = (n + 4 * j + 10) + 1 from by ring,
        show 4 * j + 9 = (4 * j + 8) + 1 from by ring]
    step fm
    rw [show (4 * j + 8) + 1 + 1 = (4 * j + 9) + 1 from by ring]
    step fm; finish
  have h3 : ⟨(3 : ℕ), 4 * j + 9, n + 4 * j + 10, 0, 0⟩ [fm]⊢*
      ⟨3, 1, n + j + 4, 2 * j + 4, 0⟩ := by
    have := r1r2_chain (j + 2) 1 (n + j + 4) 0
    rw [show 1 + 4 * (j + 2) = 4 * j + 9 from by ring,
        show (n + j + 4) + 3 * (j + 2) = n + 4 * j + 10 from by ring,
        show 0 + 2 * (j + 2) = 2 * j + 4 from by ring] at this; exact this
  have h4 : ⟨(3 : ℕ), 1, n + j + 4, 2 * j + 4, 0⟩ [fm]⊢*
      ⟨3, 0, n + j + 5, 2 * j + 4, 1⟩ := by
    rw [show n + j + 4 = (n + j + 3) + 1 from by ring,
        show (1 : ℕ) = 0 + 1 from by ring]
    step fm; step fm; step fm
    rw [show 2 * j + 5 = (2 * j + 4) + 1 from by ring]
    step fm; step fm; finish
  have h5 : ⟨(3 : ℕ), 0, n + j + 5, 2 * j + 4, 1⟩ [fm]⊢*
      ⟨3, 0, n + 7 * j + 17, 0, 4 * j + 9⟩ := by
    have := d_drain (2 * j + 4) (n + j + 5) 0 1
    rw [show 0 + (2 * j + 4) = 2 * j + 4 from by ring,
        show (n + j + 5) + 3 * (2 * j + 4) = n + 7 * j + 17 from by ring,
        show 1 + 2 * (2 * j + 4) = 4 * j + 9 from by ring] at this; exact this
  have h6 : ⟨(3 : ℕ), 0, n + 7 * j + 17, 0, 4 * j + 9⟩ [fm]⊢*
      ⟨0, 0, n + 7 * j + 20, 0, 4 * j + 12⟩ := by
    have := r3_drain 3 (n + 7 * j + 17) 0 (4 * j + 9)
    rw [show (n + 7 * j + 17) + 3 = n + 7 * j + 20 from by ring,
        show (4 * j + 9) + 3 = 4 * j + 12 from by ring] at this; exact this
  exact stepStar_stepPlus_stepPlus h1
    (stepPlus_stepStar_stepPlus h2
      (stepStar_trans h3 (stepStar_trans h4 (stepStar_trans h5 h6))))

-- Case e mod 4 = 3: E = 4j+10 (E mod 4 = 2), b_rem = 2
theorem main_case3 (n j : ℕ) :
    ⟨(0 : ℕ), 0, n + 4 * j + 12, 0, 4 * j + 10⟩ [fm]⊢⁺
    ⟨0, 0, n + 7 * j + 22, 0, 4 * j + 13⟩ := by
  have h1 : ⟨(0 : ℕ), 0, n + 4 * j + 12, 0, 4 * j + 10⟩ [fm]⊢*
      ⟨0, 4 * j + 10, n + 4 * j + 12, 0, 0⟩ :=
    e_to_b (4 * j + 10) (n + 4 * j + 12)
  have h2 : ⟨(0 : ℕ), 4 * j + 10, n + 4 * j + 12, 0, 0⟩ [fm]⊢⁺
      ⟨3, 4 * j + 10, n + 4 * j + 11, 0, 0⟩ := by
    rw [show n + 4 * j + 12 = (n + 4 * j + 11) + 1 from by ring,
        show 4 * j + 10 = (4 * j + 9) + 1 from by ring]
    step fm
    rw [show (4 * j + 9) + 1 + 1 = (4 * j + 10) + 1 from by ring]
    step fm; finish
  have h3 : ⟨(3 : ℕ), 4 * j + 10, n + 4 * j + 11, 0, 0⟩ [fm]⊢*
      ⟨3, 2, n + j + 5, 2 * j + 4, 0⟩ := by
    have := r1r2_chain (j + 2) 2 (n + j + 5) 0
    rw [show 2 + 4 * (j + 2) = 4 * j + 10 from by ring,
        show (n + j + 5) + 3 * (j + 2) = n + 4 * j + 11 from by ring,
        show 0 + 2 * (j + 2) = 2 * j + 4 from by ring] at this; exact this
  have h4 : ⟨(3 : ℕ), 2, n + j + 5, 2 * j + 4, 0⟩ [fm]⊢*
      ⟨3, 0, n + j + 4, 2 * j + 5, 0⟩ := by
    rw [show n + j + 5 = (n + j + 3) + 1 + 1 from by ring,
        show (2 : ℕ) = 1 + 1 from by ring]
    step fm; step fm; step fm
    rw [show 2 * j + 6 = (2 * j + 5) + 1 from by ring]
    step fm; step fm; finish
  have h5 : ⟨(3 : ℕ), 0, n + j + 4, 2 * j + 5, 0⟩ [fm]⊢*
      ⟨3, 0, n + 7 * j + 19, 0, 4 * j + 10⟩ := by
    have := d_drain (2 * j + 5) (n + j + 4) 0 0
    rw [show 0 + (2 * j + 5) = 2 * j + 5 from by ring,
        show (n + j + 4) + 3 * (2 * j + 5) = n + 7 * j + 19 from by ring,
        show 0 + 2 * (2 * j + 5) = 4 * j + 10 from by ring] at this; exact this
  have h6 : ⟨(3 : ℕ), 0, n + 7 * j + 19, 0, 4 * j + 10⟩ [fm]⊢*
      ⟨0, 0, n + 7 * j + 22, 0, 4 * j + 13⟩ := by
    have := r3_drain 3 (n + 7 * j + 19) 0 (4 * j + 10)
    rw [show (n + 7 * j + 19) + 3 = n + 7 * j + 22 from by ring,
        show (4 * j + 10) + 3 = 4 * j + 13 from by ring] at this; exact this
  exact stepStar_stepPlus_stepPlus h1
    (stepPlus_stepStar_stepPlus h2
      (stepStar_trans h3 (stepStar_trans h4 (stepStar_trans h5 h6))))

-- Combined transition via mod 4 dispatch
theorem main_trans (n e : ℕ) :
    ∃ n' e', ⟨(0 : ℕ), 0, n + e + 9, 0, e + 7⟩ [fm]⊢⁺ ⟨0, 0, n' + e' + 9, 0, e' + 7⟩ := by
  rcases Nat.even_or_odd e with ⟨k, hk⟩ | ⟨k, hk⟩
  · rcases Nat.even_or_odd k with ⟨j, hj⟩ | ⟨j, hj⟩
    · -- e = 4j
      subst hj; subst hk
      refine ⟨n + 3 * j + 4, 4 * j + 6, ?_⟩
      rw [show (n + 3 * j + 4) + (4 * j + 6) + 9 = n + 7 * j + 19 from by ring,
          show (4 * j + 6) + 7 = 4 * j + 13 from by ring,
          show n + (j + j + (j + j)) + 9 = n + 4 * j + 9 from by omega,
          show j + j + (j + j) + 7 = 4 * j + 7 from by omega]
      exact main_case0 n j
    · -- e = 4j+2
      subst hj; subst hk
      refine ⟨n + 3 * j + 6, 4 * j + 5, ?_⟩
      rw [show (n + 3 * j + 6) + (4 * j + 5) + 9 = n + 7 * j + 20 from by ring,
          show (4 * j + 5) + 7 = 4 * j + 12 from by ring,
          show n + (2 * j + 1 + (2 * j + 1)) + 9 = n + 4 * j + 11 from by omega,
          show 2 * j + 1 + (2 * j + 1) + 7 = 4 * j + 9 from by omega]
      exact main_case2 n j
  · rcases Nat.even_or_odd k with ⟨j, hj⟩ | ⟨j, hj⟩
    · -- e = 4j+1
      subst hj; subst hk
      refine ⟨n + 3 * j + 5, 4 * j + 4, ?_⟩
      rw [show (n + 3 * j + 5) + (4 * j + 4) + 9 = n + 7 * j + 18 from by ring,
          show (4 * j + 4) + 7 = 4 * j + 11 from by ring,
          show n + (2 * (j + j) + 1) + 9 = n + 4 * j + 10 from by omega,
          show 2 * (j + j) + 1 + 7 = 4 * j + 8 from by omega]
      exact main_case1 n j
    · -- e = 4j+3
      subst hj; subst hk
      refine ⟨n + 3 * j + 7, 4 * j + 6, ?_⟩
      rw [show (n + 3 * j + 7) + (4 * j + 6) + 9 = n + 7 * j + 22 from by ring,
          show (4 * j + 6) + 7 = 4 * j + 13 from by ring,
          show n + (2 * (2 * j + 1) + 1) + 9 = n + 4 * j + 12 from by omega,
          show 2 * (2 * j + 1) + 1 + 7 = 4 * j + 10 from by omega]
      exact main_case3 n j

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨0, 0, 9, 0, 7⟩)
  · execute fm 35
  apply progress_nonhalt (fm := fm)
    (P := fun q ↦ ∃ n e, q = ⟨0, 0, n + e + 9, 0, e + 7⟩)
  · intro q ⟨n, e, hq⟩
    subst hq
    obtain ⟨n', e', h⟩ := main_trans n e
    exact ⟨⟨0, 0, n' + e' + 9, 0, e' + 7⟩, ⟨n', e', rfl⟩, h⟩
  · exact ⟨0, 0, rfl⟩

end Sz22_2003_unofficial_1553
