import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz21_140_unofficial #97: [63/10, 2/33, 121/2, 5/7, 14/11]

Vector representation:
```
-1  2 -1  1  0
 1 -1  0  0 -1
-1  0  0  0  2
 0  0  1 -1  0
 1  0  0  1 -1
```

This Fractran program doesn't halt.

The canonical state is (n+1, 0, 0, 2n, 0) with n ≥ 1, transitioning n → n+1.
The transition decomposes into two halves through intermediate (n+1, 0, 0, 2n+1, 1):

First half:  R3→e, R4→c, R5, R1/R2 chain, R2×2, drain_odd
Second half: R3→e, R4→c, R5, R1/R2 chain, R2×2, drain_even

Author: Claude Opus 4.6
-/

namespace Sz21_140_unofficial_97

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a+1, b, c+1, d, e⟩ => some ⟨a, b+2, c, d+1, e⟩
  | ⟨a, b+1, c, d, e+1⟩ => some ⟨a+1, b, c, d, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b, c, d, e+2⟩
  | ⟨a, b, c, d+1, e⟩ => some ⟨a, b, c+1, d, e⟩
  | ⟨a, b, c, d, e+1⟩ => some ⟨a+1, b, c, d+1, e⟩
  | _ => none

-- R3 repeated: a → e (b=0, c=0)
theorem a_to_e : ⟨a+k, 0, 0, d, e⟩ [fm]⊢* ⟨a, 0, 0, d, e+2*k⟩ := by
  have many_step : ∀ k a e, ⟨a+k, 0, 0, d, e⟩ [fm]⊢* ⟨a, 0, 0, d, e+2*k⟩ := by
    intro k; induction k with
    | zero => intro a e; exists 0
    | succ k ih =>
      intro a e; rw [← Nat.add_assoc]; step fm
      apply stepStar_trans (ih _ _); ring_nf; finish
  exact many_step k a e

-- R4 repeated: d → c (a=0, b=0)
theorem d_to_c : ⟨0, 0, c, d+k, e⟩ [fm]⊢* ⟨0, 0, c+k, d, e⟩ := by
  have many_step : ∀ k c d, ⟨0, 0, c, d+k, e⟩ [fm]⊢* ⟨0, 0, c+k, d, e⟩ := by
    intro k; induction k with
    | zero => intro c d; exists 0
    | succ k ih =>
      intro c d; rw [← Nat.add_assoc]; step fm
      apply stepStar_trans (ih _ _); ring_nf; finish
  exact many_step k c d

-- R1/R2 alternating pairs: (1, b, c+k, d, e+k) →* (1, b+k, c, d+k, e)
theorem r1r2_pairs : ⟨1, b, c+k, d, e+k⟩ [fm]⊢* ⟨1, b+k, c, d+k, e⟩ := by
  have many_step : ∀ k b c d e, ⟨1, b, c+k, d, e+k⟩ [fm]⊢* ⟨1, b+k, c, d+k, e⟩ := by
    intro k; induction k with
    | zero => intro b c d e; exists 0
    | succ k ih =>
      intro b c d e
      rw [show c + (k + 1) = (c + k) + 1 from by ring,
          show e + (k + 1) = (e + k) + 1 from by ring]
      step fm; step fm
      apply stepStar_trans (ih (b+1) c (d+1) e); ring_nf; finish
  exact many_step k b c d e

-- R2 chain: (a, b+k, 0, d, k) →* (a+k, b, 0, d, 0)
theorem r2_chain : ⟨a, b+k, 0, d, k⟩ [fm]⊢* ⟨a+k, b, 0, d, 0⟩ := by
  have many_step : ∀ k a b, ⟨a, b+k, 0, d, k⟩ [fm]⊢* ⟨a+k, b, 0, d, 0⟩ := by
    intro k; induction k with
    | zero => intro a b; exists 0
    | succ k ih =>
      intro a b
      rw [show b + (k + 1) = (b + k) + 1 from by ring]
      step fm
      apply stepStar_trans (ih (a+1) b); ring_nf; finish
  exact many_step k a b

-- Drain even: each R3,R2,R2 round decreases b by 2, increases a by 1
-- (a+1, 2k+2, 0, d, 0) →* (a+k+2, 0, 0, d, 0)
theorem drain_even : ⟨a+1, 2*k+2, 0, d, 0⟩ [fm]⊢* ⟨a+k+2, 0, 0, d, 0⟩ := by
  have many_step : ∀ k a d, ⟨a+1, 2*k+2, 0, d, 0⟩ [fm]⊢* ⟨a+k+2, 0, 0, d, 0⟩ := by
    intro k; induction k with
    | zero =>
      intro a d
      -- State: (a+1, 2, 0, d, 0). R3: → (a, 2, 0, d, 2)
      step fm
      -- R2: (a, 2, 0, d, 2) → (a+1, 1, 0, d, 1)
      step fm
      -- R2: (a+1, 1, 0, d, 1) → (a+2, 0, 0, d, 0)
      step fm; finish
    | succ k ih =>
      intro a d
      rw [show 2 * (k + 1) + 2 = (2 * k + 2) + 2 from by ring]
      step fm
      rw [show (2 * k + 2 + 2 : ℕ) = (2 * k + 3) + 1 from by ring]
      step fm
      rw [show (2 * k + 3 : ℕ) = (2 * k + 2) + 1 from by ring]
      step fm
      apply stepStar_trans (ih (a+1) d); ring_nf; finish
  exact many_step k a d

-- Drain odd: R3,R2,R2 rounds then R3,R2 for the last one
-- (a+1, 2k+1, 0, d, 0) →* (a+k+1, 0, 0, d, 1)
theorem drain_odd : ⟨a+1, 2*k+1, 0, d, 0⟩ [fm]⊢* ⟨a+k+1, 0, 0, d, 1⟩ := by
  have many_step : ∀ k a d, ⟨a+1, 2*k+1, 0, d, 0⟩ [fm]⊢* ⟨a+k+1, 0, 0, d, 1⟩ := by
    intro k; induction k with
    | zero =>
      intro a d; step fm; step fm; finish
    | succ k ih =>
      intro a d
      rw [show 2 * (k + 1) + 1 = (2 * k + 1) + 2 from by ring]
      step fm
      rw [show (2 * k + 1 + 2 : ℕ) = (2 * k + 2) + 1 from by ring]
      step fm
      rw [show (2 * k + 2 : ℕ) = (2 * k + 1) + 1 from by ring]
      step fm
      apply stepStar_trans (ih (a+1) d); ring_nf; finish
  exact many_step k a d

-- Main transition: (n+1, 0, 0, 2n, 0) →⁺ (n+2, 0, 0, 2(n+1), 0)
-- Decomposed via intermediate (n+1, 0, 0, 2n+1, 1)
theorem main_trans (n : ℕ) : ⟨n+2, 0, 0, 2*(n+1), 0⟩ [fm]⊢⁺ ⟨n+3, 0, 0, 2*(n+2), 0⟩ := by
  -- Use the half_step approach:
  -- First half: (n+2, 0, 0, 2(n+1), 0) →* (n+2, 0, 0, 2(n+1)+1, 1)
  -- Second half: (n+2, 0, 0, 2(n+1)+1, 1) →⁺ (n+3, 0, 0, 2(n+2), 0)

  -- === First half ===
  -- R3 x(n+2): → (0, 0, 0, 2n+2, 2n+4)
  apply stepStar_stepPlus_stepPlus (c₂ := ⟨n+2, 0, 0, 2*n+3, 1⟩)
  · apply stepStar_trans (c₂ := ⟨0, 0, 0, 2*n+2, 2*n+4⟩)
    · have h := @a_to_e 0 (n+2) (2*n+2) 0
      simp only [Nat.zero_add] at h
      rw [show 2 * (n + 1) = 2 * n + 2 from by ring]; exact h
    -- R4 x(2n+2): → (0, 0, 2n+2, 0, 2n+4)
    apply stepStar_trans (c₂ := ⟨0, 0, 2*n+2, 0, 2*n+4⟩)
    · have h := @d_to_c (e := 2*n+4) 0 0 (2*n+2)
      simp only [Nat.zero_add] at h; exact h
    -- R5: → (1, 0, 2n+2, 1, 2n+3)
    apply stepStar_trans (c₂ := ⟨1, 0, 2*n+2, 1, 2*n+3⟩)
    · apply step_stepStar
      rw [show (2 * n + 4 : ℕ) = (2 * n + 3) + 1 from by ring]
      show fm ⟨0, 0, 2*n+2, 0, (2*n+3) + 1⟩ = some ⟨1, 0, 2*n+2, 1, 2*n+3⟩
      simp [fm]
    -- R1/R2 x(2n+1) pairs: (1, 0, 1+(2n+1), 1, 2+(2n+1)) →* (1, 2n+1, 1, 2n+2, 2)
    apply stepStar_trans (c₂ := ⟨1, 2*n+1, 1, 2*n+2, 2⟩)
    · have h := @r1r2_pairs 0 1 (2*n+1) 1 2
      simp only [Nat.zero_add] at h
      rw [show 2 * n + 2 = 1 + (2 * n + 1) from by ring,
          show 2 * n + 3 = 2 + (2 * n + 1) from by ring]; exact h
    -- Final R1: (1, 2n+1, 1, 2n+2, 2) → (0, 2n+3, 0, 2n+3, 2)
    apply stepStar_trans (c₂ := ⟨0, 2*n+3, 0, 2*n+3, 2⟩)
    · apply step_stepStar
      show fm ⟨0+1, 2*n+1, 0+1, 2*n+2, 2⟩ = some ⟨0, (2*n+1)+2, 0, (2*n+2)+1, 2⟩
      simp [fm]
    -- R2 x2: (0, 2n+3, 0, 2n+3, 2) →* (2, 2n+1, 0, 2n+3, 0)
    apply stepStar_trans (c₂ := ⟨2, 2*n+1, 0, 2*n+3, 0⟩)
    · have h := @r2_chain 0 (2*n+1) 2 (2*n+3)
      simp only [Nat.zero_add] at h
      rw [show 2 * n + 3 = (2 * n + 1) + 2 from by ring] at h; exact h
    -- drain_odd: (2, 2n+1, 0, 2n+3, 0) →* (n+2, 0, 0, 2n+3, 1)
    -- 2n+1 = 2*n+1; drain_odd with a=1, k=n, d=2n+3
    -- (1+1, 2*n+1, 0, 2n+3, 0) →* (1+n+1, 0, 0, 2n+3, 1)
    have h := @drain_odd 1 n (2*n+3)
    refine stepStar_trans h ?_; ring_nf; finish

  -- === Second half: (n+2, 0, 0, 2n+3, 1) →⁺ (n+3, 0, 0, 2n+4, 0) ===
  -- Start with one R3 step to get stepPlus
  apply step_stepStar_stepPlus (c₂ := ⟨n+1, 0, 0, 2*n+3, 3⟩)
  · show fm ⟨(n+1)+1, 0, 0, 2*n+3, 1⟩ = some ⟨n+1, 0, 0, 2*n+3, 1+2⟩
    simp [fm]
  -- R3 x(n+1): (n+1, 0, 0, 2n+3, 3) →* (0, 0, 0, 2n+3, 3+2*(n+1)) = (0,0,0,2n+3,2n+5)
  apply stepStar_trans (c₂ := ⟨0, 0, 0, 2*n+3, 2*n+5⟩)
  · have h := @a_to_e 0 (n+1) (2*n+3) 3
    simp only [Nat.zero_add] at h
    rw [show 3 + 2 * (n + 1) = 2 * n + 5 from by ring] at h; exact h
  -- R4 x(2n+3): → (0, 0, 2n+3, 0, 2n+5)
  apply stepStar_trans (c₂ := ⟨0, 0, 2*n+3, 0, 2*n+5⟩)
  · have h := @d_to_c (e := 2*n+5) 0 0 (2*n+3)
    simp only [Nat.zero_add] at h; exact h
  -- R5: → (1, 0, 2n+3, 1, 2n+4)
  apply stepStar_trans (c₂ := ⟨1, 0, 2*n+3, 1, 2*n+4⟩)
  · apply step_stepStar
    rw [show (2 * n + 5 : ℕ) = (2 * n + 4) + 1 from by ring]
    show fm ⟨0, 0, 2*n+3, 0, (2*n+4) + 1⟩ = some ⟨1, 0, 2*n+3, 1, 2*n+4⟩
    simp [fm]
  -- R1/R2 x(2n+2) pairs: (1, 0, 1+(2n+2), 1, 2+(2n+2)) →* (1, 2n+2, 1, 2n+3, 2)
  apply stepStar_trans (c₂ := ⟨1, 2*n+2, 1, 2*n+3, 2⟩)
  · have h := @r1r2_pairs 0 1 (2*n+2) 1 2
    simp only [Nat.zero_add] at h
    rw [show 2 * n + 3 = 1 + (2 * n + 2) from by ring,
        show 2 * n + 4 = 2 + (2 * n + 2) from by ring]; exact h
  -- Final R1: (1, 2n+2, 1, 2n+3, 2) → (0, 2n+4, 0, 2n+4, 2)
  apply stepStar_trans (c₂ := ⟨0, 2*n+4, 0, 2*n+4, 2⟩)
  · apply step_stepStar
    show fm ⟨0+1, 2*n+2, 0+1, 2*n+3, 2⟩ = some ⟨0, (2*n+2)+2, 0, (2*n+3)+1, 2⟩
    simp [fm]
  -- R2 x2: (0, 2n+4, 0, 2n+4, 2) →* (2, 2n+2, 0, 2n+4, 0)
  apply stepStar_trans (c₂ := ⟨2, 2*n+2, 0, 2*n+4, 0⟩)
  · have h := @r2_chain 0 (2*n+2) 2 (2*n+4)
    simp only [Nat.zero_add] at h
    rw [show 2 * n + 4 = (2 * n + 2) + 2 from by ring] at h; exact h
  -- drain_even: (2, 2n+2, 0, 2n+4, 0) →* (n+3, 0, 0, 2n+4, 0)
  -- 2n+2 = 2*n+2; drain_even with a=1, k=n, d=2n+4
  -- (1+1, 2*n+2, 0, 2n+4, 0) →* (1+n+2, 0, 0, 2n+4, 0) = (n+3, 0, 0, 2n+4, 0)
  have h := @drain_even 1 n (2*n+4)
  refine stepStar_trans h ?_; ring_nf; finish

theorem nonhalt : ¬halts fm c₀ := by
  -- Bootstrap: c₀ = (1,0,0,0,0) →* (2,0,0,2,0) in 8 steps
  apply stepStar_not_halts_not_halts (c₂ := ⟨2, 0, 0, 2, 0⟩) (by execute fm 8)
  -- (2,0,0,2,0) = ((0+1)+1, 0, 0, 2*(0+1), 0) = C(1) where C(n) = (n+1,0,0,2n,0)
  -- Actually use n starting from 1: C(n) = (n+1, 0, 0, 2*n, 0)
  -- But progress_nonhalt_simple needs the map from parameter to state.
  -- C(1) = (2, 0, 0, 2, 0). main_trans(n) proves C(n+1) →⁺ C(n+2).
  -- So we parameterize by n with C(n) = (n+2, 0, 0, 2*(n+1), 0) starting from n=0.
  apply progress_nonhalt_simple (fm := fm) (A := ℕ)
    (fun n ↦ ⟨n+2, 0, 0, 2*(n+1), 0⟩) 0
  intro n; exact ⟨n+1, main_trans n⟩

end Sz21_140_unofficial_97
