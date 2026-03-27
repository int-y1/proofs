import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #566: [35/18, 55/2, 4/77, 3/5, 14/11]

Vector representation:
```
-1 -2  1  1  0
-1  0  1  0  1
 2  0  0 -1 -1
 0  1 -1  0  0
 1  0  0  1 -1
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_566

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a+1, b+2, c, d, e⟩ => some ⟨a, b, c+1, d+1, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b, c+1, d, e+1⟩
  | ⟨a, b, c, d+1, e+1⟩ => some ⟨a+2, b, c, d, e⟩
  | ⟨a, b, c+1, d, e⟩ => some ⟨a, b+1, c, d, e⟩
  | ⟨a, b, c, d, e+1⟩ => some ⟨a+1, b, c, d+1, e⟩
  | _ => none

-- R4 chain: convert c to b (a=0, d=0)
theorem r4_chain : ∀ k b, ⟨0, b, c+k, 0, e⟩ [fm]⊢* ⟨0, b+k, c, 0, e⟩ := by
  intro k; induction k with
  | zero => intro b; exists 0
  | succ k ih =>
    intro b; rw [← Nat.add_assoc]
    step fm
    apply stepStar_trans (ih _)
    ring_nf; finish

-- R2-R2-R3 chain with b=0: each round drains 1 from d, adds 1 to e, adds 2 to c
theorem r2r3_chain_0 : ∀ k c e, ⟨2, 0, c, d+k, e⟩ [fm]⊢* ⟨2, 0, c+2*k, d, e+k⟩ := by
  intro k; induction k with
  | zero => intro c e; exists 0
  | succ k ih =>
    intro c e
    rw [show d + (k + 1) = d + k + 1 from by ring]
    step fm; step fm; step fm
    apply stepStar_trans (ih _ _)
    ring_nf; finish

-- R2-R2-R3 chain with b=1
theorem r2r3_chain_1 : ∀ k c e, ⟨2, 1, c, d+k, e⟩ [fm]⊢* ⟨2, 1, c+2*k, d, e+k⟩ := by
  intro k; induction k with
  | zero => intro c e; exists 0
  | succ k ih =>
    intro c e
    rw [show d + (k + 1) = d + k + 1 from by ring]
    step fm; step fm; step fm
    apply stepStar_trans (ih _ _)
    ring_nf; finish

-- R2-R2 final when d=0
theorem r22_final_0 : ⟨2, 0, c, 0, e⟩ [fm]⊢* ⟨0, 0, c+2, 0, e+2⟩ := by
  step fm; step fm; finish

theorem r22_final_1 : ⟨2, 1, c, 0, e⟩ [fm]⊢* ⟨0, 1, c+2, 0, e+2⟩ := by
  step fm; step fm; finish

-- gen_drain with b=0: (2, 0, c, d, e) ->* (0, c+2d+2, 0, 0, d+e+2)
theorem gen_drain_0 : ⟨2, 0, c, d, e⟩ [fm]⊢* ⟨0, c+2*d+2, 0, 0, d+e+2⟩ := by
  rw [show d = 0 + d from by ring]
  apply stepStar_trans (r2r3_chain_0 d c e)
  simp only [Nat.zero_add]
  apply stepStar_trans r22_final_0
  rw [show c + 2 * d + 2 = 0 + (c + 2 * d + 2) from by ring,
      show d + e + 2 = e + d + 2 from by ring]
  exact r4_chain _ _

-- gen_drain with b=1: (2, 1, c, d, e) ->* (0, c+2d+3, 0, 0, d+e+2)
theorem gen_drain_1 : ⟨2, 1, c, d, e⟩ [fm]⊢* ⟨0, c+2*d+3, 0, 0, d+e+2⟩ := by
  rw [show d = 0 + d from by ring]
  apply stepStar_trans (r2r3_chain_1 d c e)
  simp only [Nat.zero_add]
  apply stepStar_trans r22_final_1
  rw [show d + e + 2 = e + d + 2 from by ring]
  have h := @r4_chain 0 (e + d + 2) (c + 2 * d + 2) 1
  simp only [Nat.zero_add] at h
  rw [show 1 + (c + 2 * d + 2) = c + 2 * d + 3 from by ring] at h
  exact h

-- Mix round: R1+R1+R3 consuming 4 from b
theorem mix_round : ⟨2, b+4, c, d, e+1⟩ [fm]⊢* ⟨2, b, c+2, d+1, e⟩ := by
  rw [show b + 4 = b + 2 + 2 from by ring]
  step fm; step fm; step fm; finish

-- Mix chain: K rounds of R1+R1+R3
theorem mix_chain : ∀ k c d e, ⟨2, b+4*k, c, d, e+k⟩ [fm]⊢* ⟨2, b, c+2*k, d+k, e⟩ := by
  intro k; induction k with
  | zero => intro c d e; exists 0
  | succ k ih =>
    intro c d e
    rw [show b + 4 * (k + 1) = (b + 4 * k) + 4 from by ring,
        show e + (k + 1) = e + k + 1 from by ring]
    apply stepStar_trans (@mix_round (b + 4 * k) c d (e + k))
    apply stepStar_trans (ih _ _ _)
    ring_nf; finish

-- Mix remainder 2: R1+R2+R3
theorem mix_rem2 : ⟨2, 2, c, d, e⟩ [fm]⊢* ⟨2, 0, c+2, d, e⟩ := by
  step fm; step fm; step fm; finish

-- Mix remainder 3: R1+R2+R3
theorem mix_rem3 : ⟨2, 3, c, d, e⟩ [fm]⊢* ⟨2, 1, c+2, d, e⟩ := by
  step fm; step fm; step fm; finish

-- Opening 5 steps: (0, 3m+7, 0, 0, m+3) ⊢⁺ (0, 3m+1, 3, 3, m+1)
theorem opening : ⟨0, 3*m+7, 0, 0, m+3⟩ [fm]⊢⁺ ⟨0, 3*m+1, 3, 3, m+1⟩ := by
  rw [show m + 3 = (m + 2) + 1 from by ring]
  step fm  -- R5
  rw [show 3 * m + 7 = (3 * m + 5) + 2 from by ring]
  step fm  -- R1
  rw [show m + 2 = (m + 1) + 1 from by ring]
  step fm  -- R3
  rw [show 3 * m + 5 = (3 * m + 3) + 2 from by ring]
  step fm  -- R1
  rw [show 3 * m + 3 = (3 * m + 1) + 2 from by ring]
  step fm  -- R1
  finish

-- Setup: R3 from (0, B, 3, 3, m+1) -> (2, B, 3, 2, m)
theorem setup_r3 : ⟨0, b, 3, 3, m+1⟩ [fm]⊢* ⟨2, b, 3, 2, m⟩ := by
  rw [show (3 : ℕ) = 2 + 1 from by ring]
  step fm; finish

-- Drain lemmas for m mod 4 cases
-- m ≡ 0: (2, 12j+1, 3, 2, 4j) ->* (0, 12j+10, 0, 0, 4j+4)
theorem drain_mod0 (j : ℕ) : ⟨2, 12*j+1, 3, 2, 4*j⟩ [fm]⊢* ⟨0, 12*j+10, 0, 0, 4*j+4⟩ := by
  rw [show 12 * j + 1 = 1 + 4 * (3 * j) from by ring,
      show 4 * j = j + 3 * j from by ring]
  apply stepStar_trans (mix_chain (3*j) 3 2 j)
  -- Now at (2, 1, 3+2*(3j), 2+3j, j)
  have h := @gen_drain_1 (3 + 2 * (3 * j)) (2 + 3 * j) j
  convert h using 2; all_goals ring_nf

-- m ≡ 1: (2, 12j+4, 3, 2, 4j+1) ->* (0, 12j+13, 0, 0, 4j+5)
theorem drain_mod1 (j : ℕ) : ⟨2, 12*j+4, 3, 2, 4*j+1⟩ [fm]⊢* ⟨0, 12*j+13, 0, 0, 4*j+5⟩ := by
  rw [show 12 * j + 4 = 0 + 4 * (3 * j + 1) from by ring,
      show 4 * j + 1 = j + (3 * j + 1) from by ring]
  apply stepStar_trans (mix_chain (3*j+1) 3 2 j)
  have h := @gen_drain_0 (3 + 2 * (3 * j + 1)) (2 + (3 * j + 1)) j
  convert h using 2; all_goals ring_nf

-- m ≡ 2: (2, 12j+7, 3, 2, 4j+2) ->* (0, 12j+16, 0, 0, 4j+6)
theorem drain_mod2 (j : ℕ) : ⟨2, 12*j+7, 3, 2, 4*j+2⟩ [fm]⊢* ⟨0, 12*j+16, 0, 0, 4*j+6⟩ := by
  rw [show 12 * j + 7 = 3 + 4 * (3 * j + 1) from by ring,
      show 4 * j + 2 = (j + 1) + (3 * j + 1) from by ring]
  apply stepStar_trans (mix_chain (3*j+1) 3 2 (j+1))
  apply stepStar_trans mix_rem3
  have h := @gen_drain_1 (3 + 2 * (3 * j + 1) + 2) (2 + (3 * j + 1)) (j + 1)
  convert h using 2; all_goals ring_nf

-- m ≡ 3: (2, 12j+10, 3, 2, 4j+3) ->* (0, 12j+19, 0, 0, 4j+7)
theorem drain_mod3 (j : ℕ) : ⟨2, 12*j+10, 3, 2, 4*j+3⟩ [fm]⊢* ⟨0, 12*j+19, 0, 0, 4*j+7⟩ := by
  rw [show 12 * j + 10 = 2 + 4 * (3 * j + 2) from by ring,
      show 4 * j + 3 = (j + 1) + (3 * j + 2) from by ring]
  apply stepStar_trans (mix_chain (3*j+2) 3 2 (j+1))
  apply stepStar_trans mix_rem2
  have h := @gen_drain_0 (3 + 2 * (3 * j + 2) + 2) (2 + (3 * j + 2)) (j + 1)
  convert h using 2; all_goals ring_nf

-- Full transition
theorem full_trans (n : ℕ) : ⟨0, 3*n+1, 0, 0, n+1⟩ [fm]⊢⁺ ⟨0, 3*n+4, 0, 0, n+2⟩ := by
  rcases n with _ | _ | m
  · execute fm 8
  · execute fm 18
  · -- n = m+2
    rw [show 3 * (m + 2) + 1 = 3 * m + 7 from by ring,
        show (m + 2) + 1 = m + 3 from by ring]
    apply stepPlus_stepStar_stepPlus opening
    apply stepStar_trans setup_r3
    -- Goal: (2, 3m+1, 3, 2, m) ->* (0, 3(m+2)+4, 0, 0, m+4)
    -- Normalize the target
    rw [show 3 * (m + 2) + 4 = 3 * m + 10 from by ring,
        show m + 2 + 2 = m + 4 from by ring]
    rcases Nat.even_or_odd m with ⟨K, hK⟩ | ⟨K, hK⟩
    · rcases Nat.even_or_odd K with ⟨j, hj⟩ | ⟨j, hj⟩
      · -- m = 4j
        subst hj; subst hK
        have h := drain_mod0 j
        convert h using 2; all_goals ring_nf
      · -- m = 4j+2
        subst hj; subst hK
        have h := drain_mod2 j
        convert h using 2; all_goals ring_nf
    · rcases Nat.even_or_odd K with ⟨j, hj⟩ | ⟨j, hj⟩
      · -- m = 4j+1
        subst hj; subst hK
        have h := drain_mod1 j
        convert h using 2; all_goals ring_nf
      · -- m = 4j+3
        subst hj; subst hK
        have h := drain_mod3 j
        convert h using 2; all_goals ring_nf

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨0, 1, 0, 0, 1⟩) (by execute fm 2)
  apply progress_nonhalt_simple (fm := fm) (A := ℕ)
    (fun n ↦ ⟨0, 3*n+1, 0, 0, n+1⟩) 0
  intro n; exact ⟨n+1, full_trans n⟩
