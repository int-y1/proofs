import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #119: [1/405, 14/15, 63/2, 5/7, 3/5]

Vector representation:
```
 0 -4 -1  0
 1 -1 -1  1
-1  2  0  1
 0  0  1 -1
 0  1 -1  0
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_119

def Q := ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a, b+4, c+1, d⟩ => some ⟨a, b, c, d⟩
  | ⟨a, b+1, c+1, d⟩ => some ⟨a+1, b, c, d+1⟩
  | ⟨a+1, b, c, d⟩ => some ⟨a, b+2, c, d+1⟩
  | ⟨a, b, c, d+1⟩ => some ⟨a, b, c+1, d⟩
  | ⟨a, b, c+1, d⟩ => some ⟨a, b+1, c, d⟩
  | _ => none

-- R4: d to c transfer
theorem d_to_c : ∀ k c, ⟨0, 0, c, k⟩ [fm]⊢* ⟨0, 0, c + k, 0⟩ := by
  intro k; induction' k with k ih <;> intro c
  · exists 0
  · step fm; apply stepStar_trans (ih _); ring_nf; finish

-- R3: a to b transfer (c=0)
theorem a_to_b : ∀ k b d, ⟨k, b, 0, d⟩ [fm]⊢* ⟨0, b + 2 * k, 0, d + k⟩ := by
  intro k; induction' k with k ih <;> intro b d
  · exists 0
  · step fm; apply stepStar_trans (ih _ _); ring_nf; finish

-- Climb step: R3,R2,R2 triple
theorem climb_step : ∀ k c d, ⟨k + 1, 0, c + 2, d⟩ [fm]⊢* ⟨k + 2, 0, c, d + 3⟩ := by
  intro k c d; step fm; step fm; step fm; finish

-- Generalized climb: (a+1, 0, c+2k, d) ->* (a+k+1, 0, c, d+3k)
theorem climb_gen : ∀ k a c d,
    ⟨a + 1, 0, c + 2 * k, d⟩ [fm]⊢* ⟨a + k + 1, 0, c, d + 3 * k⟩ := by
  intro k; induction' k with k ih <;> intro a c d
  · exists 0
  · rw [show c + 2 * (k + 1) = (c + 2 * k) + 2 from by ring]
    apply stepStar_trans (climb_step a (c + 2 * k) d)
    apply stepStar_trans (ih (a + 1) c (d + 3))
    ring_nf; finish

-- Specialized climb for our use: (1, 0, 2m, 1) ->* (m+1, 0, 0, 3m+1)
theorem climb_even' (m : ℕ) : ⟨1, 0, 2 * m, 1⟩ [fm]⊢* ⟨m + 1, 0, 0, 3 * m + 1⟩ := by
  have h := climb_gen m 0 0 1
  rw [Nat.zero_add, Nat.zero_add, show 0 + m + 1 = m + 1 from by omega,
      show 1 + 3 * m = 3 * m + 1 from by omega] at h
  exact h

-- Specialized climb for our use: (1, 0, 2m+1, 1) ->* (m+1, 0, 1, 3m+1)
theorem climb_odd' (m : ℕ) : ⟨1, 0, 2 * m + 1, 1⟩ [fm]⊢* ⟨m + 1, 0, 1, 3 * m + 1⟩ := by
  have h := climb_gen m 0 1 1
  rw [Nat.zero_add, show 1 + 2 * m = 2 * m + 1 from by omega,
      show 0 + m + 1 = m + 1 from by omega,
      show 1 + 3 * m = 3 * m + 1 from by omega] at h
  exact h

-- R4,R1: drain 4 from b
theorem drain_step : ∀ b d, ⟨0, b + 4, 0, d + 1⟩ [fm]⊢* ⟨0, b, 0, d⟩ := by
  intro b d; step fm; step fm; finish

-- Drain chain
theorem drain : ∀ k b d, ⟨0, b + 4 * k, 0, d + k⟩ [fm]⊢* ⟨0, b, 0, d⟩ := by
  intro k; induction' k with k ih <;> intro b d
  · exists 0
  · rw [show b + 4 * (k + 1) = (b + 4 * k) + 4 from by ring,
        show d + (k + 1) = (d + k) + 1 from by ring]
    apply stepStar_trans (drain_step _ _); exact ih _ _

-- Drain residual b=1
theorem drain_1 : ∀ d, ⟨0, 1, 0, d + 1⟩ [fm]⊢* ⟨0, 0, 0, d + 3⟩ := by
  intro d; step fm; step fm; step fm; step fm; step fm; step fm
  step fm; step fm; step fm; step fm; step fm; finish

-- Drain residual b=2
theorem drain_2 : ∀ d, ⟨0, 2, 0, d + 1⟩ [fm]⊢* ⟨0, 0, 0, d + 2⟩ := by
  intro d; step fm; step fm; step fm; step fm
  step fm; step fm; step fm; step fm; finish

-- Drain residual b=3
theorem drain_3 : ∀ d, ⟨0, 3, 0, d + 1⟩ [fm]⊢* ⟨0, 0, 0, d + 1⟩ := by
  intro d; step fm; step fm; step fm; step fm; step fm; finish

-- Full even path: (0, 0, 2m+2, 0) ->* (0, 0, 0, 4m+2)
-- R5: (0,1,2m+1,0). R2: (1,0,2m,1). climb: (m+1,0,0,3m+1). a_to_b: (0,2m+2,0,4m+2). drain+d_to_c.
-- We prove the full path to (0, 2m+2, 0, 4m+2) first.
theorem full_climb_even (m : ℕ) :
    ⟨0, 0, 2 * m + 2, 0⟩ [fm]⊢* ⟨0, 2 * m + 2, 0, 4 * m + 2⟩ := by
  step fm; step fm
  apply stepStar_trans (climb_even' m)
  apply stepStar_trans (a_to_b (m + 1) 0 (3 * m + 1))
  ring_nf; finish

-- Full odd path: (0, 0, 2m+3, 0) ->* (0, 2m+3, 0, 4m+4)
-- R5: (0,1,2m+2,0). R2: (1,0,2m+1,1). climb: (m+1,0,1,3m+1).
-- R3: (m,2,1,3m+2). R2: (m+1,1,0,3m+3). a_to_b: (0,2m+3,0,4m+4).
theorem full_climb_odd (m : ℕ) :
    ⟨0, 0, 2 * m + 3, 0⟩ [fm]⊢* ⟨0, 2 * m + 3, 0, 4 * m + 4⟩ := by
  step fm; step fm
  apply stepStar_trans (climb_odd' m)
  step fm; step fm
  rw [show 3 * m + 1 + 1 + 1 = 3 * m + 3 from by ring]
  apply stepStar_trans (a_to_b (m + 1) 1 (3 * m + 3))
  ring_nf; finish

-- Helper for inequality proofs
private theorem ne_of_third_ne {a₁ b₁ c₁ d₁ a₂ b₂ c₂ d₂ : ℕ}
    (h : c₁ ≠ c₂) : (a₁, b₁, c₁, d₁) ≠ (a₂, b₂, c₂, d₂) := by
  intro heq; exact h (congrArg (fun x : Q => x.2.2.1) heq)

-- c ≡ 0 mod 4, c = 4(q+1)
theorem main_mod0 (q : ℕ) : ⟨0, 0, 4 * q + 4, 0⟩ [fm]⊢⁺ ⟨0, 0, 7 * q + 5, 0⟩ := by
  rw [show 4 * q + 4 = 2 * (2 * q + 1) + 2 from by ring]
  apply stepStar_stepPlus
  · apply stepStar_trans (full_climb_even (2 * q + 1))
    rw [show 2 * (2 * q + 1) + 2 = 0 + 4 * (q + 1) from by ring,
        show 4 * (2 * q + 1) + 2 = (7 * q + 5) + (q + 1) from by ring]
    apply stepStar_trans (drain (q + 1) 0 (7 * q + 5))
    have h := d_to_c (7 * q + 5) 0; rw [Nat.zero_add] at h; exact h
  · exact ne_of_third_ne (by omega)

-- c ≡ 1 mod 4, c = 4q+5
theorem main_mod1 (q : ℕ) : ⟨0, 0, 4 * q + 5, 0⟩ [fm]⊢⁺ ⟨0, 0, 7 * q + 9, 0⟩ := by
  rw [show 4 * q + 5 = 2 * (2 * q + 1) + 3 from by ring]
  apply stepStar_stepPlus
  · apply stepStar_trans (full_climb_odd (2 * q + 1))
    rw [show 2 * (2 * q + 1) + 3 = 1 + 4 * (q + 1) from by ring,
        show 4 * (2 * q + 1) + 4 = (7 * q + 7) + (q + 1) from by ring]
    apply stepStar_trans (drain (q + 1) 1 (7 * q + 7))
    rw [show 7 * q + 7 = (7 * q + 6) + 1 from by ring]
    apply stepStar_trans (drain_1 (7 * q + 6))
    rw [show 7 * q + 6 + 3 = 7 * q + 9 from by ring]
    have h := d_to_c (7 * q + 9) 0; rw [Nat.zero_add] at h; exact h
  · exact ne_of_third_ne (by omega)

-- c ≡ 2 mod 4, c = 4q+2
theorem main_mod2 (q : ℕ) : ⟨0, 0, 4 * q + 2, 0⟩ [fm]⊢⁺ ⟨0, 0, 7 * q + 3, 0⟩ := by
  rw [show 4 * q + 2 = 2 * (2 * q) + 2 from by ring]
  apply stepStar_stepPlus
  · apply stepStar_trans (full_climb_even (2 * q))
    rw [show 2 * (2 * q) + 2 = 2 + 4 * q from by ring,
        show 4 * (2 * q) + 2 = (7 * q + 2) + q from by ring]
    apply stepStar_trans (drain q 2 (7 * q + 2))
    rw [show 7 * q + 2 = (7 * q + 1) + 1 from by ring]
    apply stepStar_trans (drain_2 (7 * q + 1))
    rw [show 7 * q + 1 + 2 = 7 * q + 3 from by ring]
    have h := d_to_c (7 * q + 3) 0; rw [Nat.zero_add] at h; exact h
  · exact ne_of_third_ne (by omega)

-- c ≡ 3 mod 4, c = 4q+3
theorem main_mod3 (q : ℕ) : ⟨0, 0, 4 * q + 3, 0⟩ [fm]⊢⁺ ⟨0, 0, 7 * q + 4, 0⟩ := by
  rw [show 4 * q + 3 = 2 * (2 * q) + 3 from by ring]
  apply stepStar_stepPlus
  · apply stepStar_trans (full_climb_odd (2 * q))
    rw [show 2 * (2 * q) + 3 = 3 + 4 * q from by ring,
        show 4 * (2 * q) + 4 = (7 * q + 4) + q from by ring]
    apply stepStar_trans (drain q 3 (7 * q + 4))
    rw [show 7 * q + 4 = (7 * q + 3) + 1 from by ring]
    apply stepStar_trans (drain_3 (7 * q + 3))
    rw [show 7 * q + 3 + 1 = 7 * q + 4 from by ring]
    have h := d_to_c (7 * q + 4) 0; rw [Nat.zero_add] at h; exact h
  · exact ne_of_third_ne (by omega)

private theorem main_step (n : ℕ) :
    ∃ n', ⟨0, 0, n + 2, 0⟩ [fm]⊢⁺ ⟨0, 0, n' + 2, 0⟩ := by
  rcases n with _ | _ | n
  · exists 1; execute fm 14
  · exists 2; execute fm 14
  · rcases Nat.even_or_odd n with ⟨k, hk⟩ | ⟨k, hk⟩
    · rcases Nat.even_or_odd k with ⟨j, hj⟩ | ⟨j, hj⟩
      · subst hk; subst hj; refine ⟨7 * j + 3, ?_⟩
        rw [show j + j + (j + j) + 4 = 4 * j + 4 from by omega,
            show 7 * j + 3 + 2 = 7 * j + 5 from by omega]
        exact main_mod0 j
      · subst hk; subst hj; refine ⟨7 * j + 8, ?_⟩
        rw [show 2 * j + 1 + (2 * j + 1) + 4 = 4 * (j + 1) + 2 from by omega,
            show 7 * j + 8 + 2 = 7 * (j + 1) + 3 from by omega]
        exact main_mod2 (j + 1)
    · rcases Nat.even_or_odd k with ⟨j, hj⟩ | ⟨j, hj⟩
      · subst hk; subst hj; refine ⟨7 * j + 7, ?_⟩
        rw [show 2 * (j + j) + 1 + 4 = 4 * j + 5 from by omega,
            show 7 * j + 7 + 2 = 7 * j + 9 from by omega]
        exact main_mod1 j
      · subst hk; subst hj; refine ⟨7 * j + 9, ?_⟩
        rw [show 2 * (2 * j + 1) + 1 + 4 = 4 * (j + 1) + 3 from by omega,
            show 7 * j + 9 + 2 = 7 * (j + 1) + 4 from by omega]
        exact main_mod3 (j + 1)

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨0, 0, 2, 0⟩) (by execute fm 11)
  apply progress_nonhalt_simple (fm := fm) (A := ℕ) (fun n ↦ ⟨0, 0, n + 2, 0⟩) 0
  exact main_step

end Sz22_2003_unofficial_119
