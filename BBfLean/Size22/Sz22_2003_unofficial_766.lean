import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #766: [35/6, 4/605, 121/2, 3/7, 14/11]

Vector representation:
```
-1 -1  1  1  0
 2  0 -1  0 -2
-1  0  0  0  2
 0  1  0 -1  0
 1  0  0  1 -1
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_766

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a+1, b+1, c, d, e⟩ => some ⟨a, b, c+1, d+1, e⟩
  | ⟨a, b, c+1, d, e+2⟩ => some ⟨a+2, b, c, d, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b, c, d, e+2⟩
  | ⟨a, b, c, d+1, e⟩ => some ⟨a, b+1, c, d, e⟩
  | ⟨a, b, c, d, e+1⟩ => some ⟨a+1, b, c, d+1, e⟩
  | _ => none

theorem d_to_b : ∀ k b d e, ⟨0, b, 0, d + k, e⟩ [fm]⊢* ⟨0, b + k, 0, d, e⟩ := by
  intro k; induction' k with k ih <;> intro b d e
  · exists 0
  · rw [show d + (k + 1) = (d + k) + 1 from by ring]
    step fm
    apply stepStar_trans (ih (b + 1) d e)
    ring_nf; finish

theorem a_to_e : ∀ k a d e, ⟨a + k, 0, 0, d, e⟩ [fm]⊢* ⟨a, 0, 0, d, e + 2 * k⟩ := by
  intro k; induction' k with k ih <;> intro a d e
  · exists 0
  · rw [show a + (k + 1) = (a + k) + 1 from by ring]
    step fm
    apply stepStar_trans (ih a d (e + 2))
    ring_nf; finish

theorem r1r1r2_chain : ∀ k b j d, ⟨2, b + 2 * k, j, d, b + 2 * k⟩ [fm]⊢*
    ⟨2, b, j + k, d + 2 * k, b⟩ := by
  intro k; induction' k with k ih <;> intro b j d
  · exists 0
  · rw [show b + 2 * (k + 1) = b + 2 * k + 1 + 1 from by ring]
    step fm; step fm
    rw [show j + 1 + 1 = (j + 1) + 1 from by ring,
        show b + 2 * k + 1 + 1 = b + 2 * k + 2 from by ring]
    step fm
    apply stepStar_trans (ih b (j + 1) (d + 2))
    ring_nf; finish

theorem r3r2_chain_e0 : ∀ k a c d, ⟨a + 1, 0, c + k, d, 0⟩ [fm]⊢*
    ⟨a + k + 1, 0, c, d, 0⟩ := by
  intro k; induction' k with k ih <;> intro a c d
  · exists 0
  · rw [show c + (k + 1) = (c + k) + 1 from by ring]
    step fm; step fm
    apply stepStar_trans (ih (a + 1) c d)
    ring_nf; finish

theorem r3r2_chain_e1 : ∀ k a c d, ⟨a + 1, 0, c + k, d, 1⟩ [fm]⊢*
    ⟨a + k + 1, 0, c, d, 1⟩ := by
  intro k; induction' k with k ih <;> intro a c d
  · exists 0
  · rw [show c + (k + 1) = (c + k) + 1 from by ring]
    step fm; step fm
    apply stepStar_trans (ih (a + 1) c d)
    ring_nf; finish

-- R4+R5+R1+R2 combined: (0,0,0,n+1,e) →* (2,n,0,2,n) when e = n + 3
theorem phase_1_2_3_odd (m : ℕ) :
    ⟨0, 0, 0, 2 * m + 1, 2 * m + 3⟩ [fm]⊢* ⟨2, 2 * m, 0, 2, 2 * m⟩ := by
  apply stepStar_trans
  · rw [show (2 * m + 1 : ℕ) = 0 + (2 * m + 1) from by ring]
    exact d_to_b (2 * m + 1) 0 0 (2 * m + 3)
  rw [show 0 + (2 * m + 1) = 2 * m + 1 from by ring]
  step fm; step fm; step fm; finish

theorem phase_1_2_3_even (m : ℕ) :
    ⟨0, 0, 0, 2 * m + 2, 2 * m + 4⟩ [fm]⊢* ⟨2, 2 * m + 1, 0, 2, 2 * m + 1⟩ := by
  apply stepStar_trans
  · rw [show (2 * m + 2 : ℕ) = 0 + (2 * m + 2) from by ring]
    exact d_to_b (2 * m + 2) 0 0 (2 * m + 4)
  rw [show 0 + (2 * m + 2) = 2 * m + 2 from by ring]
  step fm; step fm; step fm; finish

-- Phases 4-6 for odd n: (2, 2m, 0, 2, 2m) →* (0, 0, 0, 2m+2, 2m+4)
theorem phase_4_5_6_odd (m : ℕ) :
    ⟨2, 2 * m, 0, 2, 2 * m⟩ [fm]⊢* ⟨0, 0, 0, 2 * m + 2, 2 * m + 4⟩ := by
  -- R1R1R2 chain
  apply stepStar_trans
  · rw [show (2 * m : ℕ) = 0 + 2 * m from by ring]
    exact r1r1r2_chain m 0 0 2
  -- Now at (2, 0, m, 2+2m, 0)
  apply stepStar_trans
  · rw [show (0 : ℕ) + m = 0 + m from by ring,
        show (2 : ℕ) = 1 + 1 from by ring]
    exact r3r2_chain_e0 m 1 0 (2 + 2 * m)
  -- Now at (m+2, 0, 0, 2+2m, 0)
  apply stepStar_trans
  · rw [show 1 + m + 1 = 0 + (m + 2) from by ring]
    exact a_to_e (m + 2) 0 (2 + 2 * m) 0
  ring_nf; finish

-- R1 step: (2, 1, m, d, 1) → (1, 0, m+1, d+1, 1)
theorem r1_step (m d : ℕ) :
    ⟨2, 1, m, d, 1⟩ [fm]⊢* ⟨1, 0, m + 1, d + 1, 1⟩ := by
  step fm; finish

-- Phases 4-6 for even n: (2, 2m+1, 0, 2, 2m+1) →* (0, 0, 0, 2m+3, 2m+5)
theorem phase_4_5_6_even (m : ℕ) :
    ⟨2, 2 * m + 1, 0, 2, 2 * m + 1⟩ [fm]⊢* ⟨0, 0, 0, 2 * m + 3, 2 * m + 5⟩ := by
  -- R1R1R2 chain m rounds
  apply stepStar_trans
  · rw [show (2 * m + 1 : ℕ) = 1 + 2 * m from by ring]
    exact r1r1r2_chain m 1 0 2
  -- Now at (2, 1, m, 2+2m, 1)
  rw [show (0 : ℕ) + m = m from by ring]
  -- R1: (2, 1, m, 2+2m, 1) → (1, 0, m+1, 2+2m+1, 1)
  apply stepStar_trans (r1_step m (2 + 2 * m))
  -- R3+R2 chain (m+1) rounds
  apply stepStar_trans
  · rw [show m + 1 = 0 + (m + 1) from by ring,
        show (1 : ℕ) = 0 + 1 from by ring]
    exact r3r2_chain_e1 (m + 1) 0 0 (2 + 2 * m + 1)
  -- R3 drain
  apply stepStar_trans
  · rw [show 0 + (m + 1) + 1 = 0 + (m + 2) from by ring]
    exact a_to_e (m + 2) 0 (2 + 2 * m + 1) 1
  ring_nf; finish

theorem path_odd (m : ℕ) :
    ⟨0, 0, 0, 2 * m + 1, 2 * m + 3⟩ [fm]⊢* ⟨0, 0, 0, 2 * m + 2, 2 * m + 4⟩ :=
  stepStar_trans (phase_1_2_3_odd m) (phase_4_5_6_odd m)

theorem path_even (m : ℕ) :
    ⟨0, 0, 0, 2 * m + 2, 2 * m + 4⟩ [fm]⊢* ⟨0, 0, 0, 2 * m + 3, 2 * m + 5⟩ :=
  stepStar_trans (phase_1_2_3_even m) (phase_4_5_6_even m)

theorem main_trans (n : ℕ) :
    ⟨0, 0, 0, n, n + 2⟩ [fm]⊢⁺ ⟨0, 0, 0, n + 1, n + 3⟩ := by
  rcases Nat.even_or_odd n with ⟨m, hm⟩ | ⟨m, hm⟩
  · rw [show m + m = 2 * m from by ring] at hm; subst hm
    rcases m with _ | m
    · execute fm 2
    · show ⟨0, 0, 0, 2 * m + 2, 2 * m + 2 + 2⟩ [fm]⊢⁺
          ⟨0, 0, 0, 2 * m + 2 + 1, 2 * m + 2 + 3⟩
      rw [show 2 * m + 2 + 2 = 2 * m + 4 from by ring,
          show 2 * m + 2 + 1 = 2 * m + 3 from by ring,
          show 2 * m + 2 + 3 = 2 * m + 5 from by ring]
      exact stepStar_stepPlus (path_even m) (by simp [Q])
  · subst hm
    rw [show 2 * m + 1 + 2 = 2 * m + 3 from by ring,
        show 2 * m + 1 + 1 = 2 * m + 2 from by ring,
        show 2 * m + 1 + 3 = 2 * m + 4 from by ring]
    exact stepStar_stepPlus (path_odd m) (by simp [Q])

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨0, 0, 0, 0, 2⟩)
  · execute fm 1
  · apply progress_nonhalt_simple (fm := fm) (A := ℕ)
      (fun n ↦ ⟨0, 0, 0, n, n + 2⟩) 0
    intro n; exists n + 1; exact main_trans n

end Sz22_2003_unofficial_766
