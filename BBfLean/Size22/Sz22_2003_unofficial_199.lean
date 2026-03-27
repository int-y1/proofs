import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #199: [1/6, 3/35, 275/3, 4/55, 147/2]

Vector representation:
```
-1 -1  0  0  0
 0  1 -1 -1  0
 0 -1  2  0  1
 2  0 -1  0 -1
-1  1  0  2  0
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_199

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a+1, b+1, c, d, e⟩ => some ⟨a, b, c, d, e⟩
  | ⟨a, b, c+1, d+1, e⟩ => some ⟨a, b+1, c, d, e⟩
  | ⟨a, b+1, c, d, e⟩ => some ⟨a, b, c+2, d, e+1⟩
  | ⟨a, b, c+1, d, e+1⟩ => some ⟨a+2, b, c, d, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b+1, c, d+2, e⟩
  | _ => none

-- 3 steps (R3, R2, R2): consume 2 from d, add 1 to b and e.
theorem step3 : ∀ b d e, ⟨0, b+1, 0, d+2, e⟩ [fm]⊢* ⟨0, b+2, 0, d, e+1⟩ := by
  intro b d e; step fm; step fm; step fm; ring_nf; finish

-- Repeat step3 k times.
theorem step3_repeat : ∀ k b d e,
    ⟨0, b+1, 0, d+2*k, e⟩ [fm]⊢* ⟨0, b+k+1, 0, d, e+k⟩ := by
  intro k; induction' k with k ih <;> intro b d e
  · exists 0
  rw [show d + 2 * (k + 1) = (d + 2 * k) + 2 from by ring]
  apply stepStar_trans (step3 b (d + 2 * k) e)
  apply stepStar_trans (ih (b + 1) d (e + 1))
  ring_nf; finish

-- R3 drain: convert b to c and e when d=0.
theorem r3_drain : ∀ k c e, ⟨0, k, c, 0, e⟩ [fm]⊢* ⟨0, 0, c+2*k, 0, e+k⟩ := by
  intro k; induction' k with k ih <;> intro c e
  · exists 0
  show ⟨0, k+1, c, 0, e⟩ [fm]⊢* _
  step fm
  apply stepStar_trans (ih (c + 2) (e + 1))
  ring_nf; finish

-- R4 chain: convert c and e to a.
theorem r4_chain : ∀ k a c, ⟨a, 0, c+k, 0, k⟩ [fm]⊢* ⟨a+2*k, 0, c, 0, 0⟩ := by
  intro k; induction' k with k ih <;> intro a c
  · exists 0
  show ⟨a, 0, c + k + 1, 0, k + 1⟩ [fm]⊢* _
  step fm
  apply stepStar_trans (ih (a + 2) c)
  ring_nf; finish

-- R5/R1 drain: convert odd a to d.
theorem r5r1_drain : ∀ k d, ⟨2*k+1, 0, 0, d, 0⟩ [fm]⊢* ⟨0, 1, 0, d+2*k+2, 0⟩ := by
  intro k; induction' k with k ih <;> intro d
  · step fm; ring_nf; finish
  rw [show 2 * (k + 1) + 1 = (2 * k + 1) + 2 from by ring]
  step fm; step fm
  apply stepStar_trans (ih (d + 2))
  ring_nf; finish

-- Phase 1 even: (0, 1, 0, 2m, 0) ->* (0, 0, 2m+2, 0, 2m+1)
theorem phase1_even (m : ℕ) : ⟨0, 1, 0, 2*m, 0⟩ [fm]⊢* ⟨0, 0, 2*m+2, 0, 2*m+1⟩ := by
  apply stepStar_trans
  · have h := step3_repeat m 0 0 0
    simp only [Nat.zero_add] at h; exact h
  apply stepStar_trans (r3_drain (m + 1) 0 m)
  ring_nf; finish

-- Phase 1 odd: (0, 1, 0, 2m+1, 0) ->* (0, 0, 2m+3, 0, 2m+2)
theorem phase1_odd (m : ℕ) : ⟨0, 1, 0, 2*m+1, 0⟩ [fm]⊢* ⟨0, 0, 2*m+3, 0, 2*m+2⟩ := by
  apply stepStar_trans
  · have h := step3_repeat m 0 1 0
    simp only [Nat.zero_add] at h
    rw [show 1 + 2 * m = 2 * m + 1 from by ring] at h
    exact h
  step fm; step fm
  apply stepStar_trans (r3_drain (m + 1) 1 (m + 1))
  ring_nf; finish

-- Phase 2: R4 chain
theorem phase2 (d : ℕ) : ⟨0, 0, d+2, 0, d+1⟩ [fm]⊢* ⟨2*d+2, 0, 1, 0, 0⟩ := by
  have h := r4_chain (d + 1) 0 1
  simp only [Nat.zero_add] at h
  apply stepStar_trans
  · rw [show d + 2 = 1 + (d + 1) from by ring]; exact h
  ring_nf; finish

-- Phase 3 for d >= 1: 4 steps then r5r1_drain
theorem phase3_succ (d : ℕ) : ⟨2*d+4, 0, 1, 0, 0⟩ [fm]⊢* ⟨0, 1, 0, 2*d+3, 0⟩ := by
  rw [show 2 * d + 4 = (2 * d + 1) + 3 from by ring]
  step fm; step fm; step fm; step fm
  apply stepStar_trans (r5r1_drain d 1)
  ring_nf; finish

-- Main star for odd d: (0, 1, 0, 2m+1, 0) ->* (0, 1, 0, 4m+3, 0)
theorem main_star_odd (m : ℕ) : ⟨0, 1, 0, 2*m+1, 0⟩ [fm]⊢* ⟨0, 1, 0, 4*m+3, 0⟩ := by
  apply stepStar_trans (phase1_odd m)
  apply stepStar_trans (phase2 (2 * m + 1))
  rw [show 2 * (2 * m + 1) + 2 = 2 * (2 * m) + 4 from by ring]
  apply stepStar_trans (phase3_succ (2 * m))
  ring_nf; finish

-- Main star for even d >= 2: (0, 1, 0, 2(m+1), 0) ->* (0, 1, 0, 4m+5, 0)
theorem main_star_even_succ (m : ℕ) : ⟨0, 1, 0, 2*(m+1), 0⟩ [fm]⊢* ⟨0, 1, 0, 4*m+5, 0⟩ := by
  apply stepStar_trans (phase1_even (m + 1))
  apply stepStar_trans (phase2 (2 * (m + 1)))
  rw [show 2 * (2 * (m + 1)) + 2 = 2 * (2 * m + 1) + 4 from by ring]
  apply stepStar_trans (phase3_succ (2 * m + 1))
  ring_nf; finish

-- Main transition: (0, 1, 0, d+1, 0) ->⁺ (0, 1, 0, 2d+3, 0) for all d
theorem main_trans (d : ℕ) : ⟨0, 1, 0, d+1, 0⟩ [fm]⊢⁺ ⟨0, 1, 0, 2*d+3, 0⟩ := by
  apply stepStar_stepPlus
  · rcases Nat.even_or_odd d with ⟨m, hm⟩ | ⟨m, hm⟩
    · -- d = 2m, d+1 = 2m+1
      subst hm
      rw [show m + m + 1 = 2 * m + 1 from by ring,
          show 2 * (m + m) + 3 = 4 * m + 3 from by ring]
      exact main_star_odd m
    · -- d = 2m+1, d+1 = 2(m+1)
      subst hm
      rw [show 2 * m + 1 + 1 = 2 * (m + 1) from by ring,
          show 2 * (2 * m + 1) + 3 = 4 * m + 5 from by ring]
      exact main_star_even_succ m
  · intro h; injection h with h1 h2; injection h2 with h3 h4; injection h4 with h5 h6
    injection h6 with h7 h8; omega

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨0, 1, 0, 2, 0⟩) (by execute fm 1)
  apply progress_nonhalt_simple (fm := fm) (A := ℕ)
    (fun n ↦ ⟨0, 1, 0, n+2, 0⟩) 0
  intro n
  refine ⟨2*n+3, ?_⟩
  show ⟨0, 1, 0, n+2, 0⟩ [fm]⊢⁺ ⟨0, 1, 0, (2*n+3)+2, 0⟩
  rw [show n + 2 = (n + 1) + 1 from by ring, show (2 * n + 3) + 2 = 2 * (n + 1) + 3 from by ring]
  exact main_trans (n + 1)

end Sz22_2003_unofficial_199
