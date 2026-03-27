import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #614: [35/6, 121/2, 4/605, 3/7, 14/11]

Vector representation:
```
-1 -1  1  1  0
-1  0  0  0  2
 2  0 -1  0 -2
 0  1  0 -1  0
 1  0  0  1 -1
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_614

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a+1, b+1, c, d, e⟩ => some ⟨a, b, c+1, d+1, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b, c, d, e+2⟩
  | ⟨a, b, c+1, d, e+2⟩ => some ⟨a+2, b, c, d, e⟩
  | ⟨a, b, c, d+1, e⟩ => some ⟨a, b+1, c, d, e⟩
  | ⟨a, b, c, d, e+1⟩ => some ⟨a+1, b, c, d+1, e⟩
  | _ => none

-- R4 repeated: convert d to b
theorem d_to_b : ∀ k b, ⟨0, b, 0, d + k, e⟩ [fm]⊢* ⟨0, b + k, 0, d, e⟩ := by
  intro k; induction k with
  | zero => intro b; exists 0
  | succ k ih =>
    intro b
    rw [show d + (k + 1) = (d + k) + 1 from by omega]
    step fm
    apply stepStar_trans (ih _)
    ring_nf; finish

-- R3+R2+R2 drain: each round decreases c by 1 and increases e by 2
theorem drain_c : ∀ k c e, ⟨0, 0, c + k, d, e + 2⟩ [fm]⊢* ⟨0, 0, c, d, e + 2 + 2 * k⟩ := by
  intro k; induction k with
  | zero => intro c e; exists 0
  | succ k ih =>
    intro c e
    rw [show c + (k + 1) = (c + k) + 1 from by omega]
    step fm; step fm; step fm
    -- Goal: (0, 0, c+k, d, e+2+2) ⊢* (0, 0, c, d, e+2+2*(k+1))
    apply stepStar_trans (ih c (e + 2))
    rw [show e + 2 + 2 + 2 * k = e + 2 + 2 * (k + 1) from by omega]
    finish

-- R3+R1+R1 interleaving chain
theorem r3r1r1_chain : ∀ k (c d e : ℕ),
    ⟨0, 2 * k + b, c + 1, d, 2 * k + e⟩ [fm]⊢* ⟨0, b, c + k + 1, 2 * k + d, e⟩ := by
  intro k; induction k with
  | zero => intro c d e; simp; exists 0
  | succ k ih =>
    intro c d e
    rw [show 2 * (k + 1) + b = (2 * k + b) + 1 + 1 from by omega,
        show 2 * (k + 1) + e = (2 * k + e) + 2 from by omega]
    step fm; step fm; step fm
    apply stepStar_trans (ih (c + 1) (d + 2) e)
    rw [show c + 1 + k + 1 = c + (k + 1) + 1 from by omega,
        show 2 * k + (d + 2) = 2 * (k + 1) + d from by omega]
    finish

-- Odd n transition: (0,0,0,2m+1,2m+3) ⊢⁺ (0,0,0,2m+2,2m+4)
theorem trans_odd : ⟨0, 0, 0, 2 * m + 1, 2 * m + 3⟩ [fm]⊢⁺ ⟨0, 0, 0, 2 * m + 2, 2 * m + 4⟩ := by
  -- d_to_b
  rw [show 2 * m + 1 = 0 + (2 * m + 1) from by omega]
  apply stepStar_stepPlus_stepPlus (d_to_b (2 * m + 1) 0)
  -- R5 + R1
  rw [show 0 + (2 * m + 1) = (2 * m) + 1 from by omega,
      show 2 * m + 3 = (2 * m + 2) + 1 from by omega]
  step fm; step fm
  -- At: (0, 2*m, 1, 2, 2*m+2); chain + drain
  apply stepStar_trans (r3r1r1_chain (b := 0) m 0 2 2)
  -- drain
  apply stepStar_trans (drain_c (d := 2 * m + 2) (m + 1) 0 0)
  rw [show 0 + 2 + 2 * (m + 1) = 2 * m + 4 from by omega]; finish

-- Even n transition: (0,0,0,2m+2,2m+4) ⊢⁺ (0,0,0,2m+3,2m+5)
theorem trans_even : ⟨0, 0, 0, 2 * m + 2, 2 * m + 4⟩ [fm]⊢⁺ ⟨0, 0, 0, 2 * m + 3, 2 * m + 5⟩ := by
  -- d_to_b
  rw [show 2 * m + 2 = 0 + (2 * m + 2) from by omega]
  apply stepStar_stepPlus_stepPlus (d_to_b (2 * m + 2) 0)
  -- R5 + R1
  rw [show 0 + (2 * m + 2) = (2 * m + 1) + 1 from by omega,
      show 2 * m + 4 = (2 * m + 3) + 1 from by omega]
  step fm; step fm
  -- At: (0, 2*m+1, 1, 2, 2*m+3)
  -- chain with k=m, b=1
  apply stepStar_trans (r3r1r1_chain (b := 1) m 0 2 3)
  -- At: (0, 1, 0+m+1, 2*m+2, 3). R3+R1+R2 tail
  rw [show (3 : ℕ) = 1 + 2 from by omega]
  step fm; step fm; step fm
  -- drain
  apply stepStar_trans (drain_c (d := 2 * m + 3) (m + 1) 0 1)
  rw [show 1 + 2 + 2 * (m + 1) = 2 * m + 5 from by omega]; finish

-- Combined: (0,0,0,n,n+2) ⊢⁺ (0,0,0,n+1,n+3)
theorem main_trans : ⟨0, 0, 0, n, n + 2⟩ [fm]⊢⁺ ⟨0, 0, 0, n + 1, n + 3⟩ := by
  rcases Nat.even_or_odd n with ⟨m, hm⟩ | ⟨m, hm⟩
  · subst hm
    rcases m with _ | m
    · execute fm 2
    · have h := @trans_even m
      rw [show 2 * m + 2 = (m + 1) + (m + 1) from by omega,
          show 2 * m + 4 = (m + 1) + (m + 1) + 2 from by omega,
          show 2 * m + 3 = (m + 1) + (m + 1) + 1 from by omega,
          show 2 * m + 5 = (m + 1) + (m + 1) + 3 from by omega] at h
      exact h
  · subst hm
    have h := @trans_odd m
    rw [show 2 * m + 3 = 2 * m + 1 + 2 from by omega,
        show 2 * m + 2 = 2 * m + 1 + 1 from by omega,
        show 2 * m + 4 = 2 * m + 1 + 3 from by omega] at h
    exact h

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨0, 0, 0, 0, 2⟩) (by execute fm 1)
  apply progress_nonhalt_simple (fm := fm) (A := ℕ)
    (fun n ↦ ⟨0, 0, 0, n, n + 2⟩) 0
  intro n; exact ⟨n + 1, main_trans⟩
