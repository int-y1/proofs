import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #1556: [7/30, 9/2, 44/21, 5/11, 7/3]

Vector representation:
```
-1 -1 -1  1  0
-1  2  0  0  0
 2 -1  0 -1  1
 0  0  1  0 -1
 0 -1  0  1  0
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_1556

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a+1, b+1, c+1, d, e⟩ => some ⟨a, b, c, d+1, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b+2, c, d, e⟩
  | ⟨a, b+1, c, d+1, e⟩ => some ⟨a+2, b, c, d, e+1⟩
  | ⟨a, b, c, d, e+1⟩ => some ⟨a, b, c+1, d, e⟩
  | ⟨a, b+1, c, d, e⟩ => some ⟨a, b, c, d+1, e⟩
  | _ => none

-- R4 chain: transfer e to c (a=0, b >= 0, d=0).
theorem e_to_c : ∀ k, ∀ b c, ⟨0, b, c, 0, e + k⟩ [fm]⊢* ⟨0, b, c + k, 0, e⟩ := by
  intro k; induction' k with k ih
  · intro b c; exists 0
  · intro b c; rw [Nat.add_succ]; step fm
    apply stepStar_trans (ih b (c + 1)); ring_nf; finish

-- R3,R1,R1 chain for even c: k rounds draining c by 2.
theorem r3r1r1_chain : ∀ k, ∀ b d e,
    ⟨0, b + 3 * k, 2 * k, d + 1, e⟩ [fm]⊢* ⟨0, b, 0, d + k + 1, e + k⟩ := by
  intro k; induction' k with k ih
  · intro b d e; exists 0
  · intro b d e
    rw [show b + 3 * (k + 1) = (b + 3 * k) + 3 from by ring,
        show 2 * (k + 1) = 2 * k + 2 from by ring]
    step fm; step fm; step fm
    apply stepStar_trans (ih b (d + 1) (e + 1))
    ring_nf; finish

-- R1,R1,R3 chain for odd c: k rounds keeping c odd.
theorem r1r1r3_chain : ∀ k, ∀ b d e,
    ⟨2, b + 3 * k, 2 * k + 1, d, e⟩ [fm]⊢* ⟨2, b, 1, d + k, e + k⟩ := by
  intro k; induction' k with k ih
  · intro b d e; exists 0
  · intro b d e
    rw [show b + 3 * (k + 1) = (b + 3 * k) + 3 from by ring,
        show 2 * (k + 1) + 1 = (2 * k + 1) + 2 from by ring]
    step fm; step fm; step fm
    apply stepStar_trans (ih b (d + 1) (e + 1))
    ring_nf; finish

-- R3,R2,R2 chain: drains d (b >= 1 ensured by b+1 pattern).
theorem r3r2r2_chain : ∀ k, ∀ b d e,
    ⟨0, b + 1, 0, d + k, e⟩ [fm]⊢* ⟨0, b + 3 * k + 1, 0, d, e + k⟩ := by
  intro k; induction' k with k ih
  · intro b d e; exists 0
  · intro b d e
    rw [show d + (k + 1) = (d + k) + 1 from by ring]
    step fm; step fm; step fm
    apply stepStar_trans (ih (b + 3) d (e + 1))
    ring_nf; finish

-- Even transition: C(0) ⊢⁺ C(1).
theorem main_even_zero :
    ⟨0, 2, 0, 0, 0⟩ [fm]⊢⁺ ⟨0, 4, 0, 0, 1⟩ := by
  step fm; step fm; step fm; step fm; finish

-- Even transition: C(2(k+1)) ⊢⁺ C(2(k+1)+1) for k >= 0.
theorem main_even_succ (k : ℕ) :
    ⟨0, 4 * k + 6, 0, 0, 2 * k + 2⟩ [fm]⊢⁺ ⟨0, 4 * k + 8, 0, 0, 2 * k + 3⟩ := by
  -- Phase 1: e_to_c (2k+2 steps)
  rw [show 2 * k + 2 = 0 + (2 * k + 2) from by ring]
  apply stepStar_stepPlus_stepPlus (e_to_c (2 * k + 2) (4 * k + 6) 0)
  rw [show 0 + (2 * k + 2) = 2 * k + 2 from by ring]
  -- Phase 2+3: R5, R3
  rw [show 4 * k + 6 = (4 * k + 5) + 1 from by ring,
      show 2 * k + 2 = (2 * k + 1) + 1 from by ring]
  step fm; step fm
  -- Now at (2, 4k+4, 2k+1+1, 0, 1). Rewrite c.
  rw [show 2 * k + 1 + 1 = 2 * k + 2 from by ring]
  -- Phase 4: R1,R1 (a=2, b=4k+4>=1, c=2k+2>=1)
  rw [show 4 * k + 4 = (4 * k + 3) + 1 from by ring,
      show 2 * k + 2 = (2 * k + 1) + 1 from by ring]
  step fm
  rw [show 4 * k + 3 = (4 * k + 2) + 1 from by ring,
      show 2 * k + 1 = (2 * k) + 1 from by ring]
  step fm
  -- Now at (0, 4k+2, 2k, 2, 1) = (0, (k+2)+3*k, 2*k, 1+1, 1)
  rw [show 4 * k + 2 = (k + 2) + 3 * k from by ring]
  -- Phase 5: r3r1r1_chain (k rounds)
  apply stepStar_trans (r3r1r1_chain k (k + 2) 1 1)
  rw [show 1 + k + 1 = k + 2 from by ring, show 1 + k = k + 1 from by ring]
  -- Now at (0, k+2, 0, k+2, k+1). Apply tail chain with d=0.
  -- Phase 6: r3r2r2_chain (k+2 rounds)
  have h := r3r2r2_chain (k + 2) (k + 1) 0 (k + 1)
  simp only [Nat.zero_add] at h
  rw [show k + 2 = (k + 1) + 1 from by ring]
  apply stepStar_trans h
  ring_nf; finish

-- Odd transition: C(2k+1) ⊢⁺ C(2k+2).
theorem main_odd (k : ℕ) :
    ⟨0, 4 * k + 4, 0, 0, 2 * k + 1⟩ [fm]⊢⁺ ⟨0, 4 * k + 6, 0, 0, 2 * k + 2⟩ := by
  -- Phase 1: e_to_c (2k+1 steps)
  rw [show 2 * k + 1 = 0 + (2 * k + 1) from by ring]
  apply stepStar_stepPlus_stepPlus (e_to_c (2 * k + 1) (4 * k + 4) 0)
  rw [show 0 + (2 * k + 1) = 2 * k + 1 from by ring]
  -- Phase 2+3: R5, R3
  rw [show 4 * k + 4 = (4 * k + 3) + 1 from by ring,
      show 2 * k + 1 = (2 * k) + 1 from by ring]
  step fm; step fm
  -- Now at (2, 4k+2, 2k+1, 0, 1) = (2, (k+2)+3*k, 2*k+1, 0, 1)
  rw [show 4 * k + 2 = (k + 2) + 3 * k from by ring]
  -- Phase 4: r1r1r3_chain (k rounds)
  apply stepStar_trans (r1r1r3_chain k (k + 2) 0 1)
  rw [show 0 + k = k from by ring, show 1 + k = k + 1 from by ring]
  -- Now at (2, k+2, 1, k, k+1). R1, R2.
  step fm; step fm
  -- Now at (0, k+1+2, 0, k+1, k+1). Apply tail chain with d=0.
  -- Phase 5: r3r2r2_chain (k+1 rounds)
  have h := r3r2r2_chain (k + 1) (k + 2) 0 (k + 1)
  simp only [Nat.zero_add] at h
  rw [show k + 1 + 2 = (k + 2) + 1 from by ring]
  apply stepStar_trans h
  ring_nf; finish

-- Combined transition: C(n) ⊢⁺ C(n+1).
theorem main_trans (n : ℕ) :
    ⟨0, 2 * n + 2, 0, 0, n⟩ [fm]⊢⁺ ⟨0, 2 * n + 4, 0, 0, n + 1⟩ := by
  rcases Nat.even_or_odd n with ⟨k, hk⟩ | ⟨k, hk⟩
  · rw [show k + k = 2 * k from by ring] at hk; subst hk
    rcases k with _ | k
    · exact main_even_zero
    · rw [show 2 * (2 * (k + 1)) + 2 = 4 * k + 6 from by ring,
          show 2 * (2 * (k + 1)) + 4 = 4 * k + 8 from by ring,
          show 2 * (k + 1) + 1 = 2 * k + 3 from by ring,
          show 2 * (k + 1) = 2 * k + 2 from by ring]
      exact main_even_succ k
  · subst hk
    rw [show 2 * (2 * k + 1) + 2 = 4 * k + 4 from by ring,
        show 2 * (2 * k + 1) + 4 = 4 * k + 6 from by ring,
        show 2 * k + 1 + 1 = 2 * k + 2 from by ring]
    exact main_odd k

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨0, 2, 0, 0, 0⟩) (by execute fm 1)
  apply progress_nonhalt_simple (fm := fm) (A := ℕ)
    (fun n ↦ ⟨0, 2 * n + 2, 0, 0, n⟩) 0
  intro n; exact ⟨n + 1, main_trans n⟩

end Sz22_2003_unofficial_1556
