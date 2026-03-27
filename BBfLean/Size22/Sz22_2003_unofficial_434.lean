import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #434: [27/35, 20/3, 1/20, 49/2, 3/7]

Vector representation:
```
 0  3 -1 -1
 2 -1  1  0
-2  0 -1  0
-1  0  0  2
 0  1  0 -1
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_434

def Q := ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a, b, c+1, d+1⟩ => some ⟨a, b+3, c, d⟩
  | ⟨a, b+1, c, d⟩ => some ⟨a+2, b, c+1, d⟩
  | ⟨a+2, b, c+1, d⟩ => some ⟨a, b, c, d⟩
  | ⟨a+1, b, c, d⟩ => some ⟨a, b, c, d+2⟩
  | ⟨a, b, c, d+1⟩ => some ⟨a, b+1, c, d⟩
  | _ => none

-- R4 loop: (a+k, 0, 0, d) ->* (a, 0, 0, d+2*k)
theorem r4_loop : ∀ k a d, ⟨a+k, 0, 0, d⟩ [fm]⊢* ⟨a, 0, 0, d+2*k⟩ := by
  intro k; induction k with
  | zero => intro a d; simp; exists 0
  | succ k ih =>
    intro a d
    rw [show a + (k + 1) = (a + k) + 1 from by ring]
    step fm
    apply stepStar_trans (ih a (d + 2))
    ring_nf; finish

-- R2,R1 pair loop: (2*k, 2*k+1, 0, j+1) ->* (2*(k+j+1), 2*(k+j+1)+1, 0, 0)
theorem r2r1_loop : ∀ j k, ⟨2*k, 2*k+1, 0, j+1⟩ [fm]⊢* ⟨2*(k+j+1), 2*(k+j+1)+1, 0, 0⟩ := by
  intro j; induction j with
  | zero =>
    intro k
    step fm; step fm
    show ⟨2*k+2, 2*k+3, 0, 0⟩ [fm]⊢* ⟨2*(k+0+1), 2*(k+0+1)+1, 0, 0⟩
    ring_nf; finish
  | succ j ih =>
    intro k
    step fm; step fm
    show ⟨2*k+2, 2*k+3, 0, j+1⟩ [fm]⊢* ⟨2*(k+(j+1)+1), 2*(k+(j+1)+1)+1, 0, 0⟩
    have h := ih (k+1)
    simp only [(by ring : 2*(k+1) = 2*k+2),
               (by ring : (k+1)+j+1 = k+(j+1)+1)] at h
    exact h

-- R2 loop: (a, k+b, c, 0) ->* (a+2*k, b, c+k, 0)
theorem r2_loop : ∀ k a b c, ⟨a, k+b, c, 0⟩ [fm]⊢* ⟨a+2*k, b, c+k, 0⟩ := by
  intro k; induction k with
  | zero => intro a b c; simp; exists 0
  | succ k ih =>
    intro a b c
    rw [show (k + 1) + b = (k + b) + 1 from by ring]
    step fm
    apply stepStar_trans (ih (a + 2) b (c + 1))
    ring_nf; finish

-- R3 loop: (2*k+a, 0, k+c, 0) ->* (a, 0, c, 0)
theorem r3_loop : ∀ k a c, ⟨2*k+a, 0, k+c, 0⟩ [fm]⊢* ⟨a, 0, c, 0⟩ := by
  intro k; induction k with
  | zero => intro a c; simp; exists 0
  | succ k ih =>
    intro a c
    rw [show 2*(k+1)+a = 2*k+a + 2 from by ring,
        show (k + 1) + c = k + c + 1 from by ring]
    step fm
    exact ih a c

-- Main recurrence: (2*(n+1), 0, 0, 0) ⊢⁺ (2*(4*n+3), 0, 0, 0)
theorem main_recurrence (n : ℕ) : ⟨2*(n+1), 0, 0, 0⟩ [fm]⊢⁺ ⟨2*(4*n+3), 0, 0, 0⟩ := by
  -- Phase 1: R4 x (2*(n+1)): (2*(n+1), 0, 0, 0) ->* (0, 0, 0, 4*n+4)
  have h1 : ⟨2*(n+1), 0, 0, 0⟩ [fm]⊢* ⟨0, 0, 0, 4*n+4⟩ := by
    have h := r4_loop (2*(n+1)) 0 0
    simp only [Nat.zero_add, (by ring : 0 + 2*(2*(n+1)) = 4*n+4)] at h
    exact h
  -- Phase 2: R5, R2, R1, then r2r1_loop: (0, 0, 0, 4*n+4) ->* (8*n+6, 8*n+7, 0, 0)
  have h2 : ⟨0, 0, 0, 4*n+4⟩ [fm]⊢⁺ ⟨8*n+6, 8*n+7, 0, 0⟩ := by
    rw [show 4*n+4 = (4*n+3) + 1 from by ring]
    step fm; step fm; step fm
    show ⟨2, 3, 0, 4*n+2⟩ [fm]⊢* ⟨8*n+6, 8*n+7, 0, 0⟩
    rw [show 4*n+2 = (4*n+1) + 1 from by ring]
    have h := r2r1_loop (4*n+1) 1
    simp only [(by ring : 2*1 = 2), (by ring : 2*1+1 = 3),
               (by ring : 1+(4*n+1)+1 = 4*n+3),
               (by ring : 2*(4*n+3) = 8*n+6)] at h
    exact h
  -- Phase 3: R2 x (8*n+7): (8*n+6, 8*n+7, 0, 0) ->* (24*n+20, 0, 8*n+7, 0)
  have h3 : ⟨8*n+6, 8*n+7, 0, 0⟩ [fm]⊢* ⟨24*n+20, 0, 8*n+7, 0⟩ := by
    have h := r2_loop (8*n+7) (8*n+6) 0 0
    simp only [(by ring : (8*n+7) + 0 = 8*n+7),
               (by ring : (8*n+6) + 2*(8*n+7) = 24*n+20),
               (by ring : 0 + (8*n+7) = 8*n+7)] at h
    exact h
  -- Phase 4: R3 x (8*n+7): (24*n+20, 0, 8*n+7, 0) ->* (8*n+6, 0, 0, 0)
  have h4 : ⟨24*n+20, 0, 8*n+7, 0⟩ [fm]⊢* ⟨8*n+6, 0, 0, 0⟩ := by
    have h := r3_loop (8*n+7) (8*n+6) 0
    simp only [(by ring : 2*(8*n+7)+(8*n+6) = 24*n+20),
               (by ring : (8*n+7) + 0 = 8*n+7)] at h
    exact h
  -- Chain: h1 is star, h2 is plus, h3 is star, h4 is star
  rw [show 2*(4*n+3) = 8*n+6 from by ring]
  exact stepPlus_stepStar_stepPlus
    (stepStar_stepPlus_stepPlus h1 h2)
    (stepStar_trans h3 h4)

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨2, 0, 0, 0⟩) (by execute fm 10)
  show ¬halts fm ⟨2 * (0 + 1), 0, 0, 0⟩
  apply progress_nonhalt_simple (fm := fm) (A := ℕ) (fun n ↦ ⟨2*(n+1), 0, 0, 0⟩) 0
  intro n
  exact ⟨4*n+2, by
    show ⟨2*(n+1), 0, 0, 0⟩ [fm]⊢⁺ ⟨2*((4*n+2)+1), 0, 0, 0⟩
    rw [show (4*n+2)+1 = 4*n+3 from by ring]
    exact main_recurrence n⟩

end Sz22_2003_unofficial_434
