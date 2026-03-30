import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #1000: [4/15, 33/98, 55/2, 7/11, 6/5]

Vector representation:
```
 2 -1 -1  0  0
-1  1  0 -2  1
-1  0  1  0  1
 0  0  0  1 -1
 1  1 -1  0  0
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_1000

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a, b+1, c+1, d, e⟩ => some ⟨a+2, b, c, d, e⟩
  | ⟨a+1, b, c, d+2, e⟩ => some ⟨a, b+1, c, d, e+1⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b, c+1, d, e+1⟩
  | ⟨a, b, c, d, e+1⟩ => some ⟨a, b, c, d+1, e⟩
  | ⟨a, b, c+1, d, e⟩ => some ⟨a+1, b+1, c, d, e⟩
  | _ => none

-- R4: transfer e to d (with a=0, b=0 so R1,R2,R3 don't fire).
theorem e_to_d : ∀ k d, ⟨0, 0, c, d, e + k⟩ [fm]⊢* ⟨0, 0, c, d + k, e⟩ := by
  intro k; induction' k with k ih
  · intro d; exists 0
  · intro d; rw [Nat.add_succ]
    step fm
    apply stepStar_trans (ih (d + 1)); ring_nf; finish

-- R2+R1 chain.
theorem r2r1_chain : ∀ k a d e, ⟨a + 1, 0, k, d + 2 * k, e⟩ [fm]⊢* ⟨a + k + 1, 0, 0, d, e + k⟩ := by
  intro k; induction' k with k ih
  · intro a d e; exists 0
  · intro a d e
    rw [show d + 2 * (k + 1) = (d + 2 * k) + 2 from by ring]
    step fm; step fm
    apply stepStar_trans (ih (a + 1) d (e + 1)); ring_nf; finish

-- R2-only chain.
theorem r2_chain : ∀ k a b d e, ⟨a + k, b, 0, d + 2 * k, e⟩ [fm]⊢* ⟨a, b + k, 0, d, e + k⟩ := by
  intro k; induction' k with k ih
  · intro a b d e; exists 0
  · intro a b d e
    rw [show a + (k + 1) = (a + k) + 1 from by ring,
        show d + 2 * (k + 1) = (d + 2 * k) + 2 from by ring]
    step fm
    apply stepStar_trans (ih a (b + 1) d (e + 1)); ring_nf; finish

-- R3+R1 chain with d=0.
theorem r3r1_d0 : ∀ k a e, ⟨a + 1, k, 0, 0, e⟩ [fm]⊢* ⟨a + k + 1, 0, 0, 0, e + k⟩ := by
  intro k; induction' k with k ih
  · intro a e; exists 0
  · intro a e; step fm; step fm
    apply stepStar_trans (ih (a + 1) (e + 1)); ring_nf; finish

-- R3+R1 chain with d=1.
theorem r3r1_d1 : ∀ k a e, ⟨a + 1, k, 0, 1, e⟩ [fm]⊢* ⟨a + k + 1, 0, 0, 1, e + k⟩ := by
  intro k; induction' k with k ih
  · intro a e; exists 0
  · intro a e; step fm; step fm
    apply stepStar_trans (ih (a + 1) (e + 1)); ring_nf; finish

-- R3 drain with d=0.
theorem r3_drain_d0 : ∀ j c e, ⟨j, 0, c, 0, e⟩ [fm]⊢* ⟨0, 0, c + j, 0, e + j⟩ := by
  intro j; induction' j with j ih
  · intro c e; exists 0
  · intro c e; step fm
    apply stepStar_trans (ih (c + 1) (e + 1)); ring_nf; finish

-- R3 drain with d=1.
theorem r3_drain_d1 : ∀ j c e, ⟨j, 0, c, 1, e⟩ [fm]⊢* ⟨0, 0, c + j, 1, e + j⟩ := by
  intro j; induction' j with j ih
  · intro c e; exists 0
  · intro c e; step fm
    apply stepStar_trans (ih (c + 1) (e + 1)); ring_nf; finish

-- Even case: (0, 0, 2k+2, 6k+4, 0) ⊢⁺ (0, 0, 2k+3, 6k+7, 0)
theorem main_even (k : ℕ) :
    ⟨0, 0, 2 * k + 2, 6 * k + 4, 0⟩ [fm]⊢⁺ ⟨0, 0, 2 * k + 3, 6 * k + 7, 0⟩ := by
  rw [show 2 * k + 2 = (2 * k + 1) + 1 from by ring]
  step fm; step fm
  rw [show (3 : ℕ) = 2 + 1 from rfl,
      show 6 * k + 4 = (2 * k + 4) + 2 * (2 * k) from by ring]
  apply stepStar_trans (r2r1_chain (2 * k) 2 (2 * k + 4) 0)
  rw [show 2 + 2 * k + 1 = (k + 1) + (k + 2) from by ring,
      show (0 + 2 * k : ℕ) = 2 * k from by ring,
      show 2 * k + 4 = 0 + 2 * (k + 2) from by ring]
  apply stepStar_trans (r2_chain (k + 2) (k + 1) 0 0 (2 * k))
  rw [show (0 + (k + 2) : ℕ) = k + 2 from by ring,
      show 2 * k + (k + 2) = 3 * k + 2 from by ring]
  apply stepStar_trans (r3r1_d0 (k + 2) k (3 * k + 2))
  rw [show k + (k + 2) + 1 = 2 * k + 3 from by ring,
      show 3 * k + 2 + (k + 2) = 4 * k + 4 from by ring]
  apply stepStar_trans (r3_drain_d0 (2 * k + 3) 0 (4 * k + 4))
  rw [show 0 + (2 * k + 3) = 2 * k + 3 from by ring,
      show 4 * k + 4 + (2 * k + 3) = 0 + (6 * k + 7) from by ring]
  apply stepStar_trans (e_to_d (6 * k + 7) 0 (c := 2 * k + 3) (e := 0))
  ring_nf; finish

-- Odd case: (0, 0, 2k+3, 6k+7, 0) ⊢⁺ (0, 0, 2k+4, 6k+10, 0)
theorem main_odd (k : ℕ) :
    ⟨0, 0, 2 * k + 3, 6 * k + 7, 0⟩ [fm]⊢⁺ ⟨0, 0, 2 * k + 4, 6 * k + 10, 0⟩ := by
  rw [show 2 * k + 3 = (2 * k + 2) + 1 from by ring]
  step fm; step fm
  rw [show (3 : ℕ) = 2 + 1 from rfl,
      show 6 * k + 7 = (2 * k + 5) + 2 * (2 * k + 1) from by ring]
  apply stepStar_trans (r2r1_chain (2 * k + 1) 2 (2 * k + 5) 0)
  rw [show 2 + (2 * k + 1) + 1 = (k + 2) + (k + 2) from by ring,
      show (0 + (2 * k + 1) : ℕ) = 2 * k + 1 from by ring,
      show 2 * k + 5 = 1 + 2 * (k + 2) from by ring]
  apply stepStar_trans (r2_chain (k + 2) (k + 2) 0 1 (2 * k + 1))
  rw [show (0 + (k + 2) : ℕ) = k + 2 from by ring,
      show (2 * k + 1) + (k + 2) = 3 * k + 3 from by ring]
  apply stepStar_trans (r3r1_d1 (k + 2) (k + 1) (3 * k + 3))
  rw [show (k + 1) + (k + 2) + 1 = 2 * k + 4 from by ring,
      show 3 * k + 3 + (k + 2) = 4 * k + 5 from by ring]
  apply stepStar_trans (r3_drain_d1 (2 * k + 4) 0 (4 * k + 5))
  rw [show 0 + (2 * k + 4) = 2 * k + 4 from by ring,
      show 4 * k + 5 + (2 * k + 4) = 0 + (6 * k + 9) from by ring]
  apply stepStar_trans (e_to_d (6 * k + 9) 1 (c := 2 * k + 4) (e := 0))
  ring_nf; finish

-- Combined transition.
theorem main_trans (n : ℕ) :
    ⟨0, 0, n + 2, 3 * n + 4, 0⟩ [fm]⊢⁺ ⟨0, 0, n + 3, 3 * n + 7, 0⟩ := by
  rcases Nat.even_or_odd n with ⟨k, hk⟩ | ⟨k, hk⟩
  · rw [show k + k = 2 * k from by ring] at hk; subst hk
    rw [show 3 * (2 * k) + 4 = 6 * k + 4 from by ring,
        show 3 * (2 * k) + 7 = 6 * k + 7 from by ring]
    exact main_even k
  · subst hk
    rw [show 2 * k + 1 + 2 = 2 * k + 3 from by ring,
        show 3 * (2 * k + 1) + 4 = 6 * k + 7 from by ring,
        show 2 * k + 1 + 3 = 2 * k + 4 from by ring,
        show 3 * (2 * k + 1) + 7 = 6 * k + 10 from by ring]
    exact main_odd k

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨0, 0, 2, 4, 0⟩)
  · execute fm 10
  apply progress_nonhalt_simple (fm := fm) (A := ℕ)
    (fun n ↦ ⟨0, 0, n + 2, 3 * n + 4, 0⟩) 0
  intro n; exact ⟨n + 1, main_trans n⟩

end Sz22_2003_unofficial_1000
