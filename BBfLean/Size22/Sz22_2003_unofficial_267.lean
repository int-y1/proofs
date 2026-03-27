import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #267: [14/15, 1/847, 9/7, 11/3, 875/2]

Vector representation:
```
 1 -1 -1  1  0
 0  0  0 -1 -2
 0  2  0 -1  0
 0 -1  0  0  1
-1  0  3  1  0
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_267

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a, b+1, c+1, d, e⟩ => some ⟨a+1, b, c, d+1, e⟩
  | ⟨a, b, c, d+1, e+2⟩ => some ⟨a, b, c, d, e⟩
  | ⟨a, b, c, d+1, e⟩ => some ⟨a, b+2, c, d, e⟩
  | ⟨a, b+1, c, d, e⟩ => some ⟨a, b, c, d, e+1⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b, c+3, d+1, e⟩
  | _ => none

-- R5+R2 pair: one iteration of the Phase A loop
theorem r5r2_pair : ⟨a+1, 0, c, 0, e+2⟩ [fm]⊢* ⟨a, 0, c+3, 0, e⟩ := by
  step fm; step fm; finish

-- Iterated R5+R2
theorem r5r2_iter : ∀ k, ∀ a c e, ⟨a+k, 0, c, 0, e+2*k⟩ [fm]⊢* ⟨a, 0, c+3*k, 0, e⟩ := by
  intro k; induction' k with k ih <;> intro a c e
  · exists 0
  rw [show a + (k + 1) = (a + k) + 1 from by ring,
      show e + 2 * (k + 1) = (e + 2 * k) + 2 from by ring]
  apply stepStar_trans r5r2_pair
  apply stepStar_trans (ih a (c + 3) e)
  rw [show c + 3 + 3 * k = c + 3 * (k + 1) from by ring]
  finish

-- R5 then R3 for e=0
theorem r5r3_0 : ⟨a+1, 0, c, 0, 0⟩ [fm]⊢⁺ ⟨a, 2, c+3, 0, 0⟩ := by
  step fm; step fm; finish

-- R5 then R3 for e=1
theorem r5r3_1 : ⟨a+1, 0, c, 0, 1⟩ [fm]⊢⁺ ⟨a, 2, c+3, 0, 1⟩ := by
  step fm; step fm; finish

-- Phase B triple for e=0
theorem pb_triple_0 : ⟨a, 2, c+2, d, 0⟩ [fm]⊢* ⟨a+2, 2, c, d+1, 0⟩ := by
  step fm; step fm; step fm; finish

-- Phase B triple for e=1
theorem pb_triple_1 : ⟨a, 2, c+2, d, 1⟩ [fm]⊢* ⟨a+2, 2, c, d+1, 1⟩ := by
  step fm; step fm; step fm; finish

-- Phase B iter for e=0
theorem pb_iter_0 : ∀ j, ∀ a c d, ⟨a, 2, c+2*j, d, 0⟩ [fm]⊢* ⟨a+2*j, 2, c, d+j, 0⟩ := by
  intro j; induction' j with j ih <;> intro a c d
  · exists 0
  rw [show c + 2 * (j + 1) = (c + 2 * j) + 2 from by ring]
  apply stepStar_trans pb_triple_0
  apply stepStar_trans (ih _ _ _)
  ring_nf; finish

-- Phase B iter for e=1
theorem pb_iter_1 : ∀ j, ∀ a c d, ⟨a, 2, c+2*j, d, 1⟩ [fm]⊢* ⟨a+2*j, 2, c, d+j, 1⟩ := by
  intro j; induction' j with j ih <;> intro a c d
  · exists 0
  rw [show c + 2 * (j + 1) = (c + 2 * j) + 2 from by ring]
  apply stepStar_trans pb_triple_1
  apply stepStar_trans (ih _ _ _)
  ring_nf; finish

-- R3 drain for e=0
theorem r3_drain_0 : ∀ j, ∀ a b, ⟨a, b, 0, j, 0⟩ [fm]⊢* ⟨a, b+2*j, 0, 0, 0⟩ := by
  intro j; induction' j with j ih <;> intro a b
  · exists 0
  step fm
  apply stepStar_trans (ih a (b + 2))
  ring_nf; finish

-- R3 drain for e=1
theorem r3_drain_1 : ∀ j, ∀ a b, ⟨a, b, 0, j, 1⟩ [fm]⊢* ⟨a, b+2*j, 0, 0, 1⟩ := by
  intro j; induction' j with j ih <;> intro a b
  · exists 0
  step fm
  apply stepStar_trans (ih a (b + 2))
  ring_nf; finish

-- R4 drain: b to e
theorem r4_drain : ∀ j, ∀ a e, ⟨a, j, 0, 0, e⟩ [fm]⊢* ⟨a, 0, 0, 0, e+j⟩ := by
  intro j; induction' j with j ih <;> intro a e
  · exists 0
  step fm
  apply stepStar_trans (ih a (e + 1))
  ring_nf; finish

-- Phase B tail R1 for e=0
theorem pb_tail_0 : ⟨a, 2, 1, d, 0⟩ [fm]⊢* ⟨a+1, 1, 0, d+1, 0⟩ := by
  step fm; finish

-- Phase B tail R1 for e=1
theorem pb_tail_1 : ⟨a, 2, 1, d, 1⟩ [fm]⊢* ⟨a+1, 1, 0, d+1, 1⟩ := by
  step fm; finish

-- Phase B even C, e=0
theorem pb_even_0 (m : ℕ) : ⟨A, 2, 2*m, 0, 0⟩ [fm]⊢* ⟨A+2*m, 0, 0, 0, 2*m+2⟩ := by
  apply stepStar_trans
  · have h := pb_iter_0 m A 0 0
    rw [show 0 + 2 * m = 2 * m from by ring, show 0 + m = m from by ring] at h; exact h
  apply stepStar_trans (r3_drain_0 m _ _)
  apply stepStar_trans (r4_drain _ _ _)
  ring_nf; finish

-- Phase B even C, e=1
theorem pb_even_1 (m : ℕ) : ⟨A, 2, 2*m, 0, 1⟩ [fm]⊢* ⟨A+2*m, 0, 0, 0, 2*m+3⟩ := by
  apply stepStar_trans
  · have h := pb_iter_1 m A 0 0
    rw [show 0 + 2 * m = 2 * m from by ring, show 0 + m = m from by ring] at h; exact h
  apply stepStar_trans (r3_drain_1 m _ _)
  apply stepStar_trans (r4_drain _ _ _)
  ring_nf; finish

-- Phase B odd C, e=0
theorem pb_odd_0 (m : ℕ) : ⟨A, 2, 2*m+1, 0, 0⟩ [fm]⊢* ⟨A+2*m+1, 0, 0, 0, 2*m+3⟩ := by
  apply stepStar_trans
  · have h := pb_iter_0 m A 1 0
    rw [show 1 + 2 * m = 2 * m + 1 from by ring, show 0 + m = m from by ring] at h; exact h
  apply stepStar_trans pb_tail_0
  apply stepStar_trans (r3_drain_0 (m+1) _ 1)
  apply stepStar_trans (r4_drain _ _ _)
  ring_nf; finish

-- Phase B odd C, e=1
theorem pb_odd_1 (m : ℕ) : ⟨A, 2, 2*m+1, 0, 1⟩ [fm]⊢* ⟨A+2*m+1, 0, 0, 0, 2*m+4⟩ := by
  apply stepStar_trans
  · have h := pb_iter_1 m A 1 0
    rw [show 1 + 2 * m = 2 * m + 1 from by ring, show 0 + m = m from by ring] at h; exact h
  apply stepStar_trans pb_tail_1
  apply stepStar_trans (r3_drain_1 (m+1) _ 1)
  apply stepStar_trans (r4_drain _ _ _)
  ring_nf; finish

-- Combined Phase B for e=0
theorem phase_b_0 (C : ℕ) : ⟨A, 2, C, 0, 0⟩ [fm]⊢* ⟨A+C, 0, 0, 0, C+2⟩ := by
  rcases Nat.even_or_odd C with ⟨m, hm⟩ | ⟨m, hm⟩
  · subst hm; rw [show m + m = 2 * m from by ring]
    apply stepStar_trans (pb_even_0 m); ring_nf; finish
  · subst hm
    apply stepStar_trans (pb_odd_0 m); ring_nf; finish

-- Combined Phase B for e=1
theorem phase_b_1 (C : ℕ) : ⟨A, 2, C, 0, 1⟩ [fm]⊢* ⟨A+C, 0, 0, 0, C+3⟩ := by
  rcases Nat.even_or_odd C with ⟨m, hm⟩ | ⟨m, hm⟩
  · subst hm; rw [show m + m = 2 * m from by ring]
    apply stepStar_trans (pb_even_1 m); ring_nf; finish
  · subst hm
    apply stepStar_trans (pb_odd_1 m); ring_nf; finish

-- Full transition for even e=2k
theorem trans_even (k : ℕ) :
    ⟨a+k+1, 0, 0, 0, 2*k⟩ [fm]⊢⁺ ⟨a+3*k+3, 0, 0, 0, 3*k+5⟩ := by
  -- Phase A: r5r2_iter then r5r3_0
  apply stepStar_stepPlus_stepPlus
  · have h := r5r2_iter k (a+1) 0 0
    rw [show (a + 1) + k = a + k + 1 from by ring,
        show 0 + 2 * k = 2 * k from by ring,
        show 0 + 3 * k = 3 * k from by ring] at h; exact h
  -- r5r3_0: stepPlus
  apply stepPlus_stepStar_stepPlus r5r3_0
  -- Phase B
  have h := phase_b_0 (A := a) (3*k+3)
  rw [show (3 * k + 3) + 2 = 3 * k + 5 from by ring,
      show a + (3 * k + 3) = a + 3 * k + 3 from by ring] at h; exact h

-- Full transition for odd e=2k+1
theorem trans_odd (k : ℕ) :
    ⟨a+k+1, 0, 0, 0, 2*k+1⟩ [fm]⊢⁺ ⟨a+3*k+3, 0, 0, 0, 3*k+6⟩ := by
  apply stepStar_stepPlus_stepPlus
  · have h := r5r2_iter k (a+1) 0 1
    rw [show (a + 1) + k = a + k + 1 from by ring,
        show 1 + 2 * k = 2 * k + 1 from by ring,
        show 0 + 3 * k = 3 * k from by ring] at h; exact h
  apply stepPlus_stepStar_stepPlus r5r3_1
  have h := phase_b_1 (A := a) (3*k+3)
  rw [show (3 * k + 3) + 3 = 3 * k + 6 from by ring,
      show a + (3 * k + 3) = a + 3 * k + 3 from by ring] at h; exact h

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨3, 0, 0, 0, 5⟩)
  · execute fm 13
  apply progress_nonhalt (fm := fm)
    (P := fun q ↦ ∃ a e, q = ⟨a, 0, 0, 0, e⟩ ∧ e ≥ 5 ∧ a ≥ e / 2 + 1)
  · intro c ⟨a, e, hq, he, ha⟩; subst hq
    rcases Nat.even_or_odd e with ⟨k, hk⟩ | ⟨k, hk⟩
    · subst hk
      rw [show k + k = 2 * k from by ring] at ha he ⊢
      obtain ⟨m, rfl⟩ : ∃ m, a = m + k + 1 := ⟨a - k - 1, by omega⟩
      exact ⟨⟨m+3*k+3, 0, 0, 0, 3*k+5⟩,
             ⟨m+3*k+3, 3*k+5, rfl, by omega, by omega⟩,
             trans_even k⟩
    · subst hk
      obtain ⟨m, rfl⟩ : ∃ m, a = m + k + 1 := ⟨a - k - 1, by omega⟩
      exact ⟨⟨m+3*k+3, 0, 0, 0, 3*k+6⟩,
             ⟨m+3*k+3, 3*k+6, rfl, by omega, by omega⟩,
             trans_odd k⟩
  · exact ⟨3, 5, rfl, by omega, by omega⟩

end Sz22_2003_unofficial_267
