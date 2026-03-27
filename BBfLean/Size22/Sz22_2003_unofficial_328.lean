import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #328: [18/35, 5/33, 7/3, 11/49, 75/2]

Vector representation:
```
 1  2 -1 -1  0
 0 -1  1  0 -1
 0 -1  0  1  0
 0  0  0 -2  1
-1  1  2  0  0
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_328

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a, b, c+1, d+1, e⟩ => some ⟨a+1, b+2, c, d, e⟩
  | ⟨a, b+1, c, d, e+1⟩ => some ⟨a, b, c+1, d, e⟩
  | ⟨a, b+1, c, d, e⟩ => some ⟨a, b, c, d+1, e⟩
  | ⟨a, b, c, d+2, e⟩ => some ⟨a, b, c, d, e+1⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b+1, c+2, d, e⟩
  | _ => none

-- r3,r1 loop: each pair increments a,b by 1 and decrements c by 1
theorem r3r1_loop : ∀ k, ∀ a b,
    ⟨a, b + 1, k + 1, 0, 0⟩ [fm]⊢* ⟨a + k + 1, b + k + 2, 0, 0, 0⟩ := by
  intro k; induction k with
  | zero => intro a b; step fm; step fm; ring_nf; finish
  | succ k ih =>
    intro a b; step fm; step fm
    have h := ih (a + 1) (b + 1)
    simp only [(by ring : a + 1 + k + 1 = a + (k + 1) + 1),
               (by ring : b + 1 + k + 2 = b + (k + 1) + 2)] at h
    exact h

-- r3 drain: transfer b to d
theorem r3_drain : ∀ k, ∀ a d,
    ⟨a, k + 1, 0, d, 0⟩ [fm]⊢* ⟨a, 0, 0, d + k + 1, 0⟩ := by
  intro k; induction k with
  | zero => intro a d; step fm; ring_nf; finish
  | succ k ih =>
    intro a d; step fm
    have h := ih a (d + 1)
    simp only [(by ring : d + 1 + k + 1 = d + (k + 1) + 1)] at h
    exact h

-- r4 loop (even): halve d into e
theorem r4_loop_even : ∀ k, ∀ a e,
    ⟨a, 0, 0, 2 * k + 2, e⟩ [fm]⊢* ⟨a, 0, 0, 0, e + k + 1⟩ := by
  intro k; induction k with
  | zero => intro a e; step fm; ring_nf; finish
  | succ k ih =>
    intro a e
    rw [show 2 * (k + 1) + 2 = (2 * k + 2) + 2 from by ring]
    step fm
    have h := ih a (e + 1)
    simp only [(by ring : e + 1 + k + 1 = e + (k + 1) + 1)] at h
    exact h

-- r4 loop (odd): halve d into e, leaving remainder 1
theorem r4_loop_odd : ∀ k, ∀ a e,
    ⟨a, 0, 0, 2 * k + 3, e⟩ [fm]⊢* ⟨a, 0, 0, 1, e + k + 1⟩ := by
  intro k; induction k with
  | zero => intro a e; step fm; ring_nf; finish
  | succ k ih =>
    intro a e
    rw [show 2 * (k + 1) + 3 = (2 * k + 3) + 2 from by ring]
    step fm
    have h := ih a (e + 1)
    simp only [(by ring : e + 1 + k + 1 = e + (k + 1) + 1)] at h
    exact h

-- r5,r2 loop: convert e into c (gaining 3 per unit of e)
theorem r5r2_loop : ∀ k, ∀ a c,
    ⟨a + k, 0, c, 0, k⟩ [fm]⊢* ⟨a, 0, c + 3 * k, 0, 0⟩ := by
  intro k; induction k with
  | zero => intro a c; ring_nf; finish
  | succ k ih =>
    intro a c
    rw [show a + (k + 1) = (a + k) + 1 from by ring]
    step fm; step fm
    have h := ih a (c + 3)
    simp only [(by ring : c + 3 + 3 * k = c + 3 * (k + 1))] at h
    exact h

-- odd d transition: r5, r1, r2 x 3
theorem odd_transition : ∀ k a,
    ⟨a + 1, 0, 0, 1, k + 3⟩ [fm]⊢* ⟨a + 1, 0, 4, 0, k⟩ := by
  intro k a; execute fm 5

-- Main transition for c odd:
-- (a+1, 0, 2j+1, 0, 0) ⊢⁺ (a+1+j, 0, 3j+6, 0, 0)
theorem main_odd (j a : ℕ) :
    ⟨a + 1, 0, 2 * j + 1, 0, 0⟩ [fm]⊢⁺ ⟨a + 1 + j, 0, 3 * j + 6, 0, 0⟩ := by
  step fm; step fm; step fm
  -- State: (a+1, 2, 2j+2, 0, 0)
  apply stepStar_trans
  · have h := r3r1_loop (2 * j + 1) (a + 1) 1
    simp only [(by ring : a + 1 + (2 * j + 1) + 1 = a + 2 * j + 3),
               (by ring : 1 + (2 * j + 1) + 2 = 2 * j + 4)] at h
    exact h
  -- State: (a+2j+3, 2j+4, 0, 0, 0)
  apply stepStar_trans
  · have h := r3_drain (2 * j + 3) (a + 2 * j + 3) 0
    simp only [(by ring : 0 + (2 * j + 3) + 1 = 2 * j + 4)] at h
    exact h
  -- State: (a+2j+3, 0, 0, 2j+4, 0)
  apply stepStar_trans
  · have h := r4_loop_even (j + 1) (a + 2 * j + 3) 0
    simp only [(by ring : 2 * (j + 1) + 2 = 2 * j + 4),
               (by ring : 0 + (j + 1) + 1 = j + 2)] at h
    exact h
  -- State: (a+2j+3, 0, 0, 0, j+2)
  have h := r5r2_loop (j + 2) (a + 1 + j) 0
  simp only [(by ring : (a + 1 + j) + (j + 2) = a + 2 * j + 3),
             (by ring : 0 + 3 * (j + 2) = 3 * j + 6)] at h
  exact h

-- Main transition for c even (c = 2(k+2)):
-- (a+1, 0, 2(k+2), 0, 0) ⊢⁺ (a+k+6, 0, 3k+4, 0, 0)
theorem main_even (k a : ℕ) :
    ⟨a + 1, 0, 2 * (k + 2), 0, 0⟩ [fm]⊢⁺ ⟨a + k + 6, 0, 3 * k + 4, 0, 0⟩ := by
  step fm; step fm; step fm
  -- State: (a+1, 2, 2k+5, 0, 0)
  apply stepStar_trans
  · have h := r3r1_loop (2 * k + 4) (a + 1) 1
    simp only [(by ring : a + 1 + (2 * k + 4) + 1 = a + 2 * k + 6),
               (by ring : 1 + (2 * k + 4) + 2 = 2 * k + 7)] at h
    exact h
  -- State: (a+2k+6, 2k+7, 0, 0, 0)
  apply stepStar_trans
  · have h := r3_drain (2 * k + 6) (a + 2 * k + 6) 0
    simp only [(by ring : 0 + (2 * k + 6) + 1 = 2 * k + 7)] at h
    exact h
  -- State: (a+2k+6, 0, 0, 2k+7, 0)
  apply stepStar_trans
  · have h := r4_loop_odd (k + 2) (a + 2 * k + 6) 0
    simp only [(by ring : 2 * (k + 2) + 3 = 2 * k + 7),
               (by ring : 0 + (k + 2) + 1 = k + 3)] at h
    exact h
  -- State: (a+2k+6, 0, 0, 1, k+3)
  apply stepStar_trans
  · have h := odd_transition k (a + 2 * k + 5)
    simp only [(by ring : a + 2 * k + 5 + 1 = a + 2 * k + 6)] at h
    exact h
  -- State: (a+2k+6, 0, 4, 0, k)
  have h := r5r2_loop k (a + k + 6) 4
  simp only [(by ring : (a + k + 6) + k = a + 2 * k + 6),
             (by ring : 4 + 3 * k = 3 * k + 4)] at h
  exact h

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := (⟨2, 0, 6, 0, 0⟩ : Q))
  · execute fm 26
  apply progress_nonhalt_simple (fm := fm) (A := ℕ × ℕ)
    (fun ⟨a, c⟩ ↦ (⟨a + 1, 0, c + 4, 0, 0⟩ : Q)) ⟨1, 2⟩
  intro ⟨a, c⟩
  rcases Nat.even_or_odd c with ⟨k, hk⟩ | ⟨k, hk⟩
  · subst hk
    refine ⟨⟨a + k + 5, 3 * k⟩, ?_⟩
    show ⟨a + 1, 0, k + k + 4, 0, 0⟩ [fm]⊢⁺ ⟨a + k + 5 + 1, 0, 3 * k + 4, 0, 0⟩
    have h := main_even k a
    simp only [(by ring : 2 * (k + 2) = k + k + 4),
               (by ring : a + k + 6 = a + k + 5 + 1)] at h
    exact h
  · subst hk
    refine ⟨⟨a + k + 2, 3 * k + 8⟩, ?_⟩
    show ⟨a + 1, 0, (2 * k + 1) + 4, 0, 0⟩ [fm]⊢⁺ ⟨a + k + 2 + 1, 0, (3 * k + 8) + 4, 0, 0⟩
    have h := main_odd (k + 2) a
    simp only [(by ring : 2 * (k + 2) + 1 = 2 * k + 1 + 4),
               (by ring : a + 1 + (k + 2) = a + k + 2 + 1),
               (by ring : 3 * (k + 2) + 6 = 3 * k + 8 + 4)] at h
    exact h

end Sz22_2003_unofficial_328
