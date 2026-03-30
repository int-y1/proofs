import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #889: [4/15, 147/22, 175/2, 11/7, 2/5]

Vector representation:
```
 2 -1 -1  0  0
-1  1  0  2 -1
-1  0  2  1  0
 0  0  0 -1  1
 1  0 -1  0  0
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_889

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a, b+1, c+1, d, e⟩ => some ⟨a+2, b, c, d, e⟩
  | ⟨a+1, b, c, d, e+1⟩ => some ⟨a, b+1, c, d+2, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b, c+2, d+1, e⟩
  | ⟨a, b, c, d+1, e⟩ => some ⟨a, b, c, d, e+1⟩
  | ⟨a, b, c+1, d, e⟩ => some ⟨a+1, b, c, d, e⟩
  | _ => none

theorem r4_drain : ∀ k, ⟨0, 0, c, d + k, e⟩ [fm]⊢* ⟨0, 0, c, d, e + k⟩ := by
  intro k; induction' k with k ih generalizing d e
  · exists 0
  · rw [show d + (k + 1) = (d + k) + 1 from by ring]
    step fm; apply stepStar_trans (ih (d := d) (e := e + 1)); ring_nf; finish

theorem r21_chain : ∀ k, ⟨a + 1, 0, c + k, d, e + k⟩ [fm]⊢* ⟨a + k + 1, 0, c, d + 2 * k, e⟩ := by
  intro k; induction' k with k ih generalizing a c d e
  · exists 0
  · rw [show c + (k + 1) = (c + k) + 1 from by ring,
        show e + (k + 1) = (e + k) + 1 from by ring]
    step fm; step fm; rw [show a + 2 = (a + 1) + 1 from by ring]
    apply stepStar_trans (ih (a := a + 1) (d := d + 2)); ring_nf; finish

theorem r2_drain : ∀ k, ⟨a + k, b, 0, d, k⟩ [fm]⊢* ⟨a, b + k, 0, d + 2 * k, 0⟩ := by
  intro k; induction' k with k ih generalizing a b d
  · exists 0
  · rw [show a + (k + 1) = (a + k) + 1 from by ring, show (k : ℕ) + 1 = k + 1 from rfl]
    step fm; apply stepStar_trans (ih (a := a) (b := b + 1) (d := d + 2)); ring_nf; finish

theorem r311_chain : ∀ k, ⟨a + 1, b + 2 * k, 0, d, 0⟩ [fm]⊢* ⟨a + 3 * k + 1, b, 0, d + k, 0⟩ := by
  intro k; induction' k with k ih generalizing a b d
  · exists 0
  · rw [show b + 2 * (k + 1) = (b + 2 * k) + 2 from by ring]
    step fm; step fm; step fm; rw [show a + 4 = (a + 3) + 1 from by ring]
    apply stepStar_trans (ih (a := a + 3) (d := d + 1)); ring_nf; finish

theorem r3_chain : ∀ k, ⟨a + k, 0, c, d, 0⟩ [fm]⊢* ⟨a, 0, c + 2 * k, d + k, 0⟩ := by
  intro k; induction' k with k ih generalizing a c d
  · exists 0
  · rw [show a + (k + 1) = (a + k) + 1 from by ring]
    step fm; apply stepStar_trans (ih (a := a) (c := c + 2) (d := d + 1)); ring_nf; finish

theorem phase34_even : ∀ m, ⟨A + 1, 0 + 2 * m, 0, D, 0⟩ [fm]⊢*
    ⟨0, 0, 2 * A + 6 * m + 2, 0, D + A + 4 * m + 1⟩ := by
  intro m; induction' m with m ih generalizing A D
  · rw [show A + 1 = 0 + (A + 1) from by ring]
    apply stepStar_trans (r3_chain (A + 1) (a := 0) (c := 0) (d := D))
    rw [show D + (A + 1) = 0 + (D + (A + 1)) from by ring]
    apply stepStar_trans (r4_drain (D + (A + 1)) (c := 0 + 2 * (A + 1)) (d := 0) (e := 0))
    ring_nf; finish
  · rw [show 0 + 2 * (m + 1) = (0 + 2 * m) + 2 from by ring]
    step fm; step fm; step fm
    rw [show A + 4 = (A + 3) + 1 from by ring]
    apply stepStar_trans (ih (A := A + 3) (D := D + 1))
    ring_nf; finish

theorem phase34_odd : ∀ m, ⟨A + 1, 1 + 2 * m, 0, D, 0⟩ [fm]⊢*
    ⟨0, 0, 2 * A + 6 * m + 5, 0, D + A + 4 * m + 3⟩ := by
  intro m; induction' m with m ih generalizing A D
  · step fm; step fm
    rw [show A + 2 = 0 + (A + 2) from by ring]
    apply stepStar_trans (r3_chain (A + 2) (a := 0) (c := 1) (d := D + 1))
    rw [show D + 1 + (A + 2) = 0 + (D + 1 + (A + 2)) from by ring]
    apply stepStar_trans (r4_drain (D + 1 + (A + 2)) (c := 1 + 2 * (A + 2)) (d := 0) (e := 0))
    ring_nf; finish
  · rw [show 1 + 2 * (m + 1) = (1 + 2 * m) + 2 from by ring]
    step fm; step fm; step fm
    rw [show A + 4 = (A + 3) + 1 from by ring]
    apply stepStar_trans (ih (A := A + 3) (D := D + 1))
    ring_nf; finish

-- Even case: (0, 0, A+2m+2, 0, A+4m+1) ⊢⁺ (0, 0, 2A+6m+4, 0, 3A+12m+4)
theorem main_trans_even (A m : ℕ) :
    ⟨0, 0, A + 2 * m + 2, 0, A + 4 * m + 1⟩ [fm]⊢⁺
    ⟨0, 0, 2 * A + 6 * m + 4, 0, 3 * A + 12 * m + 4⟩ := by
  rw [show A + 2 * m + 2 = (A + 2 * m + 1) + 1 from by ring]
  apply step_stepStar_stepPlus (by unfold fm; rfl)
  simp only [Nat.succ_eq_add_one]
  rw [show A + 4 * m + 1 = 2 * m + (A + 2 * m + 1) from by ring]
  have h1 := r21_chain (A + 2 * m + 1) (a := 0) (c := 0) (d := 0) (e := 2 * m)
  simp only [Nat.zero_add] at h1
  apply stepStar_trans h1
  rw [show A + 2 * m + 1 + 1 = (A + 2) + 2 * m from by ring]
  have h2 := r2_drain (2 * m) (a := A + 2) (b := 0) (d := 2 * (A + 2 * m + 1))
  simp only [Nat.zero_add] at h2
  apply stepStar_trans h2
  rw [show 2 * (A + 2 * m + 1) + 2 * (2 * m) = 2 * A + 8 * m + 2 from by ring,
      show A + 2 = (A + 1) + 1 from by ring,
      show 2 * m = 0 + 2 * m from by ring]
  apply stepStar_trans (phase34_even m (A := A + 1) (D := 2 * A + 8 * m + 2))
  ring_nf; finish

-- Odd case: (0, 0, A+2m+3, 0, A+4m+3) ⊢⁺ (0, 0, 2A+6m+7, 0, 3A+12m+10)
theorem main_trans_odd (A m : ℕ) :
    ⟨0, 0, A + 2 * m + 3, 0, A + 4 * m + 3⟩ [fm]⊢⁺
    ⟨0, 0, 2 * A + 6 * m + 7, 0, 3 * A + 12 * m + 10⟩ := by
  rw [show A + 2 * m + 3 = (A + 2 * m + 2) + 1 from by ring]
  apply step_stepStar_stepPlus (by unfold fm; rfl)
  simp only [Nat.succ_eq_add_one]
  rw [show A + 4 * m + 3 = (2 * m + 1) + (A + 2 * m + 2) from by ring]
  have h1 := r21_chain (A + 2 * m + 2) (a := 0) (c := 0) (d := 0) (e := 2 * m + 1)
  simp only [Nat.zero_add] at h1
  apply stepStar_trans h1
  rw [show A + 2 * m + 2 + 1 = (A + 2) + (2 * m + 1) from by ring]
  have h2 := r2_drain (2 * m + 1) (a := A + 2) (b := 0) (d := 2 * (A + 2 * m + 2))
  simp only [Nat.zero_add] at h2
  apply stepStar_trans h2
  rw [show 2 * (A + 2 * m + 2) + 2 * (2 * m + 1) = 2 * A + 8 * m + 6 from by ring,
      show A + 2 = (A + 1) + 1 from by ring,
      show 2 * m + 1 = 1 + 2 * m from by ring]
  apply stepStar_trans (phase34_odd m (A := A + 1) (D := 2 * A + 8 * m + 6))
  ring_nf; finish

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨0, 0, 2, 0, 1⟩)
  · execute fm 2
  -- Canonical form: (0, 0, C, 0, E) where C = A+B+2, E = A+2B+1
  -- Even B = 2m: C = A+2m+2, E = A+4m+1
  -- Odd B = 2m+1: C = A+2m+3, E = A+4m+3
  -- Transition even: (A, m) -> (A+1, A+3*(2m)+1) = (A+1, 6m+A+1), so next C = (A+1)+(6m+A+1)+2 = 2A+6m+4, E = (A+1)+2*(6m+A+1)+1 = 3A+12m+4
  -- But we need to express next state in terms of new (A', B') or (A', m').
  -- Even: next(A, m) -> C'=2A+6m+4, E'=3A+12m+4.
  --   E'-1 = 3A+12m+3. (E'-1)/2 = ? Not necessarily integer.
  --   C'-2 = 2A+6m+2. Let's try B' = E'-(C'-2+1) = E'-C'+1 = 3A+12m+4-2A-6m-4+1 = A+6m+1.
  --   So A' = C'-2-B' = 2A+6m+2-(A+6m+1) = A+1.
  --   B' = A+6m+1, which is odd if A is even and vice versa.
  --   B' even: B' = 2m', m' = (A+6m+1)/2 -- only if A odd.
  --   B' odd: B' = 2m'+1, m' = (A+6m)/2 = A/2+3m -- only if A even.
  -- This gets complicated. Let me use progress_nonhalt with a predicate.
  apply progress_nonhalt (fm := fm)
    (P := fun q ↦ ∃ A B, q = ⟨0, 0, A + B + 2, 0, A + 2 * B + 1⟩)
  · intro c ⟨A, B, hq⟩
    subst hq
    rcases Nat.even_or_odd B with ⟨m, hm⟩ | ⟨m, hm⟩
    · -- B = m + m (even)
      subst hm
      refine ⟨⟨0, 0, 2 * A + 6 * m + 4, 0, 3 * A + 12 * m + 4⟩,
        ⟨A + 1, A + 6 * m + 1, by ring_nf⟩, ?_⟩
      have : A + (m + m) + 2 = A + 2 * m + 2 := by ring
      have : A + 2 * (m + m) + 1 = A + 4 * m + 1 := by ring
      rw [show (0, 0, A + (m + m) + 2, 0, A + 2 * (m + m) + 1) =
            (0, 0, A + 2 * m + 2, 0, A + 4 * m + 1) from by simp [Prod.mk.injEq]; omega]
      exact main_trans_even A m
    · -- B = 2*m+1 (odd)
      subst hm
      refine ⟨⟨0, 0, 2 * A + 6 * m + 7, 0, 3 * A + 12 * m + 10⟩,
        ⟨A + 1, A + 6 * m + 4, by ring_nf⟩, ?_⟩
      rw [show (0, 0, A + (2 * m + 1) + 2, 0, A + 2 * (2 * m + 1) + 1) =
            (0, 0, A + 2 * m + 3, 0, A + 4 * m + 3) from by simp [Prod.mk.injEq]; omega]
      exact main_trans_odd A m
  · exact ⟨0, 0, by ring_nf⟩

end Sz22_2003_unofficial_889
