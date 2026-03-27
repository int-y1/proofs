import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #514: [28/15, 3/22, 65/2, 11/7, 33/13]

Vector representation:
```
 2 -1 -1  1  0  0
-1  1  0  0 -1  0
-1  0  1  0  0  1
 0  0  0 -1  1  0
 0  1  0  0  1 -1
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_514

def Q := ℕ × ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a, b+1, c+1, d, e, f⟩ => some ⟨a+2, b, c, d+1, e, f⟩
  | ⟨a+1, b, c, d, e+1, f⟩ => some ⟨a, b+1, c, d, e, f⟩
  | ⟨a+1, b, c, d, e, f⟩ => some ⟨a, b, c+1, d, e, f+1⟩
  | ⟨a, b, c, d+1, e, f⟩ => some ⟨a, b, c, d, e+1, f⟩
  | ⟨a, b, c, d, e, f+1⟩ => some ⟨a, b+1, c, d, e+1, f⟩
  | _ => none

-- Explicit step lemmas
theorem step_r5 : ⟨0, 0, c, 0, e, f+1⟩ [fm]⊢* ⟨0, 1, c, 0, e+1, f⟩ := by
  exists 1; rcases e with _ | e <;> rfl

theorem step_r1_11 : ⟨a, 1, 1, d, e, f⟩ [fm]⊢* ⟨a+2, 0, 0, d+1, e, f⟩ := by
  exists 1

theorem step_r3_c0 : ⟨a+1, b, 0, d, 0, f⟩ [fm]⊢* ⟨a, b, 1, d, 0, f+1⟩ := by
  exists 1; rcases b with _ | b <;> rfl

-- R3 repeated
theorem a_to_cf : ∀ k c f, ⟨a+k, 0, c, d, 0, f⟩ [fm]⊢* ⟨a, 0, c+k, d, 0, f+k⟩ := by
  intro k; induction' k with k h <;> intro c f
  · exists 0
  rw [← Nat.add_assoc]; step fm
  apply stepStar_trans (h _ _); ring_nf; finish

-- R4 repeated
theorem d_to_e : ∀ k d e, ⟨0, 0, c, d+k, e, f⟩ [fm]⊢* ⟨0, 0, c, d, e+k, f⟩ := by
  intro k; induction' k with k h <;> intro d e
  · exists 0
  rw [← Nat.add_assoc]; step fm
  apply stepStar_trans (h _ _); ring_nf; finish

-- R2 repeated
theorem r2_chain : ∀ k a b, ⟨a+k, b, 0, d, k, f⟩ [fm]⊢* ⟨a, b+k, 0, d, 0, f⟩ := by
  intro k; induction' k with k h <;> intro a b
  · exists 0
  rw [← Nat.add_assoc]; step fm
  apply stepStar_trans (h _ _); ring_nf; finish

-- (R1,R2) two-step
theorem r1r2_step : ⟨a, 1, c+1, d, e+1, f⟩ [fm]⊢* ⟨a+1, 1, c, d+1, e, f⟩ := by
  step fm; step fm; finish

-- (R1,R2) chain
theorem r1r2_chain : ∀ k a c d e,
    ⟨a, 1, c+k, d, e+k, f⟩ [fm]⊢* ⟨a+k, 1, c, d+k, e, f⟩ := by
  intro k; induction' k with k h <;> intro a c d e
  · exists 0
  rw [show c + (k + 1) = (c + k) + 1 from by ring,
      show e + (k + 1) = (e + k) + 1 from by ring]
  apply stepStar_trans (r1r2_step (a := a) (c := c+k) (d := d) (e := e+k) (f := f))
  apply stepStar_trans (h (a+1) c (d+1) e); ring_nf; finish

-- (R1,R3) two-step
theorem r1r3_step : ⟨a, b+1, 1, d, 0, f⟩ [fm]⊢* ⟨a+1, b, 1, d+1, 0, f+1⟩ := by
  step fm; step fm; finish

-- (R1,R3) chain
theorem r1r3_chain : ∀ k a b d f,
    ⟨a, b+k, 1, d, 0, f⟩ [fm]⊢* ⟨a+k, b, 1, d+k, 0, f+k⟩ := by
  intro k; induction' k with k h <;> intro a b d f
  · exists 0
  rw [show b + (k + 1) = (b + k) + 1 from by ring]
  apply stepStar_trans (r1r3_step (a := a) (b := b+k) (d := d) (f := f))
  apply stepStar_trans (h (a+1) b (d+1) (f+1)); ring_nf; finish

-- The full ⊢* transition using a single lemma to avoid rw pollution
theorem full_star (n : ℕ) :
    (⟨n+1, 0, 0, 2*n, 0, n*n⟩ : Q) [fm]⊢* ⟨n+2, 0, 0, 2*(n+1), 0, (n+1)*(n+1)⟩ := by
  -- R3^(n+1)
  have h1 := a_to_cf (a := 0) (k := n+1) (c := 0) (d := 2*n) (f := n*n)
  simp only [Nat.zero_add] at h1; refine stepStar_trans h1 ?_
  -- R4^(2n)
  have h2 := d_to_e (c := n+1) (k := 2*n) (d := 0) (e := 0) (f := n*n + (n+1))
  simp only [Nat.zero_add] at h2; refine stepStar_trans h2 ?_
  -- R5
  rw [show n * n + (n + 1) = n * n + n + 1 from by ring]
  refine stepStar_trans (step_r5 (c := n+1) (e := 2*n) (f := n*n+n)) ?_
  -- (R1,R2)^n
  have h3 := r1r2_chain (a := 0) (k := n) (c := 1) (d := 0) (e := n+1) (f := n*n+n)
  simp only [Nat.zero_add] at h3
  have h3' : (⟨0, 1, n+1, 0, 2*n+1, n*n+n⟩ : Q) [fm]⊢* ⟨n, 1, 1, n, n+1, n*n+n⟩ := by
    convert h3 using 2; ring_nf
  refine stepStar_trans h3' ?_
  -- R1 (b=1, c=1)
  refine stepStar_trans (step_r1_11 (a := n) (d := n) (e := n+1) (f := n*n+n)) ?_
  -- R2^(n+1)
  have h4 := r2_chain (a := 1) (k := n+1) (b := 0) (d := n+1) (f := n*n+n)
  simp only [Nat.zero_add] at h4
  have h4' : (⟨n+2, 0, 0, n+1, n+1, n*n+n⟩ : Q) [fm]⊢* ⟨1, n+1, 0, n+1, 0, n*n+n⟩ := by
    convert h4 using 2; ring_nf
  refine stepStar_trans h4' ?_
  -- R3
  refine stepStar_trans (step_r3_c0 (a := 0) (b := n+1) (d := n+1) (f := n*n+n)) ?_
  -- (R1,R3)^n
  have h5 := r1r3_chain (k := n) (a := 0) (b := 1) (d := n+1) (f := n*n+n+1)
  simp only [Nat.zero_add] at h5
  -- h5 has 1+n in pos 2, goal has n+1. Fix with targeted rw.
  have h5' : (⟨0, n+1, 1, n+1, 0, n*n+n+1⟩ : Q) [fm]⊢* ⟨n, 1, 1, n+1+n, 0, n*n+n+1+n⟩ := by
    convert h5 using 2; ring_nf
  refine stepStar_trans h5' ?_
  -- R1 (b=1, c=1)
  have h6 : (⟨n, 1, 1, n+1+n, 0, n*n+n+1+n⟩ : Q) [fm]⊢* ⟨n+2, 0, 0, 2*(n+1), 0, (n+1)*(n+1)⟩ := by
    have := step_r1_11 (a := n) (d := n+1+n) (e := 0) (f := n*n+n+1+n)
    convert this using 2; ring_nf
  exact h6

theorem main_trans (n : ℕ) :
    (⟨n+1, 0, 0, 2*n, 0, n*n⟩ : Q) [fm]⊢⁺ ⟨n+2, 0, 0, 2*(n+1), 0, (n+1)*(n+1)⟩ := by
  apply stepStar_stepPlus (full_star n)
  intro h; injection h with h1; omega

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨2, 0, 0, 2, 0, 1⟩)
  · execute fm 6
  apply progress_nonhalt_simple (fm := fm) (A := ℕ)
    (fun n ↦ ⟨n+2, 0, 0, 2*(n+1), 0, (n+1)*(n+1)⟩) 0
  intro n
  exact ⟨n+1, main_trans (n+1)⟩
