import BBfLean.FM
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

/-!
# sz22_2003_unofficial #457: [28/15, 11/3, 9/2, 5/847, 14/11]

Vector representation:
```
 2 -1 -1  1  0
 0 -1  0  0  1
-1  2  0  0  0
 0  0  1 -1 -2
 1  0  0  1 -1
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_457

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a, b+1, c+1, d, e⟩ => some ⟨a+2, b, c, d+1, e⟩
  | ⟨a, b+1, c, d, e⟩ => some ⟨a, b, c, d, e+1⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b+2, c, d, e⟩
  | ⟨a, b, c, d+1, e+2⟩ => some ⟨a, b, c+1, d, e⟩
  | ⟨a, b, c, d, e+1⟩ => some ⟨a+1, b, c, d+1, e⟩
  | _ => none

-- R4 chain + R5 + R3 combined
theorem phase1 : ∀ k, ∀ c e, ⟨0, 0, c, k, e + 2 * k + 1⟩ [fm]⊢* ⟨0, 2, c + k, 1, e⟩ := by
  intro k; induction' k with k ih <;> intro c e
  · rw [show e + 2 * 0 + 1 = e + 1 from by ring]
    step fm; step fm; ring_nf; finish
  · rw [show e + 2 * (k + 1) + 1 = (e + 2 * k + 1) + 2 from by ring,
        show (k + 1 : ℕ) = k + 1 from rfl]
    step fm
    apply stepStar_trans (ih _ _)
    ring_nf; finish

-- R3/R2/R2 chain
theorem drain_a : ∀ k, ∀ d e, ⟨k, 0, 0, d, e⟩ [fm]⊢* ⟨0, 0, 0, d, e + 2 * k⟩ := by
  intro k; induction' k with k ih <;> intro d e
  · exists 0
  rw [show k + 1 = k + 1 from rfl]
  step fm; step fm; step fm
  apply stepStar_trans (ih _ _)
  ring_nf; finish

-- R1/R1/R3 chain with odd exit (c=1 remaining): R1 then R2
-- Combined: (a, 2, 1+2k, d, e) ⊢* (a+3k+2, 0, 0, d+2k+1, e+1)
theorem r1r1r3_odd_exit : ∀ k, ∀ a d e,
    ⟨a, 2, 1 + 2 * k, d, e⟩ [fm]⊢* ⟨a + 3 * k + 2, 0, 0, d + 2 * k + 1, e + 1⟩ := by
  intro k; induction' k with k ih <;> intro a d e
  · -- k=0: (a, 2, 1, d, e) -> R1 -> (a+2, 1, 0, d+1, e) -> R2 -> (a+2, 0, 0, d+1, e+1)
    step fm; step fm; ring_nf; finish
  · -- k+1: (a, 2, 1+2(k+1), d, e) = (a, 2, (1+2k)+1+1, d, e)
    rw [show 1 + 2 * (k + 1) = (1 + 2 * k) + 1 + 1 from by ring]
    step fm  -- R1: (a+2, 1, (1+2k)+1, d+1, e)
    step fm  -- R1: (a+4, 0, 1+2k, d+2, e)
    rw [show a + 2 + 2 = (a + 2 + 1) + 1 from by ring]
    step fm  -- R3: (a+3, 2, 1+2k, d+2, e)
    apply stepStar_trans (ih _ _ _)
    ring_nf; finish

-- R1/R1/R3 chain with even exit (c=0 remaining): R2 then R2
-- Combined: (a, 2, 2k, d, e) ⊢* (a+3k, 0, 0, d+2k, e+2)
theorem r1r1r3_even_exit : ∀ k, ∀ a d e,
    ⟨a, 2, 2 * k, d, e⟩ [fm]⊢* ⟨a + 3 * k, 0, 0, d + 2 * k, e + 2⟩ := by
  intro k; induction' k with k ih <;> intro a d e
  · -- k=0: (a, 2, 0, d, e) -> R2 -> (a, 1, 0, d, e+1) -> R2 -> (a, 0, 0, d, e+2)
    step fm; step fm; ring_nf; finish
  · -- k+1: (a, 2, 2(k+1), d, e) = (a, 2, 2k+1+1, d, e)
    rw [show 2 * (k + 1) = 2 * k + 1 + 1 from by ring]
    step fm  -- R1: (a+2, 1, 2k+1, d+1, e)
    rw [show 2 * k + 1 = 2 * k + 1 from rfl]
    step fm  -- R1: (a+4, 0, 2k, d+2, e)
    rw [show a + 2 + 2 = (a + 2 + 1) + 1 from by ring]
    step fm  -- R3: (a+3, 2, 2k, d+2, e)
    apply stepStar_trans (ih _ _ _)
    ring_nf; finish

-- Arithmetic helpers
private lemma two_n_sq_ge_n (n : ℕ) : 2 * n * n ≥ n := by
  rcases n with _ | n
  · omega
  · nlinarith [Nat.zero_le n]

private lemma arith_odd_phase1 (n : ℕ) :
    2 * n * n - n + 2 * (2 * n + 1) + 1 = 2 * n * n + 3 * n + 3 := by
  have h := two_n_sq_ge_n n; omega

private lemma arith_odd_total (n : ℕ) :
    2 * n * n - n + 1 + 2 * (3 * n + 2) = 2 * n * n + 5 * n + 5 := by
  have h := two_n_sq_ge_n n; omega

-- Full odd-to-even transition as ⊢*
theorem odd_to_even_star (n : ℕ) :
    ⟨0, 0, 0, 2*n+1, 2*n*n+3*n+3⟩ [fm]⊢* ⟨0, 0, 0, 2*n+2, 2*n*n+5*n+5⟩ := by
  -- Phase 1: phase1 (2n+1) 0 (2n²-n)
  apply stepStar_trans (c₂ := ⟨0, 2, 2*n+1, 1, 2*n*n - n⟩)
  · have h := phase1 (2*n+1) 0 (2*n*n - n)
    simp only [Nat.zero_add] at h; rw [arith_odd_phase1 n] at h; exact h
  -- Phase 2: r1r1r3_odd_exit n 0 1 (2n²-n)
  apply stepStar_trans (c₂ := ⟨3*n+2, 0, 0, 2*n+2, 2*n*n - n + 1⟩)
  · have h := r1r1r3_odd_exit n 0 1 (2*n*n - n)
    simp only [Nat.zero_add,
               show 1 + 2*n = 2*n+1 from by ring] at h
    exact h
  -- Phase 3: drain_a (3n+2) (2n+2) (2n²-n+1)
  have h := drain_a (3*n+2) (2*n+2) (2*n*n - n + 1)
  rw [arith_odd_total n] at h; exact h

-- Full even-to-odd transition as ⊢*
theorem even_to_odd_star (n : ℕ) :
    ⟨0, 0, 0, 2*n+2, 2*n*n+5*n+5⟩ [fm]⊢* ⟨0, 0, 0, 2*n+3, 2*n*n+7*n+8⟩ := by
  -- Phase 1: phase1 (2n+2) 0 (2n²+n)
  apply stepStar_trans (c₂ := ⟨0, 2, 2*n+2, 1, 2*n*n+n⟩)
  · have h := phase1 (2*n+2) 0 (2*n*n+n)
    simp only [Nat.zero_add] at h
    rw [show 2*n*n + n + 2*(2*n+2) + 1 = 2*n*n+5*n+5 from by ring] at h; exact h
  -- Phase 2: r1r1r3_even_exit (n+1) 0 1 (2n²+n)
  apply stepStar_trans (c₂ := ⟨3*n+3, 0, 0, 2*n+3, 2*n*n+n+2⟩)
  · have h := r1r1r3_even_exit (n+1) 0 1 (2*n*n+n)
    simp only [Nat.zero_add,
               show 2*(n+1) = 2*n+2 from by ring,
               show 3*(n+1) = 3*n+3 from by ring] at h
    rw [show 1 + (2*n+2) = 2*n+3 from by ring] at h; exact h
  -- Phase 3: drain_a (3n+3) (2n+3) (2n²+n+2)
  have h := drain_a (3*n+3) (2*n+3) (2*n*n+n+2)
  rw [show 2*n*n+n+2+2*(3*n+3) = 2*n*n+7*n+8 from by ring] at h; exact h

-- Main transition: compose and convert ⊢* to ⊢⁺ (since d changes)
theorem main_trans (n : ℕ) :
    ⟨0, 0, 0, 2*n+1, 2*n*n+3*n+3⟩ [fm]⊢⁺ ⟨0, 0, 0, 2*n+3, 2*n*n+7*n+8⟩ := by
  have h := stepStar_trans (odd_to_even_star n) (even_to_odd_star n)
  refine stepStar_stepPlus h ?_
  intro heq
  have h4 := congr_arg Prod.snd (congr_arg Prod.snd (congr_arg Prod.snd heq))
  simp at h4

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨0, 0, 0, 1, 3⟩) (by execute fm 7)
  apply progress_nonhalt_simple (fm := fm) (A := ℕ)
    (fun n ↦ ⟨0, 0, 0, 2*n+1, 2*n*n+3*n+3⟩) 0
  intro n; exists n + 1
  show ⟨0, 0, 0, 2*n+1, 2*n*n+3*n+3⟩ [fm]⊢⁺ ⟨0, 0, 0, 2*(n+1)+1, 2*(n+1)*(n+1)+3*(n+1)+3⟩
  rw [show 2*(n+1)+1 = 2*n+3 from by ring,
      show 2*(n+1)*(n+1)+3*(n+1)+3 = 2*n*n+7*n+8 from by ring]
  exact main_trans n

end Sz22_2003_unofficial_457
