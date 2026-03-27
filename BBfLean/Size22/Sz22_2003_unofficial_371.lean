import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #371: [2/15, 9/14, 1375/2, 7/25, 2/11]

Vector representation:
```
 1 -1 -1  0  0
-1  2  0 -1  0
-1  0  3  0  1
 0  0 -2  1  0
 1  0  0  0 -1
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_371

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a, b+1, c+1, d, e⟩ => some ⟨a+1, b, c, d, e⟩
  | ⟨a+1, b, c, d+1, e⟩ => some ⟨a, b+2, c, d, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b, c+3, d, e+1⟩
  | ⟨a, b, c+2, d, e⟩ => some ⟨a, b, c, d+1, e⟩
  | ⟨a, b, c, d, e+1⟩ => some ⟨a+1, b, c, d, e⟩
  | _ => none

-- R1 chain: k applications of rule 1
theorem r1_chain : ∀ k a b c d e, ⟨a, b+k, c+k, d, e⟩ [fm]⊢* ⟨a+k, b, c, d, e⟩ := by
  intro k; induction k with
  | zero => intro a b c d e; exists 0
  | succ k ih =>
    intro a b c d e
    rw [show b + (k + 1) = (b + k) + 1 from by ring,
        show c + (k + 1) = (c + k) + 1 from by ring]
    step fm
    apply stepStar_trans (ih _ _ _ _ _)
    ring_nf; finish

-- R3 chain: k applications of rule 3 (when b=0, d=0)
theorem r3_chain : ∀ k a c e, ⟨a+k, 0, c, 0, e⟩ [fm]⊢* ⟨a, 0, c+3*k, 0, e+k⟩ := by
  intro k; induction k with
  | zero => intro a c e; exists 0
  | succ k ih =>
    intro a c e
    rw [show a + (k + 1) = (a + k) + 1 from by ring]
    step fm
    apply stepStar_trans (ih _ _ _)
    ring_nf; finish

-- R4 chain: k applications of rule 4
theorem r4_chain : ∀ k c d e, ⟨0, 0, c+2*k, d, e⟩ [fm]⊢* ⟨0, 0, c, d+k, e⟩ := by
  intro k; induction k with
  | zero => intro c d e; exists 0
  | succ k ih =>
    intro c d e
    rw [show c + 2 * (k + 1) = (c + 2 * k) + 2 from by ring]
    step fm
    apply stepStar_trans (ih _ _ _)
    ring_nf; finish

-- Tail loop: alternating R2, R5 to convert d,e pairs into b
theorem tail_loop : ∀ k b d e, ⟨1, b, 0, d+k, e+k⟩ [fm]⊢* ⟨1, b+2*k, 0, d, e⟩ := by
  intro k; induction k with
  | zero => intro b d e; exists 0
  | succ k ih =>
    intro b d e
    rw [show d + (k + 1) = (d + k) + 1 from by ring,
        show e + (k + 1) = (e + k) + 1 from by ring]
    step fm  -- R2: (0, b+2, 0, d+k, e+k+1)
    step fm  -- R5: (1, b+2, 0, d+k, e+k)
    apply stepStar_trans (ih _ _ _)
    ring_nf; finish

-- Phase A: convert (a+1, b, 0, 0, e) to (0, 0, 3*(a+1)+2*b, 0, e+a+1+b)
-- by strong induction on b
theorem phase_a : ∀ b, ∀ a e, ⟨a+1, b, 0, 0, e⟩ [fm]⊢* ⟨0, 0, 3*(a+1)+2*b, 0, e+a+1+b⟩ := by
  intro b; induction' b using Nat.strongRecOn with b ih; intro a e
  rcases b with _ | _ | _ | b
  · -- b=0: R3 chain
    have h := r3_chain (a+1) 0 0 e
    simp only [Nat.zero_add] at h
    simp only [(by omega : 3 * (a + 1) + 2 * 0 = 3 * (a + 1)),
               (by omega : e + a + 1 + 0 = e + (a + 1))]
    exact h
  · -- b=1: R3, R1, then R3 chain
    step fm
    step fm
    have h := r3_chain (a+1) 0 2 (e+1)
    simp only [Nat.zero_add] at h
    apply stepStar_trans h
    ring_nf; finish
  · -- b=2: R3, R1, R1, then R3 chain
    step fm
    step fm
    step fm
    have h := r3_chain (a+2) 0 1 (e+1)
    simp only [Nat.zero_add] at h
    apply stepStar_trans h
    ring_nf; finish
  · -- b=b+3: R3, R1x3, then IH
    step fm
    step fm
    step fm
    step fm
    have h := ih b (by omega) (a+2) (e+1)
    simp only [(by ring : (a + 2) + 1 = a + 3)] at h
    apply stepStar_trans h
    ring_nf; finish

-- Tail: from (0, 0, 1, m+1, m+1) reach (1, 2*m+1, 0, 0, 0)
theorem tail (m : ℕ) : ⟨0, 0, 1, m+1, m+1⟩ [fm]⊢* ⟨1, 2*m+1, 0, 0, 0⟩ := by
  step fm  -- R5: (1, 0, 1, m+1, m)
  step fm  -- R2: (0, 2, 1, m, m)
  step fm  -- R1: (1, 1, 0, m, m)
  have h := tail_loop m 1 0 0
  simp only [Nat.zero_add] at h
  apply stepStar_trans h
  ring_nf; finish

-- Main transition: (1, n, 0, 0, 0) ⊢⁺ (1, 2*n+1, 0, 0, 0)
theorem main_trans (n : ℕ) : ⟨1, n, 0, 0, 0⟩ [fm]⊢⁺ ⟨1, 2*n+1, 0, 0, 0⟩ := by
  apply stepStar_stepPlus_stepPlus
  · -- Phase A: (1, n, 0, 0, 0) ⊢* (0, 0, 2*n+3, 0, n+1)
    have h := phase_a n 0 0
    simp only [Nat.zero_add, (by ring : 0 + 1 = 1)] at h
    simp only [(by ring : 3 * 1 + 2 * n = 2 * n + 3),
               (by ring : 0 + 0 + 1 + n = n + 1)] at h
    exact h
  apply stepStar_stepPlus_stepPlus
  · -- Phase B: R4 chain: (0, 0, 2*n+3, 0, n+1) ⊢* (0, 0, 1, n+1, n+1)
    have h := r4_chain (n+1) 1 0 (n+1)
    simp only [Nat.zero_add, (by ring : 1 + 2 * (n + 1) = 2 * n + 3)] at h
    exact h
  -- Phase C: tail
  apply step_stepStar_stepPlus
  · -- First step of tail (R5)
    show fm ⟨0, 0, 1, n + 1, n + 1⟩ = some ⟨1, 0, 1, n + 1, n⟩
    simp [fm]
  -- Rest of tail
  step fm  -- R2: (0, 2, 1, n, n)
  step fm  -- R1: (1, 1, 0, n, n)
  have h := tail_loop n 1 0 0
  simp only [Nat.zero_add] at h
  apply stepStar_trans h
  ring_nf; finish

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨1, 0, 0, 0, 0⟩) (by exists 0)
  exact progress_nonhalt_simple (fm := fm) (fun n ↦ ⟨1, n, 0, 0, 0⟩) 0
    (fun n ↦ ⟨2*n+1, main_trans n⟩)

end Sz22_2003_unofficial_371
