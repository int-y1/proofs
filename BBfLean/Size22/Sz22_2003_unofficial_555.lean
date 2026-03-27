import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #555: [308/15, 3/26, 35/2, 13/11, 33/7]

Vector representation:
```
 2 -1 -1  1  1  0
-1  1  0  0  0 -1
-1  0  1  1  0  0
 0  0  0  0 -1  1
 0  1  0 -1  1  0
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6

---

Canonical states are `(n+2, 0, 0, (2*n+1)*(n+1), 2*(n+1), 0)` for `n ≥ 0`.
Each transition decomposes into five phases:
1. R3 drain: transfer `a` to `c` and `d`
2. R4 drain: transfer `e` to `f`
3. Interleaved R5/(R1,R2): consume `c` and `f`, build `a` and `e`
4. R2 drain: transfer remaining `f` to `b`
5. R3/R1 chain: drain `b`, growing `a`, `d`, and `e`
-/

namespace Sz22_2003_unofficial_555

def Q := ℕ × ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a, b+1, c+1, d, e, f⟩ => some ⟨a+2, b, c, d+1, e+1, f⟩
  | ⟨a+1, b, c, d, e, f+1⟩ => some ⟨a, b+1, c, d, e, f⟩
  | ⟨a+1, b, c, d, e, f⟩ => some ⟨a, b, c+1, d+1, e, f⟩
  | ⟨a, b, c, d, e+1, f⟩ => some ⟨a, b, c, d, e, f+1⟩
  | ⟨a, b, c, d+1, e, f⟩ => some ⟨a, b+1, c, d, e+1, f⟩
  | _ => none

-- Phase 1: R3 repeated k times. (b=0, f=0 ensure R3 fires.)
theorem r3_drain : ⟨a+k, 0, c, d, e, 0⟩ [fm]⊢* ⟨a, 0, c+k, d+k, e, 0⟩ := by
  have many_step : ∀ k a c d, ⟨a+k, 0, c, d, e, 0⟩ [fm]⊢* ⟨a, 0, c+k, d+k, e, 0⟩ := by
    intro k; induction' k with k h <;> intro a c d
    · exists 0
    rw [← Nat.add_assoc]
    step fm
    apply stepStar_trans (h _ _ _)
    ring_nf; finish
  exact many_step k a c d

-- Phase 2: R4 repeated k times. (a=0, b=0 ensure R4 fires.)
theorem e_to_f : ⟨0, 0, c, d, e+k, f⟩ [fm]⊢* ⟨0, 0, c, d, e, f+k⟩ := by
  have many_step : ∀ k e f, ⟨0, 0, c, d, e+k, f⟩ [fm]⊢* ⟨0, 0, c, d, e, f+k⟩ := by
    intro k; induction' k with k h <;> intro e f
    · exists 0
    rw [← Nat.add_assoc]
    step fm
    apply stepStar_trans (h _ _)
    ring_nf; finish
  exact many_step k e f

-- Phase 3: Interleaved R1/R2 chain. Each round does R1 then R2.
theorem r1r2_chain : ⟨a, 1, c+k, d, e, f+k⟩ [fm]⊢* ⟨a+k, 1, c, d+k, e+k, f⟩ := by
  have many_step : ∀ k a d e, ⟨a, 1, c+k, d, e, f+k⟩ [fm]⊢* ⟨a+k, 1, c, d+k, e+k, f⟩ := by
    intro k; induction' k with k h <;> intro a d e
    · exists 0
    rw [show c + (k + 1) = (c + k) + 1 from by ring,
        show f + (k + 1) = (f + k) + 1 from by ring]
    step fm; step fm
    apply stepStar_trans (h _ _ _)
    ring_nf; finish
  exact many_step k a d e

-- Phase 4: R2 repeated k times. (c=0 ensures R1 doesn't fire.)
theorem r2_drain : ⟨a+k, b, 0, d, e, k⟩ [fm]⊢* ⟨a, b+k, 0, d, e, 0⟩ := by
  have many_step : ∀ k a b, ⟨a+k, b, 0, d, e, k⟩ [fm]⊢* ⟨a, b+k, 0, d, e, 0⟩ := by
    intro k; induction' k with k h <;> intro a b
    · exists 0
    rw [show a + (k + 1) = (a + k) + 1 from by ring]
    step fm
    apply stepStar_trans (h _ _)
    ring_nf; finish
  exact many_step k a b

-- Phase 5: R3/R1 chain. Each round does R3 then R1 (f=0, c becomes 1 then 0).
theorem r3r1_chain : ⟨a+1, b+k, 0, d, e, 0⟩ [fm]⊢* ⟨a+k+1, b, 0, d+2*k, e+k, 0⟩ := by
  have many_step : ∀ k a d e, ⟨a+1, b+k, 0, d, e, 0⟩ [fm]⊢* ⟨a+k+1, b, 0, d+2*k, e+k, 0⟩ := by
    intro k; induction' k with k h <;> intro a d e
    · exists 0
    rw [show b + (k + 1) = (b + k) + 1 from by ring]
    step fm; step fm
    apply stepStar_trans (h _ _ _)
    ring_nf; finish
  exact many_step k a d e

-- Compose all phases into the main transition: C(n) →⁺ C(n+1)
theorem main_trans (n : ℕ) :
    (⟨n+2, 0, 0, (2*n+1)*(n+1), 2*(n+1), 0⟩ : Q) [fm]⊢⁺
    ⟨n+3, 0, 0, (2*n+3)*(n+2), 2*(n+2), 0⟩ := by
  -- Phase 1: R3 × (n+2): (n+2, 0, 0, D, E, 0) →* (0, 0, n+2, D+(n+2), E, 0)
  have p1 := @r3_drain 0 (n+2) 0 ((2*n+1)*(n+1)) (2*(n+1))
  simp only [Nat.zero_add] at p1
  -- Phase 2: R4 × E: (0, 0, n+2, D', E, 0) →* (0, 0, n+2, D', 0, E)
  have p2 := @e_to_f (n+2) ((2*n+1)*(n+1)+(n+2)) 0 (2*(n+1)) 0
  simp only [Nat.zero_add] at p2
  -- Phase 3a: R5 step: (0, 0, n+2, D', 0, E) → (0, 1, n+2, D'-1, 1, E)
  have p3a : (⟨0, 0, n+2, (2*n+1)*(n+1)+(n+2), 0, 2*(n+1)⟩ : Q) [fm]⊢
      ⟨0, 1, n+2, (2*n+1)*(n+1)+(n+1), 1, 2*(n+1)⟩ := by
    show fm ⟨0, 0, n+2, (2*n+1)*(n+1)+(n+2), 0, 2*(n+1)⟩ = _
    rw [show (2*n+1)*(n+1)+(n+2) = ((2*n+1)*(n+1)+(n+1)) + 1 from by ring]
    rfl
  -- Phase 3b: R1/R2 × (n+2): consume c and f
  have p3b := @r1r2_chain 0 0 (n+2) ((2*n+1)*(n+1)+(n+1)) 1 n
  simp only [Nat.zero_add] at p3b
  -- Phase 4: R2 × n: drain remaining f to b
  have p4 := @r2_drain 2 n 1 ((2*n+1)*(n+1)+(n+1)+(n+2)) (n+3)
  -- Phase 5: R3/R1 × (n+1): drain b
  have p5 := @r3r1_chain 1 0 (n+1) ((2*n+1)*(n+1)+(n+1)+(n+2)) (n+3)
  simp only [Nat.zero_add] at p5
  -- Compose all phases
  apply stepStar_stepPlus_stepPlus p1
  apply stepStar_stepPlus_stepPlus p2
  apply step_stepStar_stepPlus p3a
  rw [show 2*(n+1) = n + (n+2) from by ring]
  refine stepStar_trans p3b ?_
  have h1 : (⟨n+2, 1, 0, (2*n+1)*(n+1)+(n+1)+(n+2), 1+(n+2), n⟩ : Q) =
      ⟨2+n, 1, 0, (2*n+1)*(n+1)+(n+1)+(n+2), n+3, n⟩ := by ring_nf
  rw [h1]; refine stepStar_trans p4 ?_
  have h2 : (⟨2, 1+n, 0, (2*n+1)*(n+1)+(n+1)+(n+2), n+3, 0⟩ : Q) =
      ⟨1+1, n+1, 0, (2*n+1)*(n+1)+(n+1)+(n+2), n+3, 0⟩ := by ring_nf
  rw [h2]; refine stepStar_trans p5 ?_
  ring_nf; finish

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨2, 0, 0, 1, 2, 0⟩)
  · execute fm 3
  apply progress_nonhalt_simple (fm := fm) (A := ℕ)
    (fun n ↦ ⟨n+2, 0, 0, (2*n+1)*(n+1), 2*(n+1), 0⟩) 0
  intro n; exists n+1
  exact main_trans n

end Sz22_2003_unofficial_555
