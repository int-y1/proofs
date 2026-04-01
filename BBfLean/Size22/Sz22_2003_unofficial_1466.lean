import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #1466: [7/15, 3/77, 50/7, 121/25, 21/2]

Vector representation:
```
 0 -1 -1  1  0
 0  1  0 -1 -1
 1  0  2 -1  0
 0  0 -2  0  2
-1  1  0  1  0
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_1466

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a, b+1, c+1, d, e⟩ => some ⟨a, b, c, d+1, e⟩
  | ⟨a, b, c, d+1, e+1⟩ => some ⟨a, b+1, c, d, e⟩
  | ⟨a, b, c, d+1, e⟩ => some ⟨a+1, b, c+2, d, e⟩
  | ⟨a, b, c+2, d, e⟩ => some ⟨a, b, c, d, e+2⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b+1, c, d+1, e⟩
  | _ => none

-- R3 step with c=0 and e=0 (step fm can't handle symbolic b).
theorem r3_step_c0 (a b d : ℕ) :
    ⟨a, b, 0, d + 1, 0⟩ [fm]⊢ ⟨a + 1, b, 2, d, 0⟩ := by
  show fm ⟨a, b, 0, d + 1, 0⟩ = some ⟨a + 1, b, 2, d, 0⟩
  simp [fm]

-- R5 step with symbolic b (step fm can't handle symbolic b).
theorem r5_step (a b : ℕ) :
    ⟨a + 1, b, 0, 0, 0⟩ [fm]⊢ ⟨a, b + 1, 0, 1, 0⟩ := by
  show fm ⟨a + 1, b, 0, 0, 0⟩ = some ⟨a, b + 1, 0, 1, 0⟩
  simp [fm]

-- R1,R1,R3 chain: each round b-=2, a+=1, d+=1, c stays at 2.
theorem r1r1r3_chain : ∀ k, ∀ a b d,
    ⟨a, b + 2 * k, 2, d, 0⟩ [fm]⊢* ⟨a + k, b, 2, d + k, 0⟩ := by
  intro k; induction' k with k ih <;> intro a b d
  · exists 0
  · rw [show b + 2 * (k + 1) = (b + 2 * k) + 1 + 1 from by ring]
    step fm; step fm
    -- Now at (a, b + 2*k, 0, d+2, 0). Need R3 with symbolic b+2*k.
    rw [show d + 2 = (d + 1) + 1 from by ring]
    apply stepStar_trans (step_stepStar (r3_step_c0 a (b + 2 * k) (d + 1)))
    apply stepStar_trans (ih (a + 1) b (d + 1)); ring_nf; finish

-- R3 chain: drains d when b=0. Use (k+d) form to avoid 0+k issues.
theorem r3_chain : ∀ k, ∀ a c d,
    ⟨a, 0, c, k + d, 0⟩ [fm]⊢* ⟨a + k, 0, c + 2 * k, d, 0⟩ := by
  intro k; induction' k with k ih <;> intro a c d
  · ring_nf; finish
  · rw [show k + 1 + d = (k + d) + 1 from by ring]
    step fm
    apply stepStar_trans (ih (a + 1) (c + 2) d); ring_nf; finish

-- R4 chain: converts pairs of c to pairs of e.
theorem r4_chain : ∀ k, ∀ a c e,
    ⟨a, 0, c + 2 * k, 0, e⟩ [fm]⊢* ⟨a, 0, c, 0, e + 2 * k⟩ := by
  intro k; induction' k with k ih <;> intro a c e
  · exists 0
  · rw [show c + 2 * (k + 1) = (c + 2 * k) + 2 from by ring]
    step fm
    apply stepStar_trans (ih a c (e + 2)); ring_nf; finish

-- R5,R2 chain: each round a-=1, e-=1, b+=2. Use (k+a), (k+e) form.
theorem r5r2_chain : ∀ k, ∀ a b e,
    ⟨k + a, b, 0, 0, k + e⟩ [fm]⊢* ⟨a, b + 2 * k, 0, 0, e⟩ := by
  intro k; induction' k with k ih <;> intro a b e
  · ring_nf; finish
  · rw [show k + 1 + a = (k + a) + 1 from by ring,
        show k + 1 + e = (k + e) + 1 from by ring]
    step fm; step fm
    apply stepStar_trans (ih a (b + 2) e); ring_nf; finish

-- Main transition: (1, 2*n, 0, 0, 0) ⊢⁺ (1, 2*(2*n+1), 0, 0, 0)
theorem main_trans (n : ℕ) :
    ⟨1, 2 * n, 0, 0, 0⟩ [fm]⊢⁺ ⟨1, 2 * (2 * n + 1), 0, 0, 0⟩ := by
  -- Phase 1: R5. (1, 2n, 0, 0, 0) -> (0, 2n+1, 0, 1, 0)
  rw [show (1 : ℕ) = 0 + 1 from by ring]
  apply step_stepStar_stepPlus (r5_step 0 (2 * n))
  -- Phase 2: R3. (0, 2n+1, 0, 1, 0) -> (1, 2n+1, 2, 0, 0)
  step fm
  -- Phase 3a: n rounds of R1,R1,R3.
  -- (1, 2n+1, 2, 0, 0) = (1, 1+2*n, 2, 0, 0) ⊢* (1+n, 1, 2, 0+n, 0)
  rw [show 2 * n + 1 = 1 + 2 * n from by ring]
  apply stepStar_trans (r1r1r3_chain n 1 1 0)
  -- (n+1, 1, 2, n, 0)
  rw [show 1 + n = n + 1 from by ring,
      show 0 + n = n from by ring]
  -- Phase 3b-prep: one R1 step. (n+1, 1, 2, n, 0) -> (n+1, 0, 1, n+1, 0)
  step fm
  -- Phase 3b: R3 chain draining d=n+1.
  -- (n+1, 0, 1, n+1, 0) ⊢* (2n+2, 0, 2n+3, 0, 0)
  apply stepStar_trans (r3_chain (n + 1) (n + 1) 1 0)
  -- Phase 4: R4 chain.
  -- (2n+2, 0, 1+2*(n+1), 0, 0) ⊢* (2n+2, 0, 1, 0, 2*(n+1))
  apply stepStar_trans (r4_chain (n + 1) (n + 1 + (n + 1)) 1 0)
  -- Phase 5: R5 then R1.
  -- (2n+2, 0, 1, 0, 2n+2) -> (2n+1, 1, 1, 1, 2n+2) -> (2n+1, 0, 0, 2, 2n+2)
  rw [show n + 1 + (n + 1) = (2 * n + 1) + 1 from by ring,
      show 0 + 2 * (n + 1) = (2 * n + 1) + 1 from by ring]
  step fm; step fm
  -- Phase 6a: two R2 steps.
  -- (2n+1, 0, 0, 2, 2n+2) -> (2n+1, 1, 0, 1, 2n+1) -> (2n+1, 2, 0, 0, 2n)
  rw [show (2 : ℕ) = 0 + 1 + 1 from by ring,
      show (2 * n + 1) + 1 = (2 * n + 1) + 1 from by ring]
  step fm
  rw [show 2 * n + 1 = (2 * n) + 1 from by ring]
  step fm
  -- Phase 6b: R5,R2 chain.
  -- (2n+1, 2, 0, 0, 2n) ⊢* (1, 2+4n, 0, 0, 0)
  apply stepStar_trans (r5r2_chain (2 * n) 1 2 0)
  ring_nf; finish

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨1, 0, 0, 0, 0⟩) (by execute fm 0)
  apply progress_nonhalt_simple (fm := fm) (A := ℕ)
    (fun n ↦ ⟨1, 2 * n, 0, 0, 0⟩) 0
  intro n; exact ⟨2 * n + 1, main_trans n⟩

end Sz22_2003_unofficial_1466
