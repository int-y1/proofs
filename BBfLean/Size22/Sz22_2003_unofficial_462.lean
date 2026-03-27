import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #462: [28/15, 21/22, 125/2, 11/7, 3/5]

Vector representation:
```
 2 -1 -1  1  0
-1  1  0  1 -1
-1  0  3  0  0
 0  0  0 -1  1
 0  1 -1  0  0
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_462

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a, b+1, c+1, d, e⟩ => some ⟨a+2, b, c, d+1, e⟩
  | ⟨a+1, b, c, d, e+1⟩ => some ⟨a, b+1, c, d+1, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b, c+3, d, e⟩
  | ⟨a, b, c, d+1, e⟩ => some ⟨a, b, c, d, e+1⟩
  | ⟨a, b, c+1, d, e⟩ => some ⟨a, b+1, c, d, e⟩
  | _ => none

-- R4 chain: d to e (a=0, b=0, e=0)
theorem d_to_e (c : ℕ) : ∀ k d, ⟨0, 0, c, d + k, 0⟩ [fm]⊢* ⟨0, 0, c, d, k⟩ := by
  intro k; induction k with
  | zero => intro d; exists 0
  | succ k ih =>
    intro d
    rw [show d + (k + 1) = (d + 1) + k from by ring]
    apply stepStar_trans (ih (d + 1))
    step fm; finish

-- R3 chain: a to c (b=0, e=0)
theorem a_to_c (d : ℕ) : ∀ k a c, ⟨a + k, 0, c, d, 0⟩ [fm]⊢* ⟨a, 0, c + 3 * k, d, 0⟩ := by
  intro k; induction k with
  | zero => intro a c; exists 0
  | succ k ih =>
    intro a c
    rw [show a + (k + 1) = (a + k) + 1 from by ring]
    step fm
    apply stepStar_trans (ih a (c + 3))
    ring_nf; finish

-- R2+R1 interleaved chain: each round a increases by 1, c decreases by 1, d increases by 2, e decreases by 1
-- (a+1, 0, c+k, d, k) ⊢* (a+k+1, 0, c, d+2*k, 0)
theorem r2r1_chain : ∀ k a c d, ⟨a + 1, 0, c + k, d, k⟩ [fm]⊢* ⟨a + k + 1, 0, c, d + 2 * k, 0⟩ := by
  intro k; induction k with
  | zero => intro a c d; exists 0
  | succ k ih =>
    intro a c d
    rw [show c + (k + 1) = (c + k) + 1 from by ring]
    step fm  -- R2: (a+1, 0, (c+k)+1, d, k+1) -> (a, 1, (c+k)+1, d+1, k)
    step fm  -- R1: (a, 1, (c+k)+1, d+1, k) -> (a+2, 0, c+k, d+2, k)
    rw [show a + 2 = (a + 1) + 1 from by ring,
        show d + 1 + 1 = d + 2 from by ring]
    apply stepStar_trans (ih (a + 1) c (d + 2))
    ring_nf; finish

-- Main transition: (0, 0, n+e+3, 0, e) ⊢⁺ (0, 0, n+3*e+7, 0, 2*e+1)
theorem main_trans (n e : ℕ) :
    ⟨0, 0, n + e + 3, 0, e⟩ [fm]⊢⁺ ⟨0, 0, n + 3 * e + 7, 0, 2 * e + 1⟩ := by
  -- Phase 1+2: R5 then R1 (2 steps)
  rw [show n + e + 3 = (n + 1 + e) + 1 + 1 from by ring]
  step fm  -- R5: (0, 1, (n+1+e)+1, 0, e)
  step fm  -- R1: (2, 0, n+1+e, 1, e)
  -- State: (2, 0, n+1+e, 1, e) = (1+1, 0, (n+1)+e, 1, e)
  -- Phase 3: R2,R1 chain (e rounds)
  rw [show (2 : ℕ) = 1 + 1 from by ring,
      show n + 1 + e = (n + 1) + e from by ring]
  apply stepStar_trans (r2r1_chain e 1 (n + 1) 1)
  -- State: (1+e+1, 0, n+1, 1+2*e, 0) = (e+2, 0, n+1, 2*e+1, 0)
  -- Phase 4: R3 chain (e+2 times)
  rw [show 1 + e + 1 = 0 + (e + 2) from by ring,
      show 1 + 2 * e = 2 * e + 1 from by ring]
  apply stepStar_trans (a_to_c (2 * e + 1) (e + 2) 0 (n + 1))
  -- State: (0, 0, n+1+3*(e+2), 2*e+1, 0)
  -- Phase 5: R4 chain (2*e+1 times)
  rw [show 2 * e + 1 = 0 + (2 * e + 1) from by ring]
  apply stepStar_trans (d_to_e (n + 1 + 3 * (e + 2)) (2 * e + 1) 0)
  ring_nf; finish

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨0, 0, 3, 0, 0⟩) (by execute fm 1)
  apply progress_nonhalt_simple (fm := fm) (A := ℕ × ℕ)
    (fun p ↦ ⟨0, 0, p.1 + p.2 + 3, 0, p.2⟩) ⟨0, 0⟩
  intro ⟨n, e⟩
  refine ⟨⟨n + e + 3, 2 * e + 1⟩, ?_⟩
  show ⟨0, 0, n + e + 3, 0, e⟩ [fm]⊢⁺ ⟨0, 0, (n + e + 3) + (2 * e + 1) + 3, 0, 2 * e + 1⟩
  rw [show (n + e + 3) + (2 * e + 1) + 3 = n + 3 * e + 7 from by ring]
  exact main_trans n e
