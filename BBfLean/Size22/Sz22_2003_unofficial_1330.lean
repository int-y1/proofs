import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #1330: [63/10, 2/33, 121/2, 5/7, 42/11]

Vector representation:
```
-1  2 -1  1  0
 1 -1  0  0 -1
-1  0  0  0  2
 0  0  1 -1  0
 1  1  0  1 -1
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_1330

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a+1, b, c+1, d, e⟩ => some ⟨a, b+2, c, d+1, e⟩
  | ⟨a, b+1, c, d, e+1⟩ => some ⟨a+1, b, c, d, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b, c, d, e+2⟩
  | ⟨a, b, c, d+1, e⟩ => some ⟨a, b, c+1, d, e⟩
  | ⟨a, b, c, d, e+1⟩ => some ⟨a+1, b+1, c, d+1, e⟩
  | _ => none

-- R3 chain: (k, 0, 0, d, e) ⊢* (0, 0, 0, d, e+2*k)
theorem r3_chain : ∀ k d e, ⟨k, 0, 0, d, e⟩ [fm]⊢* ⟨0, 0, 0, d, e + 2 * k⟩ := by
  intro k; induction' k with k ih <;> intro d e
  · exists 0
  · step fm; apply stepStar_trans (ih d (e + 2)); ring_nf; finish

-- R4 drain with c generalized: (0, 0, c, k, e) ⊢* (0, 0, c+k, 0, e)
theorem r4_chain : ∀ k c e, ⟨0, 0, c, k, e⟩ [fm]⊢* ⟨0, 0, c + k, 0, e⟩ := by
  intro k; induction' k with k ih <;> intro c e
  · exists 0
  · step fm; apply stepStar_trans (ih (c + 1) e); ring_nf; finish

-- R1R2 chain with c=0: (1, b, k, d, e+k) ⊢* (1, b+k, 0, d+k, e)
theorem r1r2_chain : ∀ k b d e, ⟨1, b, k, d, e + k⟩ [fm]⊢* ⟨1, b + k, 0, d + k, e⟩ := by
  intro k; induction' k with k ih <;> intro b d e
  · exists 0
  · rw [show e + (k + 1) = (e + k) + 1 from by ring]
    step fm; step fm
    apply stepStar_trans (ih (b + 1) (d + 1) e); ring_nf; finish

-- R2 drain: (a, k, 0, d, k) ⊢* (a+k, 0, 0, d, 0)
theorem r2_chain : ∀ k a d, ⟨a, k, 0, d, k⟩ [fm]⊢* ⟨a + k, 0, 0, d, 0⟩ := by
  intro k; induction' k with k ih <;> intro a d
  · exists 0
  · step fm; apply stepStar_trans (ih (a + 1) d); ring_nf; finish

-- Full transition: (n+1, 0, 0, n, 0) ⊢⁺ (n+2, 0, 0, n+1, 0)
theorem main_trans (n : ℕ) :
    ⟨n + 1, 0, 0, n, 0⟩ [fm]⊢⁺ ⟨n + 2, 0, 0, n + 1, 0⟩ := by
  -- R3 step (first step, gives ⊢⁺)
  step fm
  -- State: (n, 0, 0, n, 2)
  -- Remaining R3 drain
  apply stepStar_trans (r3_chain n n 2)
  rw [show 2 + 2 * n = 2 * (n + 1) from by ring]
  -- R4 drain: (0, 0, 0, n, 2*(n+1)) ⊢* (0, 0, n, 0, 2*(n+1))
  apply stepStar_trans (r4_chain n 0 (2 * (n + 1)))
  rw [show 0 + n = n from by ring, show 2 * (n + 1) = (n + 1) + 1 + n from by ring]
  -- R5 step: (0, 0, n, 0, (n+1)+1+n) = (0, 0, n, 0, ((n+1)+n)+1)
  rw [show (n + 1) + 1 + n = ((n + 1) + n) + 1 from by ring]
  step fm
  -- State: (1, 1, n, 1, (n+1)+n)
  -- R1R2 chain
  apply stepStar_trans (r1r2_chain n 1 1 (n + 1))
  -- State: (1, 1+n, 0, 1+n, n+1)
  rw [show 1 + n = n + 1 from by ring]
  -- R2 drain: (1, n+1, 0, n+1, n+1) ⊢* (n+2, 0, 0, n+1, 0)
  apply stepStar_trans (r2_chain (n + 1) 1 (n + 1))
  ring_nf; finish

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨1, 0, 0, 0, 0⟩) (by finish)
  apply progress_nonhalt_simple (fm := fm) (A := ℕ)
    (fun n ↦ ⟨n + 1, 0, 0, n, 0⟩) 0
  intro n; exact ⟨n + 1, main_trans n⟩

end Sz22_2003_unofficial_1330
