import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #720: [35/6, 4/55, 143/2, 3/7, 105/13]

Vector representation:
```
-1 -1  1  1  0  0
 2  0 -1  0 -1  0
-1  0  0  0  1  1
 0  1  0 -1  0  0
 0  1  1  1  0 -1
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_720

def Q := ℕ × ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a+1, b+1, c, d, e, f⟩ => some ⟨a, b, c+1, d+1, e, f⟩
  | ⟨a, b, c+1, d, e+1, f⟩ => some ⟨a+2, b, c, d, e, f⟩
  | ⟨a+1, b, c, d, e, f⟩ => some ⟨a, b, c, d, e+1, f+1⟩
  | ⟨a, b, c, d+1, e, f⟩ => some ⟨a, b+1, c, d, e, f⟩
  | ⟨a, b, c, d, e, f+1⟩ => some ⟨a, b+1, c+1, d+1, e, f⟩
  | _ => none

theorem r4_chain : ∀ k, ∀ b d e f, ⟨0, b, 0, d + k, e, f⟩ [fm]⊢* ⟨0, b + k, 0, d, e, f⟩ := by
  intro k; induction' k with k ih <;> intro b d e f
  · exists 0
  · rw [show d + (k + 1) = (d + k) + 1 from by ring]
    step fm
    apply stepStar_trans (ih (b + 1) d e f)
    ring_nf; finish

theorem r3_drain : ∀ j, ∀ a d e f, ⟨a + j, 0, 0, d, e, f⟩ [fm]⊢* ⟨a, 0, 0, d, e + j, f + j⟩ := by
  intro j; induction' j with j ih <;> intro a d e f
  · exists 0
  · rw [show a + (j + 1) = (a + j) + 1 from by ring]
    step fm
    apply stepStar_trans (ih a d (e + 1) (f + 1))
    ring_nf; finish

-- R2R3 chain: k rounds of (R2, R3).
-- (a, 0, c+k, d, 1, f) ⊢* (a+k, 0, c, d, 1, f+k)
-- After R2: (a+2, 0, c+k-1, d, 0, f). R3 fires since a+2=(a+1)+1.
-- We use `show` for R3 step since c+k-1 is symbolic.
theorem r2r3_chain : ∀ k, ∀ a c d f,
    ⟨a, 0, c + k, d, 1, f⟩ [fm]⊢* ⟨a + k, 0, c, d, 1, f + k⟩ := by
  intro k; induction' k with k ih <;> intro a c d f
  · exists 0
  · rw [show c + (k + 1) = (c + k) + 1 from by ring]
    step fm
    apply stepStar_trans
    · apply step_stepStar
      show fm ⟨(a + 1) + 1, 0, c + k, d, 0, f⟩ = some ⟨a + 1, 0, c + k, d, 0 + 1, f + 1⟩
      unfold fm; simp
    apply stepStar_trans (ih (a + 1) c d (f + 1))
    ring_nf; finish

-- R1R1R2 chain: k rounds of (R1, R1, R2).
-- (2, 2k+1, c, d, k, f) ⊢* (2, 1, c+k, d+2k, 0, f)
-- Each round: state (2, 2j+1, c', d', j, f) with j>=1:
-- R1: (1, 2j, c'+1, d'+1, j, f) -> R1: (0, 2j-1, c'+2, d'+2, j, f)
-- R2 (c'+2>=1, j>=1): (2, 2j-1, c'+1, d'+2, j-1, f)
-- = (2, 2(j-1)+1, c'+1, d'+2, j-1, f)
theorem r1r1r2_chain : ∀ k, ∀ c d f,
    ⟨2, 2 * k + 1, c, d, k, f⟩ [fm]⊢* ⟨2, 1, c + k, d + 2 * k, 0, f⟩ := by
  intro k; induction' k with k ih <;> intro c d f
  · exists 0
  · rw [show 2 * (k + 1) + 1 = (2 * k + 1) + 2 from by ring,
        show (k + 1) = k + 1 from rfl]
    step fm; step fm
    rw [show c + 1 + 1 = (c + 1) + 1 from by ring,
        show d + 1 + 1 = d + 2 from by ring,
        show k + 1 = k + 1 from rfl]
    step fm
    apply stepStar_trans (ih (c + 1) (d + 2) f)
    ring_nf; finish

theorem main_trans (n : ℕ) :
    ⟨0, 0, 0, 2 * n, n + 1, n * n + n + 1⟩ [fm]⊢⁺
    ⟨0, 0, 0, 2 * n + 2, n + 2, n * n + 3 * n + 3⟩ := by
  -- Phase 1: R4 chain (d -> b)
  rw [show 2 * n = 0 + 2 * n from by ring]
  apply stepStar_stepPlus_stepPlus (r4_chain (2 * n) 0 0 (n + 1) (n * n + n + 1))
  rw [show 0 + 2 * n = 2 * n from by ring]
  -- Phase 2: R5: (0, 2n, 0, 0, n+1, n^2+n+1) -> (0, 2n+1, 1, 1, n+1, n^2+n)
  rw [show n * n + n + 1 = (n * n + n) + 1 from by ring]
  apply step_stepStar_stepPlus
  · show fm ⟨0, 2 * n, 0, 0, n + 1, (n * n + n) + 1⟩ =
        some ⟨0, 2 * n + 1, 1, 1, n + 1, n * n + n⟩
    simp [fm]
  -- Phase 3: R2: (0, 2n+1, 1, 1, n+1, n^2+n) -> (2, 2n+1, 0, 1, n, n^2+n)
  step fm
  -- Phase 4: R1R1R2 chain (n rounds)
  -- State: (2, 2n+1, 0, 1, n, n^2+n)
  -- r1r1r2_chain n: (2, 2n+1, 0, 1, n, f) ⊢* (2, 1, n, 2n+1, 0, f)
  apply stepStar_trans (r1r1r2_chain n 0 1 (n * n + n))
  rw [show 0 + n = n from by ring,
      show 1 + 2 * n = 2 * n + 1 from by ring]
  -- Phase 5: R1: (2, 1, n, 2n+1, 0, n^2+n) -> (1, 0, n+1, 2n+2, 0, n^2+n)
  step fm
  -- Phase 6: R3: (1, 0, n+1, 2n+2, 0, n^2+n)
  -- R1 can't fire (b=0). R2 can't fire (e=0). R3 fires (a=1>=1).
  -- But n+1 could match c'+1 pattern in R2, and e=0 doesn't match e'+1.
  -- step fm should handle this since a=1=(0)+1, b=0.
  step fm
  -- Phase 7: R2R3 chain (n+1 rounds)
  -- State: (0, 0, n+1, 2n+2, 1, n^2+n+1)
  rw [show n + 1 = 0 + (n + 1) from by ring]
  apply stepStar_trans (r2r3_chain (n + 1) 0 0 (2 * n + 2) (n * n + n + 1))
  rw [show 0 + (n + 1) = n + 1 from by ring,
      show n * n + n + 1 + (n + 1) = n * n + 2 * n + 2 from by ring]
  -- Phase 8: R3 drain: (n+1, 0, 0, 2n+2, 1, n^2+2n+2) -> (0, 0, 0, 2n+2, n+2, n^2+3n+3)
  rw [show n + 1 = 0 + (n + 1) from by ring]
  apply stepStar_trans (r3_drain (n + 1) 0 (2 * n + 2) 1 (n * n + 2 * n + 2))
  ring_nf; finish

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨0, 0, 0, 0, 1, 1⟩) (by execute fm 1)
  apply progress_nonhalt_simple (fm := fm) (A := ℕ)
    (fun n ↦ ⟨0, 0, 0, 2 * n, n + 1, n * n + n + 1⟩) 0
  intro n; refine ⟨n + 1, ?_⟩
  convert main_trans n using 2; ring_nf

end Sz22_2003_unofficial_720
