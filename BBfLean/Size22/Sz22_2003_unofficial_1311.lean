import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #1311: [63/10, 1331/2, 2/33, 5/7, 10/11]

Vector representation:
```
-1  2 -1  1  0
-1  0  0  0  3
 1 -1  0  0 -1
 0  0  1 -1  0
 1  0  1  0 -1
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_1311

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a+1, b, c+1, d, e⟩ => some ⟨a, b+2, c, d+1, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b, c, d, e+3⟩
  | ⟨a, b+1, c, d, e+1⟩ => some ⟨a+1, b, c, d, e⟩
  | ⟨a, b, c, d+1, e⟩ => some ⟨a, b, c+1, d, e⟩
  | ⟨a, b, c, d, e+1⟩ => some ⟨a+1, b, c+1, d, e⟩
  | _ => none

-- R1-R3 interleaved chain: each round R1 then R3.
-- (1, j, c+k, j, e+k) ⊢* (1, j+k, c, j+k, e)
theorem r1r3_chain : ∀ k j c e, ⟨1, j, c + k, j, e + k⟩ [fm]⊢* ⟨1, j + k, c, j + k, e⟩ := by
  intro k; induction' k with k ih <;> intro j c e
  · exists 0
  · rw [show c + (k + 1) = (c + k) + 1 from by ring,
        show e + (k + 1) = (e + k) + 1 from by ring]
    step fm; step fm
    apply stepStar_trans (ih (j + 1) c e)
    ring_nf; finish

-- R3-R2 chain: each round R3 then R2, draining b.
-- (0, k, 0, d, e + 3) ⊢* (0, 0, 0, d, e + 2*k + 3)
theorem r3r2_chain : ∀ k d e, ⟨0, k, 0, d, e + 3⟩ [fm]⊢* ⟨0, 0, 0, d, e + 2 * k + 3⟩ := by
  intro k; induction' k with k ih <;> intro d e
  · exists 0
  · rw [show (k : ℕ) + 1 = k + 1 from rfl]
    step fm; step fm
    apply stepStar_trans (ih d (e + 2))
    ring_nf; finish

-- R4 chain: transfer d to c.
-- (0, 0, c, d+k, e) ⊢* (0, 0, c+k, d, e)
theorem r4_chain : ∀ k c d e, ⟨0, 0, c, d + k, e⟩ [fm]⊢* ⟨0, 0, c + k, d, e⟩ := by
  intro k; induction' k with k ih <;> intro c d e
  · exists 0
  · rw [show d + (k + 1) = (d + k) + 1 from by ring]
    step fm
    apply stepStar_trans (ih (c + 1) d e)
    ring_nf; finish

-- Main transition: (0, 0, n+1, 0, e+n+3) ⊢⁺ (0, 0, n+2, 0, e+2*n+7)
theorem main_trans (n e : ℕ) :
    ⟨0, 0, n + 1, 0, e + n + 3⟩ [fm]⊢⁺ ⟨0, 0, n + 2, 0, e + 2 * n + 7⟩ := by
  -- Phase 1: R5 (1 step)
  rw [show e + n + 3 = (e + n + 2) + 1 from by ring]
  step fm
  -- State: (1, 0, n+2, 0, e+n+2)
  rw [show n + 1 + 1 = n + 2 from by ring]
  -- Phase 2: R1-R3 chain (n+2 rounds)
  rw [show n + 2 = 0 + (n + 2) from by ring,
      show e + n + 2 = e + (n + 2) from by ring]
  apply stepStar_trans (r1r3_chain (n + 2) 0 0 e)
  rw [show 0 + (n + 2) = n + 2 from by ring]
  -- State: (1, n+2, 0, n+2, e)
  -- Phase 3: R2 (1 step)
  step fm
  -- State: (0, n+2, 0, n+2, e+3)
  -- Phase 4: R3-R2 chain (n+2 rounds)
  apply stepStar_trans (r3r2_chain (n + 2) (n + 2) e)
  -- Phase 5: R4 chain (n+2 steps)
  rw [show e + 2 * (n + 2) + 3 = e + 2 * n + 7 from by ring]
  have := r4_chain (n + 2) 0 0 (e + 2 * n + 7)
  simp only [Nat.zero_add] at this
  exact this

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨0, 0, 1, 0, 6⟩) (by execute fm 8)
  apply progress_nonhalt (fm := fm)
    (P := fun q ↦ ∃ n e, q = ⟨0, 0, n + 1, 0, e + n + 3⟩)
  · intro c ⟨n, e, hc⟩; subst hc
    refine ⟨⟨0, 0, n + 2, 0, e + 2 * n + 7⟩, ⟨n + 1, e + n + 3, ?_⟩, main_trans n e⟩
    change (0, 0, n + 2, 0, e + 2 * n + 7) = (0, 0, n + 1 + 1, 0, e + n + 3 + (n + 1) + 3)
    simp only [Prod.mk.injEq, true_and]; omega
  · exact ⟨0, 3, rfl⟩

end Sz22_2003_unofficial_1311
