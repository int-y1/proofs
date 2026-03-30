import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #709: [35/6, 4/55, 121/2, 3/7, 70/11]

Vector representation:
```
-1 -1  1  1  0
 2  0 -1  0 -1
-1  0  0  0  2
 0  1  0 -1  0
 1  0  1  1 -1
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_709

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a+1, b+1, c, d, e⟩ => some ⟨a, b, c+1, d+1, e⟩
  | ⟨a, b, c+1, d, e+1⟩ => some ⟨a+2, b, c, d, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b, c, d, e+2⟩
  | ⟨a, b, c, d+1, e⟩ => some ⟨a, b+1, c, d, e⟩
  | ⟨a, b, c, d, e+1⟩ => some ⟨a+1, b, c+1, d+1, e⟩
  | _ => none

theorem r3_chain : ∀ k, ∀ a d e, ⟨a + k, 0, 0, d, e⟩ [fm]⊢* ⟨a, 0, 0, d, e + 2 * k⟩ := by
  intro k; induction' k with k ih <;> intro a d e
  · exists 0
  · rw [show a + (k + 1) = (a + k) + 1 from by ring]
    step fm
    apply stepStar_trans (ih a d (e + 2))
    ring_nf; finish

theorem r4_chain : ∀ k, ∀ b d e, ⟨0, b, 0, d + k, e⟩ [fm]⊢* ⟨0, b + k, 0, d, e⟩ := by
  intro k; induction' k with k ih <;> intro b d e
  · exists 0
  · rw [show d + (k + 1) = (d + k) + 1 from by ring]
    step fm
    apply stepStar_trans (ih (b + 1) d e)
    ring_nf; finish

theorem r2_chain : ∀ k, ∀ a c d e, ⟨a, 0, c + k, d, e + k⟩ [fm]⊢* ⟨a + 2 * k, 0, c, d, e⟩ := by
  intro k; induction' k with k ih <;> intro a c d e
  · exists 0
  · rw [show c + (k + 1) = (c + k) + 1 from by ring,
        show e + (k + 1) = (e + k) + 1 from by ring]
    step fm
    apply stepStar_trans (ih (a + 2) c d e)
    ring_nf; finish

theorem r2r1r1_chain : ∀ k, ∀ c d e, ⟨0, 2 * k, c + 1, d, e + k⟩ [fm]⊢* ⟨0, 0, c + k + 1, d + 2 * k, e⟩ := by
  intro k; induction' k with k ih <;> intro c d e
  · exists 0
  · rw [show 2 * (k + 1) = (2 * k + 1) + 1 from by ring,
        show e + (k + 1) = (e + k) + 1 from by ring]
    step fm
    rw [show 2 * k + 1 = (2 * k) + 1 from by ring]
    step fm; step fm
    apply stepStar_trans (ih (c + 1) (d + 2) e)
    ring_nf; finish

theorem r2r1_odd_chain : ∀ k, ∀ c d e, ⟨0, 2 * k + 1, c + 1, d, e + k + 1⟩ [fm]⊢* ⟨1, 0, c + k + 1, d + 2 * k + 1, e⟩ := by
  intro k; induction' k with k ih <;> intro c d e
  · rw [show e + 0 + 1 = (e + 0) + 1 from by ring,
        show c + 0 + 1 = c + 1 from by ring,
        show d + 0 + 1 = d + 1 from by ring]
    step fm; step fm; finish
  · rw [show 2 * (k + 1) + 1 = (2 * k + 2) + 1 from by ring,
        show e + (k + 1) + 1 = (e + k + 1) + 1 from by ring]
    step fm
    rw [show 2 * k + 2 = (2 * k + 1) + 1 from by ring]
    step fm; step fm
    apply stepStar_trans (ih (c + 1) (d + 2) e)
    ring_nf; finish

theorem main_trans (n e : ℕ) :
    ⟨n + 3, 0, 0, n + 1, e⟩ [fm]⊢⁺ ⟨n + 4, 0, 0, n + 2, e + n + 3⟩ := by
  rcases Nat.even_or_odd n with ⟨k, hk⟩ | ⟨k, hk⟩
  · -- Even case: n = 2k
    rw [show k + k = 2 * k from by ring] at hk; subst hk
    -- Phase 1: first R3 step (for stepPlus) then R3 chain
    rw [show 2 * k + 3 = 0 + (2 * k + 3) from by ring]
    apply step_stepStar_stepPlus
    · show fm ⟨0 + (2 * k + 2) + 1, 0, 0, 2 * k + 1, e⟩ = some ⟨0 + (2 * k + 2), 0, 0, 2 * k + 1, e + 2⟩
      simp [fm]
    apply stepStar_trans (r3_chain (2 * k + 2) 0 (2 * k + 1) (e + 2))
    -- Phase 2: R4 chain
    rw [show e + 2 + 2 * (2 * k + 2) = e + 4 * k + 6 from by ring,
        show 2 * k + 1 = 0 + (2 * k + 1) from by ring]
    apply stepStar_trans (r4_chain (2 * k + 1) 0 0 (e + 4 * k + 6))
    -- Phase 3: R5+R1
    rw [show 0 + (2 * k + 1) = (2 * k) + 1 from by ring,
        show e + 4 * k + 6 = (e + 3 * k + 5) + (k + 1) from by ring]
    step fm; step fm
    -- Phase 4: R2R1R1 chain (k rounds, even b=2k)
    apply stepStar_trans (r2r1r1_chain k 1 2 (e + 3 * k + 5))
    -- Phase 5: R2 chain (k+2 rounds)
    rw [show 1 + k + 1 = 0 + (k + 2) from by ring,
        show 2 + 2 * k = 2 * k + 2 from by ring,
        show e + 3 * k + 5 = (e + 2 * k + 3) + (k + 2) from by ring]
    apply stepStar_trans (r2_chain (k + 2) 0 0 (2 * k + 2) (e + 2 * k + 3))
    ring_nf; finish
  · -- Odd case: n = 2k+1
    subst hk
    rw [show 2 * k + 1 + 3 = 2 * k + 4 from by ring,
        show 2 * k + 1 + 1 = 2 * k + 2 from by ring,
        show 2 * k + 1 + 4 = 2 * k + 5 from by ring,
        show 2 * k + 1 + 2 = 2 * k + 3 from by ring,
        show e + (2 * k + 1) + 3 = e + 2 * k + 4 from by ring]
    -- Phase 1: first R3 step (for stepPlus) then R3 chain
    rw [show 2 * k + 4 = 0 + (2 * k + 4) from by ring]
    apply step_stepStar_stepPlus
    · show fm ⟨0 + (2 * k + 3) + 1, 0, 0, 2 * k + 2, e⟩ = some ⟨0 + (2 * k + 3), 0, 0, 2 * k + 2, e + 2⟩
      simp [fm]
    apply stepStar_trans (r3_chain (2 * k + 3) 0 (2 * k + 2) (e + 2))
    -- Phase 2: R4 chain
    rw [show e + 2 + 2 * (2 * k + 3) = e + 4 * k + 8 from by ring,
        show 2 * k + 2 = 0 + (2 * k + 2) from by ring]
    apply stepStar_trans (r4_chain (2 * k + 2) 0 0 (e + 4 * k + 8))
    -- Phase 3: R5+R1
    rw [show 0 + (2 * k + 2) = (2 * k + 1) + 1 from by ring,
        show e + 4 * k + 8 = (e + 3 * k + 6) + (k + 2) from by ring]
    step fm; step fm
    -- Phase 4: R2R1 odd chain (b = 2k+1)
    apply stepStar_trans (r2r1_odd_chain k 1 2 (e + 3 * k + 6))
    -- Phase 5: R2 chain (k+2 rounds, starting with a=1)
    rw [show 1 + k + 1 = 0 + (k + 2) from by ring,
        show 2 + 2 * k + 1 = 2 * k + 3 from by ring,
        show e + 3 * k + 6 = (e + 2 * k + 4) + (k + 2) from by ring]
    apply stepStar_trans (r2_chain (k + 2) 1 0 (2 * k + 3) (e + 2 * k + 4))
    ring_nf; finish

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨3, 0, 0, 1, 0⟩) (by execute fm 3)
  apply progress_nonhalt_simple (fm := fm) (A := ℕ × ℕ)
    (fun ⟨n, e⟩ ↦ ⟨n + 3, 0, 0, n + 1, e⟩) ⟨0, 0⟩
  intro ⟨n, e⟩; exact ⟨⟨n + 1, e + n + 3⟩, main_trans n e⟩

end Sz22_2003_unofficial_709
