import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #777: [35/6, 55/2, 40/77, 3/5, 7/3]

Vector representation:
```
-1 -1  1  1  0
-1  0  1  0  1
 3  0  1 -1 -1
 0  1 -1  0  0
 0 -1  0  1  0
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_777

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a+1, b+1, c, d, e⟩ => some ⟨a, b, c+1, d+1, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b, c+1, d, e+1⟩
  | ⟨a, b, c, d+1, e+1⟩ => some ⟨a+3, b, c+1, d, e⟩
  | ⟨a, b, c+1, d, e⟩ => some ⟨a, b+1, c, d, e⟩
  | ⟨a, b+1, c, d, e⟩ => some ⟨a, b, c, d+1, e⟩
  | _ => none

theorem r4_chain : ∀ k b c e, ⟨0, b, c + k, 0, e⟩ [fm]⊢* ⟨0, b + k, c, 0, e⟩ := by
  intro k; induction' k with k ih <;> intro b c e
  · exists 0
  · rw [show c + (k + 1) = (c + k) + 1 from by ring]
    step fm
    apply stepStar_trans (ih (b + 1) c e)
    ring_nf; finish

theorem r3r2_chain : ∀ k c d e, ⟨0, 0, c, d + k, e + 1⟩ [fm]⊢* ⟨0, 0, c + 4 * k, d, e + 2 * k + 1⟩ := by
  intro k; induction' k with k ih <;> intro c d e
  · exists 0
  · rw [show d + (k + 1) = (d + k) + 1 from by ring]
    step fm; step fm; step fm; step fm
    rw [show e + 1 + 1 + 1 = (e + 2) + 1 from by ring]
    apply stepStar_trans (ih (c + 4) d (e + 2))
    ring_nf; finish

-- Process (3, b, c, d, e'+1) to canonical form.
-- Condition: 3*e'+3 >= b+1 (i.e. 3*e' >= b-2)
theorem combined_drain : ∀ b, ∀ c d e', 3 * e' + 3 ≥ b + 1 →
    ⟨3, b, c, d, e' + 1⟩ [fm]⊢* ⟨0, 0, c + 4 * (d + b) + 3, 0, e' + 2 * d + b + 4⟩ := by
  intro b; induction' b using Nat.strongRecOn with b ih; intro c d e' hb
  rcases b with _ | _ | _ | b
  · -- b = 0: R2 x 3, then R3R2 chain
    step fm; step fm; step fm
    rw [show c + 1 + 1 + 1 = c + 3 from by ring,
        show e' + 1 + 1 + 1 + 1 = (e' + 3) + 1 from by ring,
        show (d : ℕ) = 0 + d from by ring]
    apply stepStar_trans (r3r2_chain d (c + 3) 0 (e' + 3))
    ring_nf; finish
  · -- b = 1: R1 + R2 x 2, then R3R2 chain
    step fm; step fm; step fm
    rw [show c + 1 + 1 + 1 = c + 3 from by ring,
        show d + 1 = 0 + (d + 1) from by ring,
        show e' + 1 + 1 + 1 = (e' + 2) + 1 from by ring]
    apply stepStar_trans (r3r2_chain (d + 1) (c + 3) 0 (e' + 2))
    ring_nf; finish
  · -- b = 2: R1 x 2 + R2, then R3R2 chain
    step fm; step fm; step fm
    rw [show c + 1 + 1 + 1 = c + 3 from by ring,
        show d + 1 + 1 = 0 + (d + 2) from by ring,
        show e' + 1 + 1 = (e' + 1) + 1 from by ring]
    apply stepStar_trans (r3r2_chain (d + 2) (c + 3) 0 (e' + 1))
    ring_nf; finish
  · -- b = b + 3: R1 x 3, R3, recurse
    have he' : e' ≥ 1 := by omega
    obtain ⟨f, rfl⟩ : ∃ f, e' = f + 1 := ⟨e' - 1, by omega⟩
    step fm; step fm; step fm
    rw [show d + 1 + 1 + 1 = (d + 2) + 1 from by ring]
    step fm
    rw [show c + 1 + 1 + 1 + 1 = c + 4 from by ring]
    apply stepStar_trans (ih b (by omega) (c + 4) (d + 2) f (by omega))
    ring_nf; finish

-- Invariant: 3*e >= c+1 ensures non-halting.
-- State: (0, 0, c+1, 0, e+1) with 3*e >= c+1.
-- This implies e >= 1 (since c+1 >= 1).
theorem main_transition (hce : 3 * e ≥ c + 1) :
    ⟨0, 0, c + 1, 0, e + 1⟩ [fm]⊢⁺ ⟨0, 0, 4 * (c + 1), 0, e + c + 3⟩ := by
  have he : e ≥ 1 := by omega
  obtain ⟨e', rfl⟩ : ∃ e', e = e' + 1 := ⟨e - 1, by omega⟩
  -- R4 chain
  have h1 : ⟨0, 0, 0 + (c + 1), 0, e' + 1 + 1⟩ [fm]⊢* ⟨0, 0 + (c + 1), 0, 0, e' + 1 + 1⟩ :=
    r4_chain (c + 1) 0 0 (e' + 1 + 1)
  simp at h1
  apply stepStar_stepPlus_stepPlus h1
  -- R5
  step fm
  -- R3: state has e'+1+1 in e-slot, which matches d+1=1, e+1 pattern for R3.
  step fm
  -- Now at (3, c, 1, 0, e'+1). Apply combined_drain.
  apply stepStar_trans (combined_drain c 1 0 e' (by omega))
  rw [show 1 + 4 * (0 + c) + 3 = 4 * (c + 1) from by ring,
      show e' + 2 * 0 + c + 4 = e' + 1 + c + 3 from by ring]
  finish

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨0, 0, 4, 0, 3⟩) (by execute fm 7)
  apply progress_nonhalt (fm := fm)
    (P := fun q ↦ ∃ c e, q = ⟨0, 0, c + 1, 0, e + 1⟩ ∧ 3 * e ≥ c + 1)
  · intro q ⟨c, e, hq, hce⟩; subst hq
    refine ⟨⟨0, 0, 4 * (c + 1), 0, e + c + 3⟩, ?_, main_transition hce⟩
    refine ⟨4 * c + 3, e + c + 2, ?_, ?_⟩
    · ring_nf
    · omega
  · exact ⟨3, 2, rfl, by omega⟩

end Sz22_2003_unofficial_777
