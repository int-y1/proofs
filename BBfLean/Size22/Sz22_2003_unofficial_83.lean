import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #83: [1/30, 12/77, 49/3, 10/7, 33/2]

Vector representation:
```
-1 -1 -1  0  0
 2  1  0 -1 -1
 0 -1  0  2  0
 1  0  1 -1  0
-1  1  0  0  1
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_83

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a+1, b+1, c+1, d, e⟩ => some ⟨a, b, c, d, e⟩
  | ⟨a, b, c, d+1, e+1⟩ => some ⟨a+2, b+1, c, d, e⟩
  | ⟨a, b+1, c, d, e⟩ => some ⟨a, b, c, d+2, e⟩
  | ⟨a, b, c, d+1, e⟩ => some ⟨a+1, b, c+1, d, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b+1, c, d, e+1⟩
  | _ => none

-- R4 chain: d transfers to a and c
theorem r4_chain (d : ℕ) : ∀ k c a, ⟨a, 0, c, d + k, 0⟩ [fm]⊢* ⟨a + k, 0, c + k, d, 0⟩ := by
  intro k; induction' k with k ih <;> intro c a
  · exists 0
  rw [show d + (k + 1) = (d + k) + 1 from by ring]
  step fm
  apply stepStar_trans (ih _ _)
  ring_nf; finish

-- R5/R1 chain: each pair reduces a by 2 and c by 1
theorem r5r1_chain : ∀ k s e, ⟨s + 2 * k, 0, k, 0, e⟩ [fm]⊢* ⟨s, 0, 0, 0, e + k⟩ := by
  intro k; induction' k with k ih <;> intro s e
  · exists 0
  rw [show s + 2 * (k + 1) = (s + 2 * k + 1) + 1 from by ring]
  step fm; step fm
  apply stepStar_trans (ih _ _)
  ring_nf; finish

-- R3 drain: b transfers to d
theorem r3_drain : ∀ k a d, ⟨a, k, 0, d, 0⟩ [fm]⊢* ⟨a, 0, 0, d + 2 * k, 0⟩ := by
  intro k; induction' k with k ih <;> intro a d
  · exists 0
  rw [show (k + 1) = k + 1 from rfl]
  step fm
  apply stepStar_trans (ih _ _)
  ring_nf; finish

-- R2/R3 phase: (A, B, 0, 2, E) ->* (A + 2*E, 0, 0, E + 2 + 2*B, 0)
theorem r2r3_phase : ∀ E, ∀ A B, ⟨A, B, 0, 2, E⟩ [fm]⊢* ⟨A + 2 * E, 0, 0, E + 2 + 2 * B, 0⟩ := by
  intro E; induction' E using Nat.strongRecOn with E ih; intro A B
  rcases E with _ | _ | E'
  · -- E=0: drain B via R3
    rw [show A + 2 * 0 = A from by ring, show 0 + 2 + 2 * B = 2 + 2 * B from by ring]
    exact r3_drain B A 2
  · -- E=1: R2, then drain (B+1) via R3
    step fm
    rw [show A + 2 * 1 = A + 2 from by ring, show 1 + 2 + 2 * B = 1 + 2 * (B + 1) from by ring]
    exact r3_drain (B + 1) (A + 2) 1
  · -- E'+2: R2, R2, R3, then recurse
    step fm; step fm; step fm
    apply stepStar_trans (ih E' (by omega) _ _)
    ring_nf; finish

-- Main transition: (a, 0, 0, d, 0) ⊢⁺ (a+d+1, 0, 0, d+3, 0) when a ≥ d+1
theorem main_trans (ha : a ≥ d + 1) :
    ⟨a, 0, 0, d, 0⟩ [fm]⊢⁺ ⟨a + d + 1, 0, 0, d + 3, 0⟩ := by
  obtain ⟨r, rfl⟩ : ∃ r, a = d + 1 + r := ⟨a - (d + 1), by omega⟩
  -- Rewrite target to use r
  rw [show d + 1 + r + d + 1 = r + 2 * d + 2 from by ring]
  -- Phase 1: R4 chain
  have h1 := r4_chain 0 d 0 (d + 1 + r)
  simp only [Nat.zero_add] at h1
  apply stepStar_stepPlus_stepPlus h1
  -- Phase 2: R5/R1 chain
  rw [show d + 1 + r + d = (r + 1) + 2 * d from by ring]
  have h2 := r5r1_chain d (r + 1) 0
  simp only [Nat.zero_add] at h2
  apply stepStar_stepPlus_stepPlus h2
  -- Phase 3: R5, R3 (2 steps)
  step fm; step fm
  -- Phase 4: R2/R3 phase
  apply stepStar_trans (r2r3_phase (d + 1) r 0)
  ring_nf; finish

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨5, 0, 0, 3, 0⟩) (by execute fm 19)
  apply progress_nonhalt (fm := fm)
    (P := fun q ↦ ∃ a d, q = ⟨a, 0, 0, d, 0⟩ ∧ a ≥ d + 1 ∧ d ≥ 3)
  · intro c ⟨a, d, hq, ha, hd⟩; subst hq
    exact ⟨⟨a + d + 1, 0, 0, d + 3, 0⟩,
      ⟨a + d + 1, d + 3, rfl, by omega, by omega⟩,
      main_trans ha⟩
  · exact ⟨5, 3, rfl, by omega, by omega⟩

end Sz22_2003_unofficial_83
