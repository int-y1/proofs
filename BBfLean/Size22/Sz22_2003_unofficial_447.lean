import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #447: [28/15, 1/154, 9/7, 22/3, 35/2]

Vector representation:
```
 2 -1 -1  1  0
-1  0  0 -1 -1
 0  2  0 -1  0
 1 -1  0  0  1
-1  0  1  1  0
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_447

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a, b+1, c+1, d, e⟩ => some ⟨a+2, b, c, d+1, e⟩
  | ⟨a+1, b, c, d+1, e+1⟩ => some ⟨a, b, c, d, e⟩
  | ⟨a, b, c, d+1, e⟩ => some ⟨a, b+2, c, d, e⟩
  | ⟨a, b+1, c, d, e⟩ => some ⟨a+1, b, c, d, e+1⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b, c+1, d+1, e⟩
  | _ => none

-- R3 drain: (X, b, 0, D, 0) →* (X, b + 2*D, 0, 0, 0)
theorem r3_drain : ∀ D, ∀ X b, ⟨X, b, 0, D, 0⟩ [fm]⊢* ⟨X, b + 2*D, 0, 0, 0⟩ := by
  intro D; induction' D with D h <;> intro X b
  · exists 0
  step fm
  apply stepStar_trans (h X (b + 2))
  ring_nf; finish

-- Phase 1: R5/R2 interleaved chain
-- (a+2*k, 0, c, 0, k) →* (a, 0, c+k, 0, 0)
theorem r5r2_chain : ∀ k, ∀ a c, ⟨a+2*k, 0, c, 0, k⟩ [fm]⊢* ⟨a, 0, c+k, 0, 0⟩ := by
  intro k; induction' k with k h <;> intro a c
  · exists 0
  rw [show a + 2 * (k + 1) = (a + 2 * k) + 2 from by ring]
  step fm
  step fm
  apply stepStar_trans (h a (c + 1))
  ring_nf; finish

-- Phase 2: R3/R1 chain + R3 drain
-- (X, 0, C, D+1, 0) →* (X + 2*C, 2*(D+1) + C, 0, 0, 0)
theorem r3r1_phase : ∀ C, ∀ X D, ⟨X, 0, C, D+1, 0⟩ [fm]⊢* ⟨X + 2*C, 2*(D+1) + C, 0, 0, 0⟩ := by
  intro C; induction' C using Nat.strongRecOn with C ih; intro X D
  rcases C with _ | _ | C
  · -- C=0: R3 drain
    have h := r3_drain (D+1) X 0
    rw [show (0 : ℕ) + 2 * (D + 1) = 2 * (D + 1) from by omega] at h
    simpa using h
  · -- C=1: R3, R1, then R3 drain
    step fm
    step fm
    apply stepStar_trans (r3_drain (D+1) (X+2) 1)
    ring_nf; finish
  · -- C+2: R3, R1, R1, then IH on C
    step fm
    rw [show C + 2 = (C + 1) + 1 from by ring]
    step fm
    rw [show C + 1 = C + 1 from rfl]
    step fm
    rw [show D + 1 + 1 = (D + 1) + 1 from by ring]
    apply stepStar_trans (ih C (by omega) (X + 4) (D + 1))
    ring_nf; finish

-- Phase 3: R4 chain: (a, b+k, 0, 0, e) →* (a+k, b, 0, 0, e+k)
theorem r4_chain : ∀ k, ∀ a b e, ⟨a, b+k, 0, 0, e⟩ [fm]⊢* ⟨a+k, b, 0, 0, e+k⟩ := by
  intro k; induction' k with k h <;> intro a b e
  · exists 0
  rw [show b + (k + 1) = (b + k) + 1 from by ring]
  step fm
  apply stepStar_trans (h (a + 1) b (e + 1))
  ring_nf; finish

-- Main transition: (S, 0, 0, 0, E) →⁺ (S+E+4, 0, 0, 0, E+3) when S ≥ 2*E+1 and E ≥ 1
theorem main_trans (S E : ℕ) (hS : S ≥ 2*E+1) (_hE : E ≥ 1) :
    ⟨S, 0, 0, 0, E⟩ [fm]⊢⁺ ⟨S+E+4, 0, 0, 0, E+3⟩ := by
  -- Phase 1: R5/R2 chain: →* (S-2E, 0, E, 0, 0)
  apply stepStar_stepPlus_stepPlus (c₂ := ⟨S - 2*E, 0, E, 0, 0⟩)
  · have h := r5r2_chain E (S - 2*E) 0
    rw [show (S - 2 * E) + 2 * E = S from by omega,
        show 0 + E = E from by omega] at h
    exact h
  -- R5 step: (S-2E, 0, E, 0, 0) → (S-2E-1, 0, E+1, 1, 0), then rest
  -- S-2E ≥ 1, so rewrite as (S-2E-1)+1
  rw [show S - 2 * E = (S - 2 * E - 1) + 1 from by omega]
  step fm  -- R5: ((S-2E-1), 0, E+1, 1, 0)
  -- Phase 2: (S-2E-1, 0, E+1, 0+1, 0) →* (S+1, E+3, 0, 0, 0)
  apply stepStar_trans (c₂ := ⟨S+1, E+3, 0, 0, 0⟩)
  · have h := r3r1_phase (E+1) (S - 2*E - 1) 0
    rw [show (S - 2 * E - 1) + 2 * (E + 1) = S + 1 from by omega,
        show 2 * (0 + 1) + (E + 1) = E + 3 from by omega] at h
    exact h
  -- Phase 3: R4 chain: (S+1, E+3, 0, 0, 0) →* (S+E+4, 0, 0, 0, E+3)
  rw [show E + 3 = 0 + (E + 3) from by omega]
  apply stepStar_trans (r4_chain (E+3) (S+1) 0 0)
  rw [show S + 1 + (E + 3) = S + E + 4 from by omega,
      show (0 : ℕ) + (E + 3) = E + 3 from by omega]
  finish

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := (⟨8, 0, 0, 0, 3⟩ : Q)) (by execute fm 22)
  apply progress_nonhalt (fm := fm)
    (P := fun q ↦ ∃ S E, q = (⟨S, 0, 0, 0, E⟩ : Q) ∧ S ≥ 2*E+1 ∧ E ≥ 3)
  · intro c ⟨S, E, hq, hS, hE⟩
    subst hq
    exact ⟨⟨S+E+4, 0, 0, 0, E+3⟩,
           ⟨S+E+4, E+3, rfl, by omega, by omega⟩,
           main_trans S E hS (by omega)⟩
  · exact ⟨8, 3, rfl, by omega, by omega⟩

end Sz22_2003_unofficial_447
