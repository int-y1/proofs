import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #838: [36/35, 15/22, 49/2, 11/3, 5/7]

Vector representation:
```
 2  2 -1 -1  0
-1  1  1  0 -1
-1  0  0  2  0
 0 -1  0  0  1
 0  0  1 -1  0
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_838

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a, b, c+1, d+1, e⟩ => some ⟨a+2, b+2, c, d, e⟩
  | ⟨a+1, b, c, d, e+1⟩ => some ⟨a, b+1, c+1, d, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b, c, d+2, e⟩
  | ⟨a, b+1, c, d, e⟩ => some ⟨a, b, c, d, e+1⟩
  | ⟨a, b, c, d+1, e⟩ => some ⟨a, b, c+1, d, e⟩
  | _ => none

-- Phase 1: R3 chain. Move a to d (c=0, e=0).
theorem r3_chain : ∀ k, ∀ b d, ⟨a + k, b, 0, d, 0⟩ [fm]⊢* ⟨a, b, 0, d + 2 * k, 0⟩ := by
  intro k; induction' k with k ih <;> intro b d
  · exists 0
  · rw [show a + (k + 1) = (a + k) + 1 from by ring]
    step fm
    apply stepStar_trans (ih b (d + 2))
    ring_nf; finish

-- Phase 2: R4 chain. Move b to e (a=0, c=0).
theorem r4_chain : ∀ k, ∀ d e, ⟨0, b + k, 0, d, e⟩ [fm]⊢* ⟨0, b, 0, d, e + k⟩ := by
  intro k; induction' k with k ih <;> intro d e
  · exists 0
  · rw [show b + (k + 1) = (b + k) + 1 from by ring]
    step fm
    apply stepStar_trans (ih d (e + 1))
    ring_nf; finish

-- Phase 4: R2+R1 interleaved chain.
-- Each round: R2 then R1. Net: a+1, b+3, d-1, e-1.
theorem r2r1_chain : ∀ k a b d e, ⟨a + 1, b, 0, d + k, e + k⟩ [fm]⊢* ⟨a + 1 + k, b + 3 * k, 0, d, e⟩ := by
  intro k; induction' k with k ih <;> intro a b d e
  · exists 0
  · rw [show d + (k + 1) = (d + k) + 1 from by ring,
        show e + (k + 1) = (e + k) + 1 from by ring]
    step fm  -- R2
    step fm  -- R1
    rw [show a + 1 + 1 = (a + 1) + 1 from by ring,
        show b + 1 + 2 = (b + 3) from by ring]
    apply stepStar_trans (ih (a + 1) (b + 3) d e)
    ring_nf; finish

-- Phase 5: R2 chain (d=0). Move a,e to b,c.
theorem r2_chain_d0 : ∀ k, ∀ b c, ⟨a + k, b, c, 0, e + k⟩ [fm]⊢* ⟨a, b + k, c + k, 0, e⟩ := by
  intro k; induction' k with k ih <;> intro b c
  · exists 0
  · rw [show a + (k + 1) = (a + k) + 1 from by ring,
        show e + (k + 1) = (e + k) + 1 from by ring]
    -- State: ((a+k)+1, b, c, 0, (e+k)+1)
    -- R1: c≥1? c could be ≥1, but d=0. R1 needs c+1, d+1, so d≥1. Doesn't match.
    -- R2: a+1=(a+k)+1≥1, e+1=(e+k)+1≥1. Fires.
    -- Result: (a+k, b+1, c+1, 0, e+k)
    step fm
    apply stepStar_trans (ih (b + 1) (c + 1))
    ring_nf; finish

-- Phase 6: R3+R1x2 chain.
-- Each round: R3 then R1 twice. Net: a+3, b+4, c-2.
theorem r3r1r1_chain : ∀ k a b, ⟨a + 1, b, 2 * k, 0, 0⟩ [fm]⊢* ⟨a + 1 + 3 * k, b + 4 * k, 0, 0, 0⟩ := by
  intro k; induction' k with k ih <;> intro a b
  · exists 0
  · rw [show 2 * (k + 1) = 2 * k + 2 from by ring]
    step fm  -- R3
    step fm  -- R1
    step fm  -- R1
    rw [show a + 3 + 1 = (a + 3) + 1 from by ring,
        show b + 2 + 2 = b + 4 from by ring]
    apply stepStar_trans (ih (a + 3) (b + 4))
    ring_nf; finish

-- R5+R1 two-step phase
theorem r5r1_phase : ∀ d e, ⟨0, 0, 0, d + 2, e⟩ [fm]⊢* ⟨2, 2, 0, d, e⟩ := by
  intro d e; step fm; step fm; finish

-- Helper: the full transition as ⊢*
theorem main_trans_star (a E : ℕ) (hE : E ≤ a + 1) :
    ⟨a + 2, 2 * (a + E + 1), 0, 0, 0⟩ [fm]⊢* ⟨2 * a + E + 4, 6 * a + 6 * E + 8, 0, 0, 0⟩ := by
  obtain ⟨g, hg⟩ : ∃ g, a + 2 = E + (g + 1) := ⟨a + 1 - E, by omega⟩
  -- Phase 1: R3 chain
  have h1 : ⟨a + 2, 2 * (a + E + 1), 0, 0, 0⟩ [fm]⊢* ⟨0, 2 * (a + E + 1), 0, 2 * a + 4, 0⟩ := by
    rw [show a + 2 = 0 + (a + 2) from by ring]
    apply stepStar_trans (r3_chain (a + 2) (a := 0) (b := 2 * (a + E + 1)) (d := 0))
    rw [show 0 + 2 * (a + 2) = 2 * a + 4 from by ring]; finish
  -- Phase 2: R4 chain
  have h2 : ⟨0, 2 * (a + E + 1), 0, 2 * a + 4, 0⟩ [fm]⊢* ⟨0, 0, 0, 2 * a + 4, 2 * (a + E + 1)⟩ := by
    rw [show (2 * (a + E + 1) : ℕ) = 0 + 2 * (a + E + 1) from by ring]
    apply stepStar_trans (r4_chain (2 * (a + E + 1)) (b := 0) (d := 2 * a + 4) (e := 0))
    ring_nf; finish
  -- Phase 3: R5+R1
  have h3 : ⟨0, 0, 0, 2 * a + 4, 2 * (a + E + 1)⟩ [fm]⊢* ⟨2, 2, 0, 2 * a + 2, 2 * (a + E + 1)⟩ := by
    rw [show 2 * a + 4 = (2 * a + 2) + 2 from by ring]
    exact r5r1_phase (2 * a + 2) (2 * (a + E + 1))
  -- Phase 4: R2+R1 chain
  have h4 : ⟨2, 2, 0, 2 * a + 2, 2 * (a + E + 1)⟩ [fm]⊢* ⟨2 * a + 4, 6 * a + 8, 0, 0, 2 * E⟩ := by
    have key := r2r1_chain (2 * a + 2) 1 2 0 (2 * E)
    rw [show 1 + 1 + (2 * a + 2) = 2 * a + 4 from by ring,
        show 2 + 3 * (2 * a + 2) = 6 * a + 8 from by ring,
        show 1 + 1 = 2 from by ring,
        show 0 + (2 * a + 2) = 2 * a + 2 from by ring,
        show 2 * E + (2 * a + 2) = 2 * (a + E + 1) from by ring] at key
    exact key
  -- Phase 5: R2 chain
  have h5 : ⟨2 * a + 4, 6 * a + 8, 0, 0, 2 * E⟩ [fm]⊢* ⟨2 * (g + 1), 6 * a + 2 * E + 8, 2 * E, 0, 0⟩ := by
    have key := r2_chain_d0 (2 * E) (a := 2 * (g + 1)) (e := 0) (b := 6 * a + 8) (c := 0)
    rw [show 2 * (g + 1) + 2 * E = 2 * a + 4 from by omega,
        show 0 + 2 * E = 2 * E from by ring,
        show 6 * a + 8 + 2 * E = 6 * a + 2 * E + 8 from by ring] at key
    exact key
  -- Phase 6: R3+R1x2 chain
  have h6 : ⟨2 * (g + 1), 6 * a + 2 * E + 8, 2 * E, 0, 0⟩ [fm]⊢* ⟨2 * a + E + 4, 6 * a + 6 * E + 8, 0, 0, 0⟩ := by
    rw [show 2 * (g + 1) = (2 * g + 1) + 1 from by ring]
    apply stepStar_trans (r3r1r1_chain E (2 * g + 1) (6 * a + 2 * E + 8))
    have : 2 * g + 1 + 1 + 3 * E = 2 * a + E + 4 := by omega
    rw [this, show 6 * a + 2 * E + 8 + 4 * E = 6 * a + 6 * E + 8 from by ring]; finish
  exact stepStar_trans h1 (stepStar_trans h2 (stepStar_trans h3 (stepStar_trans h4 (stepStar_trans h5 h6))))

-- Main transition as ⊢⁺
theorem main_trans (a E : ℕ) (hE : E ≤ a + 1) :
    ⟨a + 2, 2 * (a + E + 1), 0, 0, 0⟩ [fm]⊢⁺ ⟨2 * a + E + 4, 6 * a + 6 * E + 8, 0, 0, 0⟩ :=
  stepStar_stepPlus (main_trans_star a E hE) (by intro h; have := congr_arg Prod.fst h; omega)

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨2, 2, 0, 0, 0⟩)
  · execute fm 3
  apply progress_nonhalt (fm := fm)
    (P := fun q ↦ ∃ a E, q = ⟨a + 2, 2 * (a + E + 1), 0, 0, 0⟩ ∧ E ≤ a + 1)
  · intro c ⟨a, E, hq, hE⟩; subst hq
    refine ⟨⟨2 * a + E + 4, 6 * a + 6 * E + 8, 0, 0, 0⟩,
      ⟨2 * a + E + 2, a + 2 * E + 1, ?_, by omega⟩,
      main_trans a E hE⟩
    show (2 * a + E + 4, 6 * a + 6 * E + 8, 0, 0, 0) =
         ((2 * a + E + 2) + 2, 2 * ((2 * a + E + 2) + (a + 2 * E + 1) + 1), 0, 0, 0)
    ring_nf
  · exact ⟨0, 0, rfl, by omega⟩
