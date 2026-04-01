import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #1570: [7/45, 25/77, 242/5, 3/11, 35/2]

Vector representation:
```
 0 -2 -1  1  0
 0  0  2 -1 -1
 1  0 -1  0  2
 0  1  0  0 -1
-1  0  1  1  0
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_1570

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a, b+2, c+1, d, e⟩ => some ⟨a, b, c, d+1, e⟩
  | ⟨a, b, c, d+1, e+1⟩ => some ⟨a, b, c+2, d, e⟩
  | ⟨a, b, c+1, d, e⟩ => some ⟨a+1, b, c, d, e+2⟩
  | ⟨a, b, c, d, e+1⟩ => some ⟨a, b+1, c, d, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b, c+1, d+1, e⟩
  | _ => none

theorem r5_step : ⟨a + 1, b, 0, d, 0⟩ [fm]⊢ ⟨a, b, 1, d + 1, 0⟩ := by simp [fm]

theorem e_to_b : ∀ k, ⟨a, b, 0, 0, e + k⟩ [fm]⊢* ⟨a, b + k, 0, 0, e⟩ := by
  intro k; induction' k with k ih generalizing a b e
  · exists 0
  · rw [Nat.add_succ e k]; step fm
    apply stepStar_trans (ih (b := b + 1)); ring_nf; finish

theorem drain_pair : ⟨a + 1, b + 2, 0, d, 0⟩ [fm]⊢⁺ ⟨a, b, 0, d + 2, 0⟩ := by
  step fm; step fm; finish

theorem drain_chain : ∀ k, ⟨a + k, b + 2 * k, 0, d, 0⟩ [fm]⊢* ⟨a, b, 0, d + 2 * k, 0⟩ := by
  intro k; induction' k with k ih generalizing a b d
  · exists 0
  · rw [show a + (k + 1) = (a + 1) + k from by ring,
        show b + 2 * (k + 1) = (b + 2) + 2 * k from by ring]
    apply stepStar_trans (ih (a := a + 1) (b := b + 2))
    rw [show d + 2 * (k + 1) = (d + 2 * k) + 2 from by ring]
    exact stepPlus_stepStar drain_pair

theorem r3_chain_b0 : ∀ k, ⟨a, 0, c + k, 0, e⟩ [fm]⊢* ⟨a + k, 0, c, 0, e + 2 * k⟩ := by
  intro k; induction' k with k ih generalizing a c e
  · exists 0
  · rw [show c + (k + 1) = (c + k) + 1 from by ring]; step fm
    apply stepStar_trans (ih (a := a + 1) (e := e + 2)); ring_nf; finish

theorem r3_chain_b1 : ∀ k, ⟨a, 1, c + k, 0, e⟩ [fm]⊢* ⟨a + k, 1, c, 0, e + 2 * k⟩ := by
  intro k; induction' k with k ih generalizing a c e
  · exists 0
  · rw [show c + (k + 1) = (c + k) + 1 from by ring]; step fm
    apply stepStar_trans (ih (a := a + 1) (e := e + 2)); ring_nf; finish

theorem r2r2r3_round_b0 : ⟨a, 0, c, d + 2, 2⟩ [fm]⊢⁺ ⟨a + 1, 0, c + 3, d, 2⟩ := by
  step fm; step fm; step fm; finish

theorem r2r2r3_chain_b0 : ∀ k, ⟨a, 0, c, d + 2 * k, 2⟩ [fm]⊢* ⟨a + k, 0, c + 3 * k, d, 2⟩ := by
  intro k; induction' k with k ih generalizing a c d
  · exists 0
  · rw [show d + 2 * (k + 1) = (d + 2) + 2 * k from by ring]
    apply stepStar_trans (ih (d := d + 2))
    exact stepPlus_stepStar r2r2r3_round_b0

theorem r2r2r3_round_b1 : ⟨a, 1, c, d + 2, 2⟩ [fm]⊢⁺ ⟨a + 1, 1, c + 3, d, 2⟩ := by
  step fm; step fm; step fm; finish

theorem r2r2r3_chain_b1 : ∀ k, ⟨a, 1, c, d + 2 * k, 2⟩ [fm]⊢* ⟨a + k, 1, c + 3 * k, d, 2⟩ := by
  intro k; induction' k with k ih generalizing a c d
  · exists 0
  · rw [show d + 2 * (k + 1) = (d + 2) + 2 * k from by ring]
    apply stepStar_trans (ih (d := d + 2))
    exact stepPlus_stepStar r2r2r3_round_b1

-- Build from (a+1, 0, 0, 2*m, 0): R5,R3 opening then m rounds then R2,R3 ending then R3 chain
-- D = 2*m (even). D+1 = 2*m+1 (odd). m rounds: d goes from 2*m+1 to 1.
-- Then R2,R3, R3 chain. Result: (a+4*m+3, 0, 0, 0, 6*m+5).
theorem build_b0_even :
    ⟨a + 1, 0, 0, 2 * m, 0⟩ [fm]⊢⁺ ⟨a + 4 * m + 3, 0, 0, 0, 6 * m + 5⟩ := by
  refine step_stepPlus_stepPlus (r5_step (b := 0)) ?_
  show ⟨a, 0, 0 + 1, 2 * m + 1, 0⟩ [fm]⊢⁺ _
  step fm -- R3: (a+1, 0, 0, 2*m+1, 2)
  rw [show 2 * m + 1 = 1 + 2 * m from by ring]
  apply stepStar_trans (r2r2r3_chain_b0 m (a := a + 1) (c := 0) (d := 1))
  -- now at (a+1+m, 0, 3*m, 1, 2)
  rw [show 0 + 3 * m = 3 * m from by ring]
  step fm -- R2: (a+1+m, 0, 3*m+2, 0, 1)
  step fm -- R3: (a+1+m+1, 0, 3*m+1, 0, 3)
  rw [show a + 1 + m + 1 = a + m + 2 from by ring,
      show 3 * m + 1 = 0 + (3 * m + 1) from by ring]
  apply stepStar_trans (r3_chain_b0 (3 * m + 1) (a := a + m + 2) (c := 0) (e := 3))
  ring_nf; finish

-- Build from (a+1, 0, 0, 2*m+1, 0): D = 2*m+1 (odd). D+1 = 2*(m+1) (even).
-- (m+1) rounds: d goes from 2*(m+1) to 0.
-- Then R3 chain. Result: (a+4*m+5, 0, 0, 0, 6*m+8).
theorem build_b0_odd :
    ⟨a + 1, 0, 0, 2 * m + 1, 0⟩ [fm]⊢⁺ ⟨a + 4 * m + 5, 0, 0, 0, 6 * m + 8⟩ := by
  refine step_stepPlus_stepPlus (r5_step (b := 0)) ?_
  show ⟨a, 0, 0 + 1, 2 * m + 2, 0⟩ [fm]⊢⁺ _
  step fm -- R3: (a+1, 0, 0, 2*m+2, 2)
  rw [show 2 * m + 2 = 0 + 2 * (m + 1) from by ring]
  apply stepStar_trans (r2r2r3_chain_b0 (m + 1) (a := a + 1) (c := 0) (d := 0))
  rw [show a + 1 + (m + 1) = a + m + 2 from by ring,
      show 0 + 3 * (m + 1) = 0 + (3 * m + 3) from by ring]
  apply stepStar_trans (r3_chain_b0 (3 * m + 3) (a := a + m + 2) (c := 0) (e := 2))
  ring_nf; finish

-- Build from (a+1, 1, 0, 2*m, 0): same interleaving but b=1, then R4 at end.
-- Result: (a+4*m+3, 6*m+6, 0, 0, 0).
theorem build_b1_even :
    ⟨a + 1, 1, 0, 2 * m, 0⟩ [fm]⊢⁺ ⟨a + 4 * m + 3, 6 * m + 6, 0, 0, 0⟩ := by
  refine step_stepPlus_stepPlus (r5_step (b := 1)) ?_
  show ⟨a, 1, 0 + 1, 2 * m + 1, 0⟩ [fm]⊢⁺ _
  step fm -- R3: (a+1, 1, 0, 2*m+1, 2)
  rw [show 2 * m + 1 = 1 + 2 * m from by ring]
  apply stepStar_trans (r2r2r3_chain_b1 m (a := a + 1) (c := 0) (d := 1))
  rw [show 0 + 3 * m = 3 * m from by ring]
  step fm -- R2
  step fm -- R3
  rw [show a + 1 + m + 1 = a + m + 2 from by ring,
      show 3 * m + 1 = 0 + (3 * m + 1) from by ring]
  apply stepStar_trans (r3_chain_b1 (3 * m + 1) (a := a + m + 2) (c := 0) (e := 3))
  rw [show a + m + 2 + (3 * m + 1) = a + 4 * m + 3 from by ring,
      show 3 + 2 * (3 * m + 1) = 0 + (6 * m + 5) from by ring]
  apply stepStar_trans (e_to_b (6 * m + 5) (a := a + 4 * m + 3) (b := 1) (e := 0))
  ring_nf; finish

-- Full 2-step transition:
-- (f+m+2, 2*m, 0, 0, 0) →⁺ (f+13*m+12, 18*m+18, 0, 0, 0)
-- Phase 1: Even drain m pairs: →* (f+2, 0, 0, 2*m, 0)
-- Phase 2: Build b0 even: →⁺ (f+4*m+4, 0, 0, 0, 6*m+5)
-- Phase 3: R4 chain: →* (f+4*m+4, 6*m+5, 0, 0, 0)
-- Phase 4: Odd drain (3*m+2) pairs: →* (f+m+2, 1, 0, 6*m+4, 0)
-- Phase 5: Build b1 even: →⁺ (f+13*m+12, 18*m+18, 0, 0, 0)
theorem two_step_trans :
    ⟨f + m + 2, 2 * m, 0, 0, 0⟩ [fm]⊢⁺ ⟨f + 13 * m + 12, 18 * m + 18, 0, 0, 0⟩ := by
  -- Phase 1: even drain
  rw [show f + m + 2 = (f + 2) + m from by ring,
      show 2 * m = 0 + 2 * m from by ring]
  apply stepStar_stepPlus_stepPlus (drain_chain m (a := f + 2) (b := 0) (d := 0))
  rw [show 0 + 2 * m = 2 * m from by ring]
  -- Phase 2: build b0 even
  rw [show f + 2 = (f + 1) + 1 from by ring]
  apply stepPlus_stepStar_stepPlus (build_b0_even (a := f + 1) (m := m))
  rw [show f + 1 + 4 * m + 3 = f + 4 * m + 4 from by ring]
  -- Phase 3: R4 chain
  rw [show 6 * m + 5 = 0 + (6 * m + 5) from by ring]
  apply stepStar_trans (e_to_b (6 * m + 5) (a := f + 4 * m + 4) (b := 0) (e := 0))
  rw [show 0 + (6 * m + 5) = 6 * m + 5 from by ring]
  -- Phase 4: odd drain
  rw [show f + 4 * m + 4 = (f + m + 2) + (3 * m + 2) from by ring,
      show 6 * m + 5 = 1 + 2 * (3 * m + 2) from by ring]
  apply stepStar_trans (drain_chain (3 * m + 2) (a := f + m + 2) (b := 1) (d := 0))
  rw [show 0 + 2 * (3 * m + 2) = 6 * m + 4 from by ring]
  -- Phase 5: build b1 even
  rw [show f + m + 2 = (f + m + 1) + 1 from by ring,
      show 6 * m + 4 = 2 * (3 * m + 2) from by ring]
  apply stepStar_trans (stepPlus_stepStar (build_b1_even (a := f + m + 1) (m := 3 * m + 2)))
  ring_nf; finish

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨11, 18, 0, 0, 0⟩) (by execute fm 48)
  apply progress_nonhalt_simple (fm := fm) (A := ℕ × ℕ)
    (fun ⟨f, m⟩ ↦ ⟨f + m + 2, 2 * m, 0, 0, 0⟩) ⟨0, 9⟩
  intro ⟨f, m⟩; exists ⟨f + 4 * m + 1, 9 * m + 9⟩
  show ⟨f + m + 2, 2 * m, 0, 0, 0⟩ [fm]⊢⁺ ⟨(f + 4 * m + 1) + (9 * m + 9) + 2, 2 * (9 * m + 9), 0, 0, 0⟩
  rw [show (f + 4 * m + 1) + (9 * m + 9) + 2 = f + 13 * m + 12 from by ring,
      show 2 * (9 * m + 9) = 18 * m + 18 from by ring]
  exact two_step_trans
