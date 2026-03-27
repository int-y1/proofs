import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #465: [28/15, 21/22, 175/2, 11/7, 3/5]

Vector representation:
```
 2 -1 -1  1  0
-1  1  0  1 -1
-1  0  2  1  0
 0  0  0 -1  1
 0  1 -1  0  0
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_465

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a, b+1, c+1, d, e⟩ => some ⟨a+2, b, c, d+1, e⟩
  | ⟨a+1, b, c, d, e+1⟩ => some ⟨a, b+1, c, d+1, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b, c+2, d+1, e⟩
  | ⟨a, b, c, d+1, e⟩ => some ⟨a, b, c, d, e+1⟩
  | ⟨a, b, c+1, d, e⟩ => some ⟨a, b+1, c, d, e⟩
  | _ => none

-- R4 chain: d to e
theorem d_to_e : ∀ k, ∀ c d, ⟨0, 0, c, d + k, 0⟩ [fm]⊢* ⟨0, 0, c, d, k⟩ := by
  intro k; induction k with
  | zero => intro c d; exists 0
  | succ k ih =>
    intro c d
    rw [show d + (k + 1) = (d + 1) + k from by ring]
    apply stepStar_trans (ih c (d + 1))
    step fm; finish

-- R3 chain: a to c (c increases by 2 per step, d increases by 1)
theorem a_to_c : ∀ k, ∀ a c d, ⟨a + k, 0, c, d, 0⟩ [fm]⊢* ⟨a, 0, c + 2 * k, d + k, 0⟩ := by
  intro k; induction k with
  | zero => intro a c d; exists 0
  | succ k ih =>
    intro a c d
    rw [show a + (k + 1) = (a + k) + 1 from by ring]
    step fm
    apply stepStar_trans (ih a (c + 2) (d + 1))
    ring_nf; finish

-- R2R1 chain: interleaved R2, R1 pairs
theorem r2r1_chain : ∀ k, ∀ a c d e,
    ⟨a + 1, 0, c + k, d, e + k⟩ [fm]⊢* ⟨a + k + 1, 0, c, d + 2 * k, e⟩ := by
  intro k; induction k with
  | zero => intro a c d e; exists 0
  | succ k ih =>
    intro a c d e
    rw [show c + (k + 1) = (c + k) + 1 from by ring,
        show e + (k + 1) = (e + k) + 1 from by ring]
    step fm  -- R2
    step fm  -- R1
    rw [show a + 2 = (a + 1) + 1 from by ring,
        show d + 1 + 1 = d + 2 from by ring]
    apply stepStar_trans (ih (a + 1) c (d + 2) e)
    ring_nf; finish

-- R2 drain: consume e via R2 (b accumulates)
theorem r2_drain : ∀ k, ∀ a b d,
    ⟨a + k, b, 0, d, k⟩ [fm]⊢* ⟨a, b + k, 0, d + k, 0⟩ := by
  intro k; induction k with
  | zero => intro a b d; exists 0
  | succ k ih =>
    intro a b d
    rw [show a + (k + 1) = (a + k) + 1 from by ring]
    step fm  -- R2
    apply stepStar_trans (ih a (b + 1) (d + 1))
    ring_nf; finish

-- Combined phase: reduce (a+1, b, 0, d, 0) to (0, 0, 2*a+2+3*b, d+a+1+3*b, 0)
theorem ab_phase : ∀ b, ∀ a d,
    ⟨a + 1, b, 0, d, 0⟩ [fm]⊢* ⟨0, 0, 2 * a + 2 + 3 * b, d + a + 1 + 3 * b, 0⟩ := by
  intro b; induction' b using Nat.strongRecOn with b ih; intro a d
  rcases b with _ | b
  · -- b = 0: pure R3 chain
    rw [show a + 1 = 0 + (a + 1) from by ring]
    apply stepStar_trans (a_to_c (a + 1) 0 0 d)
    ring_nf; finish
  · -- b + 1
    step fm  -- R3: (a+1, b+1, 0, d, 0) -> (a, b+1, 2, d+1, 0)
    step fm  -- R1: (a, b+1, 2, d+1, 0) -> (a+2, b, 1, d+2, 0)
    rcases b with _ | b
    · -- b = 0: R3 chain from (a+2, 0, 1, d+2, 0)
      rw [show a + 2 = 0 + (a + 2) from by ring,
          show d + 1 + 1 = d + 2 from by ring]
      apply stepStar_trans (a_to_c (a + 2) 0 1 (d + 2))
      ring_nf; finish
    · -- b + 1: R1 step then IH
      rw [show d + 1 + 1 = d + 2 from by ring]
      step fm  -- R1: (a+2, b+1, 1, d+2, 0) -> (a+4, b, 0, d+3, 0)
      rw [show a + 2 + 2 = (a + 3) + 1 from by ring,
          show d + 2 + 1 = d + 3 from by ring]
      apply stepStar_trans (ih b (by omega) (a + 3) (d + 3))
      ring_nf; finish

-- Main transition: (0, 0, c+2, 0, e+1) ⊢⁺ (0, 0, c+e+5, 0, 3*e+6)
-- Requires c ≤ e+1 and e ≤ 2*c
theorem main_trans (c e : ℕ) (hce : c ≤ e + 1) (hec : e ≤ 2 * c) :
    ⟨0, 0, c + 2, 0, e + 1⟩ [fm]⊢⁺ ⟨0, 0, c + e + 5, 0, 3 * e + 6⟩ := by
  -- Introduce named differences to help omega with nat subtraction
  -- p = e + 1 - c (number of R2 drain rounds), p ≥ 1 since c ≤ e + 1
  obtain ⟨p, hp⟩ : ∃ p, e + 1 = p + c := ⟨e + 1 - c, by omega⟩
  -- s = 2c - e (used in ab_phase), s ≥ 0 since e ≤ 2c
  obtain ⟨s, hs⟩ : ∃ s, 2 * c = s + e := ⟨2 * c - e, by omega⟩
  -- Note: c + 2 = (s + 1) + p since c+2 = (2c-e+1) + (e+1-c) = s+1+p
  have hrp : c + 2 = (s + 1) + p := by omega
  -- Phase 1+2: R5, R1 (2 steps giving ⊢⁺)
  rw [show c + 2 = (c + 1) + 1 from by ring]
  step fm  -- R5
  step fm  -- R1: -> (2, 0, c, 1, e+1)
  -- Phase 3: R2R1 chain (c rounds)
  rw [show (2 : ℕ) = 1 + 1 from by ring,
      show c = 0 + c from by ring, hp]
  apply stepStar_trans (r2r1_chain c 1 0 1 p)
  -- State: (1+c+1, 0, 0, 1+2*c, p)
  rw [show 1 + c + 1 = c + 2 from by ring, hrp,
      show 1 + 2 * c = 2 * c + 1 from by ring]
  -- Phase 4: R2 drain (p rounds)
  apply stepStar_trans (r2_drain p (s + 1) 0 (2 * c + 1))
  -- State: (s+1, p, 0, 2*c+1+p, 0)
  rw [show 0 + p = p from by ring,
      show 2 * c + 1 + p = c + e + 2 from by omega]
  -- Phase 5: ab_phase
  apply stepStar_trans (ab_phase p s (c + e + 2))
  -- Phase 6: d_to_e
  rw [show 2 * s + 2 + 3 * p = c + e + 5 from by omega,
      show c + e + 2 + s + 1 + 3 * p = 0 + (3 * e + 6) from by omega]
  apply stepStar_trans (d_to_e (3 * e + 6) (c + e + 5) 0)
  ring_nf; finish

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨0, 0, 2, 0, 1⟩) (by execute fm 2)
  apply progress_nonhalt (fm := fm)
    (P := fun q ↦ ∃ c e, q = ⟨0, 0, c + 2, 0, e + 1⟩ ∧ c ≤ e + 1 ∧ e ≤ 2 * c)
  · intro q ⟨c, e, hq, hce, hec⟩; subst hq
    exact ⟨⟨0, 0, c + e + 5, 0, 3 * e + 6⟩,
      ⟨c + e + 3, 3 * e + 5, by ring_nf, by omega, by omega⟩,
      main_trans c e hce hec⟩
  · exact ⟨0, 0, by ring_nf, by omega, by omega⟩

end Sz22_2003_unofficial_465
