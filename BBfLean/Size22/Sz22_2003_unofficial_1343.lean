import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #1343: [63/10, 28/33, 11/2, 5/7, 6/11]

Vector representation:
```
-1  2 -1  1  0
 2 -1  0  1 -1
-1  0  0  0  1
 0  0  1 -1  0
 1  1  0  0 -1
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_1343

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a+1, b, c+1, d, e⟩ => some ⟨a, b+2, c, d+1, e⟩
  | ⟨a, b+1, c, d, e+1⟩ => some ⟨a+2, b, c, d+1, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b, c, d, e+1⟩
  | ⟨a, b, c, d+1, e⟩ => some ⟨a, b, c+1, d, e⟩
  | ⟨a, b, c, d, e+1⟩ => some ⟨a+1, b+1, c, d, e⟩
  | _ => none

-- R3 drain: transfer a to e (b=0, c=0 so R1/R2 don't fire)
theorem r3_drain : ∀ j, ∀ d e, ⟨j, (0:ℕ), (0:ℕ), d, e⟩ [fm]⊢* ⟨0, 0, 0, d, e + j⟩ := by
  intro j; induction' j with j ih
  · intro d e; exists 0
  · intro d e; step fm
    apply stepStar_trans (ih d (e + 1)); ring_nf; finish

-- R4 drain: transfer d to c (a=0, b=0 so R1/R2/R3 don't fire)
theorem r4_drain : ∀ k, ∀ d e, ⟨(0:ℕ), (0:ℕ), (0:ℕ), d + k, e⟩ [fm]⊢* ⟨(0:ℕ), 0, k, d, e⟩ := by
  intro k; induction' k with k ih
  · intro d e; exists 0
  · intro d e
    rw [show d + (k + 1) = (d + 1) + k from by ring]
    apply stepStar_trans (ih (d + 1) e)
    step fm; finish

-- R1,R1,R2 chain (even c = 2k): each round does c -= 2, e -= 1, b += 3, d += 3
theorem r112_even : ∀ k, ∀ b d e, ⟨(2:ℕ), b, 2 * k, d, e + k⟩ [fm]⊢* ⟨2, b + 3 * k, 0, d + 3 * k, e⟩ := by
  intro k; induction' k with k ih
  · intro b d e; simp; exists 0
  · intro b d e
    rw [show 2 * (k + 1) = 2 * k + 2 from by ring,
        show e + (k + 1) = (e + k) + 1 from by ring]
    step fm; step fm; step fm
    apply stepStar_trans (ih (b + 3) (d + 3) e); ring_nf; finish

-- R1,R1,R2 chain (odd c = 2k+1): k rounds then one R1+R2
theorem r112_odd : ∀ k, ∀ b d e, ⟨(2:ℕ), b, 2 * k + 1, d, e + k + 1⟩ [fm]⊢* ⟨3, b + 3 * k + 1, 0, d + 3 * k + 2, e⟩ := by
  intro k; induction' k with k ih
  · intro b d e; step fm; step fm; ring_nf; finish
  · intro b d e
    rw [show 2 * (k + 1) + 1 = (2 * k + 1) + 2 from by ring,
        show e + (k + 1) + 1 = (e + k + 1) + 1 from by ring]
    step fm; step fm; step fm
    apply stepStar_trans (ih (b + 3) (d + 3) e); ring_nf; finish

-- Drain chain: process (a+1, b, 0, d, e) down to (0, 0, 0, d+b, a+1+b+e)
theorem drain_chain : ∀ b, ∀ a d e, ⟨a + 1, b, (0:ℕ), d, e⟩ [fm]⊢* ⟨0, 0, 0, d + b, a + 1 + b + e⟩ := by
  intro b; induction' b with b ih
  · intro a d e
    rw [show d + 0 = d from by ring, show a + 1 + 0 + e = e + (a + 1) from by ring]
    exact r3_drain (a + 1) d e
  · intro a d e
    rcases e with _ | e
    · -- e = 0: R3 step then R2 step, then IH
      step fm; step fm
      apply stepStar_trans (ih (a + 1) (d + 1) 0); ring_nf; finish
    · -- e ≥ 1: R2 step, then IH
      step fm
      apply stepStar_trans (ih (a + 2) (d + 1) e); ring_nf; finish

-- Main transition (D odd, d = 2m):
-- (0, 0, 0, 2m+1, e'+m+2) ⊢⁺ (0, 0, 0, 6m+4, 3m+e'+4)
theorem main_even (m e' : ℕ) :
    ⟨(0:ℕ), 0, 0, 2 * m + 1, e' + m + 2⟩ [fm]⊢⁺ ⟨0, 0, 0, 6 * m + 4, 3 * m + e' + 4⟩ := by
  -- Phase 1: R4 drain d to c
  rw [show (2 * m + 1 : ℕ) = 0 + (2 * m + 1) from by ring]
  apply stepStar_stepPlus_stepPlus (r4_drain (2 * m + 1) 0 (e' + m + 2))
  -- State: ⟨0, 0, 2*m+1, 0, e'+m+2⟩
  -- Phase 2: Opening (R5, R1, R2)
  rw [show e' + m + 2 = (e' + m + 1) + 1 from by ring]
  step fm
  rw [show 2 * m + 1 = (2 * m) + 1 from by ring]
  step fm
  rw [show (3 : ℕ) = 2 + 1 from rfl,
      show e' + m + 1 = (e' + m) + 1 from by ring]
  step fm
  -- State: ⟨2, 2, 2*m, 2, e'+m⟩
  -- Phase 3: r112_even chain
  apply stepStar_trans (r112_even m 2 2 e')
  -- State: ⟨2, 2+3*m, 0, 2+3*m, e'⟩
  -- Phase 4: drain_chain
  apply stepStar_trans (drain_chain (2 + 3 * m) 1 (2 + 3 * m) e')
  ring_nf; finish

-- Main transition (D even, d = 2m+1):
-- (0, 0, 0, 2m+2, e'+m+3) ⊢⁺ (0, 0, 0, 6m+7, 3m+e'+6)
theorem main_odd (m e' : ℕ) :
    ⟨(0:ℕ), 0, 0, 2 * m + 2, e' + m + 3⟩ [fm]⊢⁺ ⟨0, 0, 0, 6 * m + 7, 3 * m + e' + 6⟩ := by
  -- Phase 1: R4 drain
  rw [show (2 * m + 2 : ℕ) = 0 + (2 * m + 2) from by ring]
  apply stepStar_stepPlus_stepPlus (r4_drain (2 * m + 2) 0 (e' + m + 3))
  -- Phase 2: Opening
  rw [show e' + m + 3 = (e' + m + 2) + 1 from by ring]
  step fm
  rw [show 2 * m + 2 = (2 * m + 1) + 1 from by ring]
  step fm
  rw [show (3 : ℕ) = 2 + 1 from rfl,
      show e' + m + 2 = (e' + m + 1) + 1 from by ring]
  step fm
  -- State: ⟨2, 2, 2*m+1, 2, e'+m+1⟩
  -- Phase 3: r112_odd chain
  apply stepStar_trans (r112_odd m 2 2 e')
  -- State: ⟨3, 2+3*m+1, 0, 2+3*m+2, e'⟩
  rw [show 2 + 3 * m + 1 = 3 + 3 * m from by ring,
      show 2 + 3 * m + 2 = 4 + 3 * m from by ring]
  -- Phase 4: drain_chain
  apply stepStar_trans (drain_chain (3 + 3 * m) 2 (4 + 3 * m) e')
  ring_nf; finish

-- Combined main transition:
-- (0, 0, 0, d+1, e+2) ⊢⁺ (0, 0, 0, 3*d+4, d+e+4) when 2*e ≥ d
theorem main_trans (d e : ℕ) (h : 2 * e ≥ d) :
    ⟨(0:ℕ), 0, 0, d + 1, e + 2⟩ [fm]⊢⁺ ⟨0, 0, 0, 3 * d + 4, d + e + 4⟩ := by
  rcases Nat.even_or_odd d with ⟨m, hm⟩ | ⟨m, hm⟩
  · -- d = m + m (even)
    subst hm
    have hm' : e ≥ m := by omega
    obtain ⟨e', rfl⟩ := Nat.exists_eq_add_of_le hm'
    rw [show m + m = 2 * m from by ring,
        show m + e' + 2 = e' + m + 2 from by ring,
        show 3 * (2 * m) + 4 = 6 * m + 4 from by ring,
        show 2 * m + (m + e') + 4 = 3 * m + e' + 4 from by ring]
    exact main_even m e'
  · -- d = 2*m + 1 (odd)
    subst hm
    have hm' : e ≥ m + 1 := by omega
    obtain ⟨e', rfl⟩ := Nat.exists_eq_add_of_le hm'
    rw [show 2 * m + 1 + 1 = 2 * m + 2 from by ring,
        show m + 1 + e' + 2 = e' + m + 3 from by ring,
        show 3 * (2 * m + 1) + 4 = 6 * m + 7 from by ring,
        show 2 * m + 1 + (m + 1 + e') + 4 = 3 * m + e' + 6 from by ring]
    exact main_odd m e'

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨0, 0, 0, 1, 2⟩) (by execute fm 6)
  apply progress_nonhalt (fm := fm)
    (P := fun q ↦ ∃ d e : ℕ, q = ⟨0, 0, 0, d + 1, e + 2⟩ ∧ 2 * e ≥ d)
  · intro c ⟨d, e, hq, hge⟩
    exact ⟨⟨0, 0, 0, 3 * d + 4, d + e + 4⟩,
      ⟨3 * d + 3, d + e + 2, by ring_nf, by omega⟩,
      hq ▸ main_trans d e hge⟩
  · exact ⟨0, 0, rfl, by omega⟩

end Sz22_2003_unofficial_1343
