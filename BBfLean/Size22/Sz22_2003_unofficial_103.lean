import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #103: [1/30, 45/77, 35/3, 2/7, 363/2]

Vector representation:
```
-1 -1 -1  0  0
 0  2  1 -1 -1
 0 -1  1  1  0
 1  0  0 -1  0
-1  1  0  0  2
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_103

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a+1, b+1, c+1, d, e⟩ => some ⟨a, b, c, d, e⟩
  | ⟨a, b, c, d+1, e+1⟩ => some ⟨a, b+2, c+1, d, e⟩
  | ⟨a, b+1, c, d, e⟩ => some ⟨a, b, c+1, d+1, e⟩
  | ⟨a, b, c, d+1, e⟩ => some ⟨a+1, b, c, d, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b+1, c, d, e+2⟩
  | _ => none

-- R5+R1 chain: k pairs converting a and c into e
theorem r5r1_chain : ∀ k, ∀ c e, ⟨1+2*k, 0, c+k, 0, e⟩ [fm]⊢* ⟨1, 0, c, 0, e+2*k⟩ := by
  intro k; induction' k with k ih <;> intro c e
  · exists 0
  rw [show 1 + 2 * (k + 1) = (1 + 2 * k) + 1 + 1 from by ring]
  rw [show c + (k + 1) = (c + k) + 1 from by ring]
  step fm; step fm
  apply stepStar_trans (ih _ _)
  ring_nf; finish

-- R4 chain: converting d into a
theorem r4_chain : ∀ d, ∀ a c, ⟨a, 0, c, d, 0⟩ [fm]⊢* ⟨a+d, 0, c, 0, 0⟩ := by
  intro d; induction' d with d ih <;> intro a c
  · exists 0
  step fm
  apply stepStar_trans (ih _ _)
  ring_nf; finish

-- R3 drain: converting b into c and d
theorem r3_drain : ∀ b, ∀ c d, ⟨0, b, c, d, 0⟩ [fm]⊢* ⟨0, 0, c+b, d+b, 0⟩ := by
  intro b; induction' b with b ih <;> intro c d
  · exists 0
  step fm
  apply stepStar_trans (ih _ _)
  ring_nf; finish

-- R3+R2 interleaved chain: each round does R3 then R2
theorem r3r2_chain : ∀ e, ∀ b c, ⟨0, b+1, c, 0, e+1⟩ [fm]⊢* ⟨0, b+2+e, c+2*e+2, 0, 0⟩ := by
  intro e; induction' e with e ih <;> intro b c
  · step fm; step fm; finish
  · step fm; step fm
    rw [show b + 2 = (b + 1) + 1 from by ring]
    apply stepStar_trans (ih (b+1) (c+2))
    ring_nf; finish

-- Middle phase base case: e=0
theorem middle_phase_zero : ∀ c, ⟨0, 0, c, 1, 1⟩ [fm]⊢* ⟨0, 0, c+3, 2, 0⟩ := by
  intro c
  step fm
  apply stepStar_trans (r3_drain 2 (c+1) 0)
  ring_nf; finish

-- Middle phase successor case: e≥1
theorem middle_phase_succ : ∀ e, ∀ c, ⟨0, 0, c, 1, e+2⟩ [fm]⊢* ⟨0, 0, c+3*e+6, e+3, 0⟩ := by
  intro e c
  step fm
  apply stepStar_trans (r3r2_chain e 1 (c+1))
  rw [show 1 + 2 + e = e + 3 from by ring]
  apply stepStar_trans (r3_drain (e+3) (c+1+2*e+2) 0)
  ring_nf; finish

-- Full middle phase: R2 + interleaved R3/R2 + R3 drain
theorem middle_phase : ∀ e, ∀ c, ⟨0, 0, c, 1, e+1⟩ [fm]⊢* ⟨0, 0, c+3*e+3, e+2, 0⟩ := by
  intro e c
  rcases e with _ | e
  · exact middle_phase_zero c
  · rw [show (e + 1) + 1 = e + 2 from by ring]
    apply stepStar_trans (middle_phase_succ e c)
    ring_nf; finish

-- Main transition composing all phases
theorem main_trans : ∀ k, ∀ c, ⟨2*k+3, 0, c+k+1, 0, 0⟩ [fm]⊢⁺ ⟨2*k+5, 0, c+6*k+13, 0, 0⟩ := by
  intro k c
  rw [show 2*k+3 = 1+2*(k+1) from by ring]
  rw [show c+k+1 = c+(k+1) from by ring]
  apply stepStar_stepPlus_stepPlus (r5r1_chain (k+1) c 0)
  simp only [Nat.zero_add]
  rw [show 2*(k+1) = 2*k+2 from by ring]
  step fm; step fm
  rw [show 2*k+2+2 = (2*k+3)+1 from by ring]
  apply stepStar_trans (middle_phase (2*k+3) (c+1))
  apply stepStar_trans (r4_chain (2*k+5) 0 (c+1+3*(2*k+3)+3))
  simp only [Nat.zero_add]
  ring_nf; finish

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨3, 0, 7, 0, 0⟩)
  · execute fm 11
  apply progress_nonhalt (fm := fm)
    (P := fun q ↦ ∃ k c, q = ⟨2*k+3, 0, c+(k+1), 0, 0⟩)
  · intro q ⟨k, c, hq⟩; subst hq
    refine ⟨⟨2*k+5, 0, c+6*k+13, 0, 0⟩, ⟨k+1, c+5*k+11, by ring_nf⟩, ?_⟩
    rw [show c + (k + 1) = c + k + 1 from by ring]
    exact main_trans k c
  · exact ⟨0, 6, by ring_nf⟩
