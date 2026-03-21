import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz21_140_unofficial #60: [4/15, 3/14, 275/2, 7/5, 10/11]

Vector representation:
```
 2 -1 -1  0  0
-1  1  0 -1  0
-1  0  2  0  1
 0  0 -1  1  0
 1  0  1  0 -1
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz21_140_unofficial_60

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a, b+1, c+1, d, e⟩ => some ⟨a+2, b, c, d, e⟩
  | ⟨a+1, b, c, d+1, e⟩ => some ⟨a, b+1, c, d, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b, c+2, d, e+1⟩
  | ⟨a, b, c+1, d, e⟩ => some ⟨a, b, c, d+1, e⟩
  | ⟨a, b, c, d, e+1⟩ => some ⟨a+1, b, c+1, d, e⟩
  | _ => none

-- c_to_d: move c to d
theorem c_to_d : ⟨0, 0, c+k, d, e⟩ [fm]⊢* ⟨0, 0, c, d+k, e⟩ := by
  have many_step : ∀ k c d, ⟨0, 0, c+k, d, e⟩ [fm]⊢* ⟨0, 0, c, d+k, e⟩ := by
    intro k; induction' k with k h <;> intro c d
    · exists 0
    rw [← Nat.add_assoc]
    step fm
    apply stepStar_trans (h _ _)
    ring_nf; finish
  exact many_step k c d

-- r3_chain: convert a to c and e
theorem r3_chain : ⟨a+k, 0, c, 0, e⟩ [fm]⊢* ⟨a, 0, c+2*k, 0, e+k⟩ := by
  have many_step : ∀ k a c e, ⟨a+k, 0, c, 0, e⟩ [fm]⊢* ⟨a, 0, c+2*k, 0, e+k⟩ := by
    intro k; induction' k with k h <;> intro a c e
    · exists 0
    rw [← Nat.add_assoc]
    step fm
    apply stepStar_trans (h _ _ _)
    ring_nf; finish
  exact many_step k a c e

-- main_loop_step: one iteration of the inner loop
theorem main_loop_step : ⟨0, b+1, 0, d+3, e+1⟩ [fm]⊢* ⟨0, b+3, 0, d, e⟩ := by
  step fm; step fm; step fm; step fm; step fm; finish

-- main_loop_gen: k iterations of the inner loop
theorem main_loop_gen : ⟨0, b+2, 0, 3*k+2, e+k⟩ [fm]⊢* ⟨0, b+2*k+2, 0, 2, e⟩ := by
  have many_step : ∀ k b e, ⟨0, b+2, 0, 3*k+2, e+k⟩ [fm]⊢* ⟨0, b+2*k+2, 0, 2, e⟩ := by
    intro k; induction' k with k h <;> intro b e
    · exists 0
    rw [show 3 * (k + 1) + 2 = (3 * k + 2) + 3 from by ring,
        show e + (k + 1) = (e + k) + 1 from by ring,
        show b + 2 = (b + 1) + 1 from by ring]
    apply stepStar_trans (main_loop_step (b := b+1) (d := 3*k+2) (e := e+k))
    rw [show b + 1 + 3 = (b + 2) + 2 from by ring]
    apply stepStar_trans (h (b + 2) e)
    ring_nf; finish
  exact many_step k b e

-- main_loop_full: full inner loop from b=0
theorem main_loop_full : ⟨0, 0, 0, 3*k+5, e+k+1⟩ [fm]⊢* ⟨0, 2*k+2, 0, 2, e⟩ := by
  rw [show 3 * k + 5 = (3 * k + 2) + 3 from by ring,
      show e + k + 1 = (e + k) + 1 from by ring]
  step fm; step fm; step fm; step fm; step fm
  rw [show (2 : ℕ) = 0 + 2 from by ring]
  apply stepStar_trans (main_loop_gen (b := 0) (k := k) (e := e))
  ring_nf; finish

-- residue_d2: handle d=2 residue
theorem residue_d2 : ⟨0, b+2, 0, 2, e+1⟩ [fm]⊢⁺ ⟨4, b+1, 0, 0, e+1⟩ := by
  execute fm 7

-- r3_r1_r1_step: one 3-step cycle
theorem r3_r1_r1_step : ⟨a+1, b+2, 0, 0, e⟩ [fm]⊢* ⟨a+4, b, 0, 0, e+1⟩ := by
  step fm; step fm; step fm; finish

-- r3_r1_r1_loop: iterated 3-step cycle
theorem r3_r1_r1_loop : ⟨a+1, b+2*k, 0, 0, e⟩ [fm]⊢* ⟨a+3*k+1, b, 0, 0, e+k⟩ := by
  have many_step : ∀ k a e, ⟨a+1, b+2*k, 0, 0, e⟩ [fm]⊢* ⟨a+3*k+1, b, 0, 0, e+k⟩ := by
    intro k; induction' k with k h <;> intro a e
    · exists 0
    rw [show b + 2 * (k + 1) = (b + 2 * k) + 2 from by ring]
    apply stepStar_trans r3_r1_r1_step
    rw [show a + 4 = (a + 3) + 1 from by ring]
    apply stepStar_trans (h _ _)
    ring_nf; finish
  exact many_step k a e

-- final_phase: R3 then R1
theorem final_phase : ⟨a+2, 1, 0, 0, e⟩ [fm]⊢⁺ ⟨a+3, 0, 1, 0, e+1⟩ := by
  execute fm 2

-- full_transition: one complete cycle
theorem full_transition :
    ⟨0, 0, 3*m+5, 0, m+e+2⟩ [fm]⊢⁺ ⟨0, 0, 6*m+11, 0, 4*m+e+7⟩ := by
  -- Phase 1: c_to_d
  rw [show (3*m+5 : ℕ) = 0 + (3*m+5) from by ring]
  apply stepStar_stepPlus_stepPlus (c_to_d (c := 0) (k := 3*m+5))
  simp only [Nat.zero_add]
  -- Phase 2: main_loop_full
  rw [show m + e + 2 = (e + 1) + m + 1 from by ring]
  apply stepStar_stepPlus_stepPlus (main_loop_full (k := m) (e := e + 1))
  -- Phase 3: residue_d2
  rw [show 2 * m + 2 = (2 * m) + 2 from by ring]
  apply stepPlus_stepStar_stepPlus (residue_d2 (b := 2*m) (e := e))
  -- Phase 4: r3_r1_r1_loop
  rw [show (4 : ℕ) = 3 + 1 from by ring, show 2 * m + 1 = 1 + 2 * m from by ring]
  apply stepStar_trans (r3_r1_r1_loop (a := 3) (b := 1) (k := m) (e := e + 1))
  -- Phase 5: final_phase
  rw [show 3 + 3 * m + 1 = (3 * m + 2) + 2 from by ring,
      show e + 1 + m = e + m + 1 from by ring]
  apply stepStar_trans (stepPlus_stepStar (final_phase (a := 3*m+2) (e := e+m+1)))
  -- Phase 6: r3_chain
  rw [show 3 * m + 2 + 3 = 0 + (3 * m + 5) from by ring]
  apply stepStar_trans (r3_chain (a := 0) (k := 3*m+5) (c := 1) (e := e+m+1+1))
  ring_nf; finish

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨0, 0, 5, 0, 3⟩) (by execute fm 11)
  apply progress_nonhalt_simple (fm := fm) (A := ℕ × ℕ)
    (fun p ↦ ⟨0, 0, 3*p.1+5, 0, p.1+p.2+2⟩) ⟨0, 1⟩
  intro ⟨m, e⟩; dsimp only
  refine ⟨⟨2*m+2, 2*m+e+3⟩, ?_⟩; dsimp only
  rw [show 3 * (2 * m + 2) + 5 = 6 * m + 11 from by ring,
      show 2 * m + 2 + (2 * m + e + 3) + 2 = 4 * m + e + 7 from by ring]
  exact full_transition
