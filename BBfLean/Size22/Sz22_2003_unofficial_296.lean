import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #296: [15/2, 1/147, 26/33, 847/5, 3/169]

Vector representation:
```
-1  1  1  0  0  0
 0 -1  0 -2  0  0
 1 -1  0  0 -1  1
 0  0 -1  1  2  0
 0  1  0  0  0 -2
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_296

def Q := ℕ × ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a+1, b, c, d, e, f⟩ => some ⟨a, b+1, c+1, d, e, f⟩
  | ⟨a, b+1, c, d+2, e, f⟩ => some ⟨a, b, c, d, e, f⟩
  | ⟨a, b+1, c, d, e+1, f⟩ => some ⟨a+1, b, c, d, e, f+1⟩
  | ⟨a, b, c+1, d, e, f⟩ => some ⟨a, b, c, d+1, e+2, f⟩
  | ⟨a, b, c, d, e, f+2⟩ => some ⟨a, b+1, c, d, e, f⟩
  | _ => none

-- R3+R1 loop: converts e into c and f
theorem r3r1_loop : ∀ k c f,
    ⟨0, 1, c, 1, k, f⟩ [fm]⊢* ⟨0, 1, c + k, 1, 0, f + k⟩ := by
  intro k; induction k with
  | zero => intro c f; exists 0
  | succ k ih =>
    intro c f
    step fm; step fm
    apply stepStar_trans (ih (c + 1) (f + 1))
    ring_nf; finish

-- R4 loop: converts c into d and e
theorem r4_loop : ∀ c d e f,
    ⟨0, 0, c, d, e, f⟩ [fm]⊢* ⟨0, 0, 0, d + c, e + 2 * c, f⟩ := by
  intro c; induction c with
  | zero => intro d e f; exists 0
  | succ c ih =>
    intro d e f
    step fm
    apply stepStar_trans (ih (d + 1) (e + 2) f)
    ring_nf; finish

-- R4+R2: transition after the R3R1 loop
theorem r4_r2 : ⟨0, 1, c + 1, 1, 0, f⟩ [fm]⊢* ⟨0, 0, c, 0, 2, f⟩ := by
  step fm; step fm; finish

-- Drain: converts (0,0,0,2k+1,E,2k+2) to (0,1,0,1,E,0) via repeated R5+R2
theorem drain : ∀ k E,
    ⟨0, 0, 0, 2 * k + 1, E, 2 * (k + 1)⟩ [fm]⊢⁺ ⟨0, 1, 0, 1, E, 0⟩ := by
  intro k; induction k with
  | zero => intro E; step fm; finish
  | succ k ih =>
    intro E
    rw [show 2 * (k + 1) + 1 = (2 * k + 1) + 2 from by ring,
        show 2 * (k + 1 + 1) = 2 * (k + 1) + 2 from by ring]
    step fm; step fm
    exact stepPlus_stepStar (ih E)

-- Main cycle: (0,1,0,1,2*(e+1),0) →⁺ (0,1,0,1,4*(e+1),0)
theorem main_cycle (e : ℕ) :
    ⟨0, 1, 0, 1, 2 * (e + 1), 0⟩ [fm]⊢⁺ ⟨0, 1, 0, 1, 4 * (e + 1), 0⟩ := by
  -- Phase 1: R3/R1 loop
  apply stepStar_stepPlus_stepPlus (r3r1_loop (2 * (e + 1)) 0 0)
  simp only [Nat.zero_add]
  -- Phase 2: R4+R2
  rw [show 2 * (e + 1) = (2 * e + 1) + 1 from by ring]
  apply stepStar_stepPlus_stepPlus r4_r2
  -- Phase 3: R4 loop
  apply stepStar_stepPlus_stepPlus (r4_loop (2 * e + 1) 0 2 (2 * (e + 1)))
  simp only [Nat.zero_add]
  rw [show 2 + 2 * (2 * e + 1) = 4 * (e + 1) from by ring]
  -- Phase 4: Drain
  exact drain e (4 * (e + 1))

theorem nonhalt : ¬halts fm c₀ := by
  -- First reach the anchor state (0,1,0,1,2,0) in 2 steps
  apply stepStar_not_halts_not_halts (c₂ := ⟨0, 1, 0, 1, 2, 0⟩)
  · execute fm 2
  -- Use progress_nonhalt with invariant: state is (0,1,0,1,2*(e+1),0) for some e
  apply progress_nonhalt (fm := fm)
    (P := fun q ↦ ∃ e, q = ⟨0, 1, 0, 1, 2 * (e + 1), 0⟩)
  · intro c ⟨e, hq⟩; subst hq
    exact ⟨⟨0, 1, 0, 1, 4 * (e + 1), 0⟩,
           ⟨2 * e + 1, by ring_nf⟩,
           main_cycle e⟩
  · exact ⟨0, by ring_nf⟩

end Sz22_2003_unofficial_296
