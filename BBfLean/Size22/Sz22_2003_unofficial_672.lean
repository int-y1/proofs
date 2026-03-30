import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #672: [35/6, 28/55, 1573/2, 3/7, 5/13]

Vector representation:
```
-1 -1  1  1  0  0
 2  0 -1  1 -1  0
-1  0  0  0  2  1
 0  1  0 -1  0  0
 0  0  1  0  0 -1
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_672

def Q := ℕ × ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a+1, b+1, c, d, e, f⟩ => some ⟨a, b, c+1, d+1, e, f⟩
  | ⟨a, b, c+1, d, e+1, f⟩ => some ⟨a+2, b, c, d+1, e, f⟩
  | ⟨a+1, b, c, d, e, f⟩ => some ⟨a, b, c, d, e+2, f+1⟩
  | ⟨a, b, c, d+1, e, f⟩ => some ⟨a, b+1, c, d, e, f⟩
  | ⟨a, b, c, d, e, f+1⟩ => some ⟨a, b, c+1, d, e, f⟩
  | _ => none

-- R4 repeated: move d to b.
theorem r4_chain : ∀ k, ⟨0, b, 0, d + k, e, f⟩ [fm]⊢* ⟨0, b + k, 0, d, e, f⟩ := by
  intro k; induction' k with k ih generalizing b d
  · exists 0
  · rw [show d + (k + 1) = (d + k) + 1 from by ring]; step fm
    apply stepStar_trans (ih (b := b + 1)); ring_nf; finish

-- R3 repeated: drain a.
theorem r3_chain : ∀ k, ⟨a + k, 0, 0, d, e, f⟩ [fm]⊢* ⟨a, 0, 0, d, e + 2 * k, f + k⟩ := by
  intro k; induction' k with k ih generalizing a e f
  · exists 0
  · rw [show a + (k + 1) = (a + k) + 1 from by ring]; step fm
    apply stepStar_trans (ih (a := a) (e := e + 2) (f := f + 1)); ring_nf; finish

-- R2 chain with b=0: drain c while building a.
theorem r2_chain : ∀ k c D, ⟨a, 0, c + k, D, E + k, f⟩ [fm]⊢* ⟨a + 2 * k, 0, c, D + k, E, f⟩ := by
  intro k; induction' k with k ih generalizing a E
  · intro c D; exists 0
  · intro c D
    rw [show c + (k + 1) = (c + k) + 1 from by ring,
        show E + (k + 1) = (E + k) + 1 from by ring]; step fm
    apply stepStar_trans (ih (a := a + 2) (E := E) c (D + 1)); ring_nf; finish

-- Interleaving: (0, b, c+1, D, E+b+c+1, f) →* (b+2*c+2, 0, 0, D+2*b+c+1, E, f)
theorem interleave : ∀ b c D,
    ⟨0, b, c + 1, D, E + b + c + 1, f⟩ [fm]⊢* ⟨b + 2 * c + 2, 0, 0, D + 2 * b + c + 1, E, f⟩ := by
  intro b; induction' b using Nat.strongRecOn with b ih
  intro c D; rcases b with _ | _ | b
  · -- b = 0: R2 chain of length c+1
    rw [show E + 0 + c + 1 = E + (c + 1) from by ring]
    have := r2_chain (c + 1) 0 D (a := 0) (E := E) (f := f)
    simp only [Nat.zero_add] at this
    apply stepStar_trans this; ring_nf; finish
  · -- b = 1: R2, R1, then R2 chain of length c+1
    rw [show E + 1 + c + 1 = (E + (c + 1)) + 1 from by ring]
    step fm; step fm
    have := r2_chain (c + 1) 0 (D + 1 + 1) (a := 1) (E := E) (f := f)
    simp only [Nat.zero_add] at this
    apply stepStar_trans this; ring_nf; finish
  · -- b + 2: 3-step round (R2, R1, R1) then IH
    rw [show E + (b + 2) + c + 1 = (E + b + c + 2) + 1 from by ring]
    step fm; step fm; step fm
    rw [show E + b + c + 2 = E + b + (c + 1) + 1 from by ring]
    apply stepStar_trans (ih b (by omega) (c + 1) (D + 1 + 1 + 1))
    ring_nf; finish

-- All phases combined as ⊢*
theorem all_phases :
    ⟨0, 0, 0, d, d + 1 + m, d + 1⟩ [fm]⊢* ⟨0, 0, 0, 2 * d + 1, 2 * d + 2 + (m + 2), 2 * d + 2⟩ := by
  -- Phase 1: R4 x d
  have h1 := r4_chain d (b := 0) (d := 0) (e := d + 1 + m) (f := d + 1)
  simp only [Nat.zero_add] at h1
  apply stepStar_trans h1
  -- Phase 2: R5 x 1: step (0, d, 0, 0, d+1+m, d+1) -> (0, d, 1, 0, d+1+m, d)
  have h2 : (0, d, 0, 0, d + 1 + m, d + 1) [fm]⊢* (0, d, 1, 0, d + 1 + m, d) := by
    apply step_stepStar; unfold fm; simp
  apply stepStar_trans h2
  -- Phase 3: Interleave
  rw [show d + 1 + m = m + d + 1 from by ring]
  have h3 := interleave d 0 0 (E := m) (f := d)
  simp only [Nat.zero_add, Nat.add_zero] at h3
  apply stepStar_trans h3
  -- Phase 4: R3 x (d+2)
  have h4 := r3_chain (d + 2) (a := 0) (d := 2 * d + 1) (e := m) (f := d)
  simp only [Nat.zero_add] at h4
  apply stepStar_trans h4
  ring_nf; finish

-- Main transition as ⊢⁺
theorem main_trans :
    ⟨0, 0, 0, d, d + 1 + m, d + 1⟩ [fm]⊢⁺ ⟨0, 0, 0, 2 * d + 1, 2 * d + 2 + (m + 2), 2 * d + 2⟩ := by
  apply stepStar_stepPlus (all_phases)
  simp [Q]; omega

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨0, 0, 0, 0, 2, 1⟩) (by execute fm 1)
  apply progress_nonhalt_simple (fm := fm) (A := ℕ × ℕ)
    (fun ⟨d, m⟩ ↦ ⟨0, 0, 0, d, d + 1 + m, d + 1⟩) ⟨0, 1⟩
  intro ⟨d, m⟩; exact ⟨⟨2 * d + 1, m + 2⟩, main_trans⟩

end Sz22_2003_unofficial_672
