import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz21_140_unofficial #121: [77/15, 9/14, 44/3, 5/11, 3/2]

Vector representation:
```
 0 -1 -1  1  1
-1  2  0 -1  0
 2 -1  0  0  1
 0  0  1  0 -1
-1  1  0  0  0
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz21_140_unofficial_121

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a, b+1, c+1, d, e⟩ => some ⟨a, b, c, d+1, e+1⟩
  | ⟨a+1, b, c, d+1, e⟩ => some ⟨a, b+2, c, d, e⟩
  | ⟨a, b+1, c, d, e⟩ => some ⟨a+2, b, c, d, e+1⟩
  | ⟨a, b, c, d, e+1⟩ => some ⟨a, b, c+1, d, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b+1, c, d, e⟩
  | _ => none

-- R4 repeated: e → c
theorem e_to_c : ∀ k, ∀ a c e, ⟨a, 0, c, 0, e+k⟩ [fm]⊢* ⟨a, 0, c+k, 0, e⟩ := by
  intro k; induction' k with k h <;> intro a c e
  · exists 0
  rw [← Nat.add_assoc]
  step fm
  apply stepStar_trans (h _ _ _)
  ring_nf; finish

-- R3 repeated: b → a+2, e+1
theorem r3_chain : ∀ k, ∀ a b e, ⟨a, b+k, 0, 0, e⟩ [fm]⊢* ⟨a+2*k, b, 0, 0, e+k⟩ := by
  intro k; induction' k with k h <;> intro a b e
  · exists 0
  rw [← Nat.add_assoc]
  step fm
  apply stepStar_trans (h _ _ _)
  ring_nf; finish

-- R1R1R2 chain: k rounds of (R1, R1, R2), consuming 2 from c and 1 from a per round
theorem r1r1r2_chain : ∀ k, ∀ a c d f, ⟨a+k, 2, c+2*k, d, f⟩ [fm]⊢* ⟨a, 2, c, d+k, f+2*k⟩ := by
  intro k; induction' k with k h <;> intro a c d f
  · exists 0
  rw [show a + (k + 1) = (a + k) + 1 from by ring,
      show c + 2 * (k + 1) = (c + 2 * k) + 2 from by ring]
  step fm  -- R1
  step fm  -- R1
  step fm  -- R2
  apply stepStar_trans (h _ _ _ _)
  ring_nf; finish

-- R2 drain: (a, b, 0, a, f) →* (0, b+2*a, 0, 0, f) when c=0
theorem r2_drain : ∀ a, ∀ b f, ⟨a, b, 0, a, f⟩ [fm]⊢* ⟨0, b+2*a, 0, 0, f⟩ := by
  intro a; induction' a with a h <;> intro b f
  · exists 0
  step fm  -- R2
  apply stepStar_trans (h _ _)
  ring_nf; finish

-- Middle even subchain: (2m, 2, 2m, 0, 1) →* (0, 2m+2, 0, 0, 2m+1)
theorem middle_even (m : ℕ) : ⟨2*m, 2, 2*m, 0, 1⟩ [fm]⊢* ⟨0, 2*m+2, 0, 0, 2*m+1⟩ := by
  apply stepStar_trans (c₂ := ⟨m, 2, 0, m, 1+2*m⟩)
  · have := r1r1r2_chain m m 0 0 1
    simp only [Nat.zero_add] at this
    rw [show m + m = 2 * m from by ring] at this
    refine stepStar_trans this ?_
    ring_nf; finish
  have := r2_drain m 2 (1+2*m)
  refine stepStar_trans this ?_
  ring_nf; finish

-- Middle odd subchain: (2m+1, 2, 2m+1, 0, 1) →* (0, 2m+3, 0, 0, 2m+2)
theorem middle_odd (m : ℕ) : ⟨2*m+1, 2, 2*m+1, 0, 1⟩ [fm]⊢* ⟨0, 2*m+3, 0, 0, 2*m+2⟩ := by
  apply stepStar_trans (c₂ := ⟨m+1, 2, 1, m, 1+2*m⟩)
  · have := r1r1r2_chain m (m+1) 1 0 1
    simp only [Nat.zero_add] at this
    rw [show m + 1 + m = 2 * m + 1 from by ring,
        show 1 + 2 * m = 2 * m + 1 from by ring] at this
    refine stepStar_trans this ?_
    ring_nf; finish
  -- R1: (m+1, 2, 1, m, 1+2m) → (m+1, 1, 0, m+1, 2+2m)
  apply stepStar_trans (c₂ := ⟨m+1, 1, 0, m+1, 2+2*m⟩)
  · step fm; ring_nf; finish
  -- R2 drain
  have := r2_drain (m+1) 1 (2+2*m)
  refine stepStar_trans this ?_
  ring_nf; finish

-- Combined middle + R3: (e+2, 0, e+1, 0, 0) ⊢⁺ (2e+4, 0, 0, 0, 2e+3)
theorem middle_r3 : ⟨e+2, 0, e+1, 0, 0⟩ [fm]⊢⁺ ⟨2*e+4, 0, 0, 0, 2*e+3⟩ := by
  -- R5: (e+2, 0, e+1, 0, 0) → (e+1, 1, e+1, 0, 0)
  apply step_stepStar_stepPlus (c₂ := ⟨e+1, 1, e+1, 0, 0⟩)
  · show fm ⟨(e+1)+1, 0, e+1, 0, 0⟩ = some ⟨e+1, 0+1, e+1, 0, 0⟩; simp [fm]
  -- R1: → (e+1, 0, e, 1, 1)
  apply stepStar_trans (c₂ := ⟨e+1, 0, e, 1, 1⟩)
  · step fm; finish
  -- R2: → (e, 2, e, 0, 1)
  apply stepStar_trans (c₂ := ⟨e, 2, e, 0, 1⟩)
  · step fm; finish
  -- Even/odd subchain then R3 chain
  rcases Nat.even_or_odd e with ⟨m, hm⟩ | ⟨m, hm⟩
  · rw [show m + m = 2 * m from by ring] at hm; subst hm
    apply stepStar_trans (middle_even m)
    have := r3_chain (2*m+2) 0 0 (2*m+1)
    simp only [Nat.zero_add] at this
    refine stepStar_trans this ?_
    ring_nf; finish
  · subst hm
    apply stepStar_trans (middle_odd m)
    have := r3_chain (2*m+3) 0 0 (2*m+2)
    simp only [Nat.zero_add] at this
    refine stepStar_trans this ?_
    ring_nf; finish

-- Main transition: (e+1, 0, 0, 0, e) ⊢⁺ (2e+2, 0, 0, 0, 2e+1)
theorem main_trans : ⟨e+1, 0, 0, 0, e⟩ [fm]⊢⁺ ⟨2*e+2, 0, 0, 0, 2*e+1⟩ := by
  rcases e with _ | e
  · -- e = 0: (1, 0, 0, 0, 0) → (0, 1, 0, 0, 0) → (2, 0, 0, 0, 1)
    step fm; step fm; finish
  · -- e ≥ 1: Phase 1 (R4 chain) then middle_r3
    have h1 : ⟨e+2, 0, 0, 0, e+1⟩ [fm]⊢* ⟨e+2, 0, e+1, 0, 0⟩ := by
      have := e_to_c (e+1) (e+2) 0 0
      simp only [Nat.zero_add] at this; exact this
    apply stepStar_stepPlus_stepPlus h1
    exact middle_r3

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨1, 0, 0, 0, 0⟩) (by exists 0)
  apply progress_nonhalt_simple (fm := fm) (A := ℕ) (fun e ↦ ⟨e+1, 0, 0, 0, e⟩) 0
  intro e; exact ⟨2*e+1, main_trans⟩
