import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #877: [4/15, 1/42, 33/2, 7/3, 5/11, 2/7]

Vector representation:
```
 2 -1 -1  0  0
-1 -1  0 -1  0
-1  1  0  0  1
 0 -1  0  1  0
 0  0  1  0 -1
 1  0  0 -1  0
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_877

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a, b+1, c+1, d, e⟩ => some ⟨a+2, b, c, d, e⟩
  | ⟨a+1, b+1, c, d+1, e⟩ => some ⟨a, b, c, d, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b+1, c, d, e+1⟩
  | ⟨a, b+1, c, d, e⟩ => some ⟨a, b, c, d+1, e⟩
  | ⟨a, b, c, d, e+1⟩ => some ⟨a, b, c+1, d, e⟩
  | ⟨a, b, c, d+1, e⟩ => some ⟨a+1, b, c, d, e⟩
  | _ => none

theorem r3_chain : ∀ k, ∀ a b e, ⟨a + k, b, 0, 0, e⟩ [fm]⊢* ⟨a, b + k, 0, 0, e + k⟩ := by
  intro k; induction' k with k ih <;> intro a b e
  · exists 0
  · rw [show a + (k + 1) = (a + k) + 1 from by ring]
    step fm
    apply stepStar_trans (ih a (b + 1) (e + 1))
    ring_nf; finish

theorem r4_chain : ∀ k, ∀ b d e, ⟨0, b + k, 0, d, e⟩ [fm]⊢* ⟨0, b, 0, d + k, e⟩ := by
  intro k; induction' k with k ih <;> intro b d e
  · exists 0
  · rw [show b + (k + 1) = (b + k) + 1 from by ring]
    step fm
    apply stepStar_trans (ih b (d + 1) e)
    ring_nf; finish

theorem r5_chain : ∀ k, ∀ c d e, ⟨0, 0, c, d, e + k⟩ [fm]⊢* ⟨0, 0, c + k, d, e⟩ := by
  intro k; induction' k with k ih <;> intro c d e
  · exists 0
  · rw [show e + (k + 1) = (e + k) + 1 from by ring]
    step fm
    apply stepStar_trans (ih (c + 1) d e)
    ring_nf; finish

theorem r3r1_chain : ∀ C, ∀ a D E, ⟨a + 1, 0, C, D, E⟩ [fm]⊢* ⟨a + C + 1, 0, 0, D, E + C⟩ := by
  intro C; induction' C with C ih <;> intro a D E
  · exists 0
  · step fm
    step fm
    rw [show a + 2 = (a + 1) + 1 from by ring]
    apply stepStar_trans (ih (a + 1) D (E + 1))
    ring_nf; finish

theorem r3r2_drain : ∀ k, ∀ A E, ⟨2 * k + A, 0, 0, k, E⟩ [fm]⊢* ⟨A, 0, 0, 0, E + k⟩ := by
  intro k; induction' k with k ih <;> intro A E
  · simp; exists 0
  · rw [show 2 * (k + 1) + A = (2 * k + A) + 1 + 1 from by ring]
    step fm
    step fm
    apply stepStar_trans (ih A (E + 1))
    ring_nf; finish

theorem main_trans (A E : ℕ) :
    ⟨A + 1, 0, 0, 0, A + E + 1⟩ [fm]⊢⁺ ⟨E + 3, 0, 0, 0, 3 * A + E + 2⟩ := by
  -- Phase 1: R3 chain (A+1 steps)
  have h1 : ⟨A + 1, 0, 0, 0, A + E + 1⟩ [fm]⊢* ⟨0, A + 1, 0, 0, 2 * A + E + 2⟩ := by
    have := r3_chain (A + 1) 0 0 (A + E + 1)
    rw [show 0 + (A + 1) = A + 1 from by ring,
        show A + E + 1 + (A + 1) = 2 * A + E + 2 from by ring] at this
    exact this
  -- Phase 2: R4 chain (A+1 steps)
  have h2 : ⟨0, A + 1, 0, 0, 2 * A + E + 2⟩ [fm]⊢* ⟨0, 0, 0, A + 1, 2 * A + E + 2⟩ := by
    have := r4_chain (A + 1) 0 0 (2 * A + E + 2)
    rw [show 0 + (A + 1) = A + 1 from by ring] at this
    exact this
  -- Phase 3: R5 chain
  have h3 : ⟨0, 0, 0, A + 1, 2 * A + E + 2⟩ [fm]⊢* ⟨0, 0, 2 * A + E + 2, A + 1, 0⟩ := by
    have := r5_chain (2 * A + E + 2) 0 (A + 1) 0
    rw [show 0 + (2 * A + E + 2) = 2 * A + E + 2 from by ring] at this
    exact this
  -- Phase 4-6: R6, R3, R1 (3 steps)
  have h456 : ⟨0, 0, 2 * A + E + 2, A + 1, 0⟩ [fm]⊢⁺ ⟨2, 0, 2 * A + E + 1, A, 1⟩ := by
    rw [show 2 * A + E + 2 = (2 * A + E + 1) + 1 from by ring,
        show A + 1 = (A : ℕ) + 1 from rfl]
    step fm  -- R6: (1, 0, (2A+E+1)+1, A, 0)
    rw [show (2 * A + E + 1) + 1 = (2 * A + E) + 1 + 1 from by ring]
    step fm  -- R3: (0, 1, (2A+E)+1+1, A, 1)
    step fm  -- R1: (2, 0, 2A+E+1, A, 1)
    rw [show 2 * A + E + 1 = 2 * A + E + 1 from rfl]
    finish
  -- Phase 7: R3/R1 chain (2*A+E+1 rounds)
  have h7 : ⟨2, 0, 2 * A + E + 1, A, 1⟩ [fm]⊢* ⟨2 * A + E + 3, 0, 0, A, 2 * A + E + 2⟩ := by
    rw [show (2 : ℕ) = 1 + 1 from by ring]
    have := r3r1_chain (2 * A + E + 1) 1 A 1
    rw [show 1 + (2 * A + E + 1) + 1 = 2 * A + E + 3 from by ring,
        show 1 + (2 * A + E + 1) = 2 * A + E + 2 from by ring] at this
    exact this
  -- Phase 8: R3/R2 drain (A rounds)
  have h8 : ⟨2 * A + E + 3, 0, 0, A, 2 * A + E + 2⟩ [fm]⊢* ⟨E + 3, 0, 0, 0, 3 * A + E + 2⟩ := by
    rw [show 2 * A + E + 3 = 2 * A + (E + 3) from by ring]
    have := r3r2_drain A (E + 3) (2 * A + E + 2)
    rw [show 2 * A + E + 2 + A = 3 * A + E + 2 from by ring] at this
    exact this
  exact stepStar_stepPlus_stepPlus h1
    (stepStar_stepPlus_stepPlus h2
      (stepStar_stepPlus_stepPlus h3
        (stepPlus_stepStar_stepPlus h456
          (stepStar_trans h7 h8))))

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨2, 0, 0, 0, 4⟩) (by execute fm 22)
  apply progress_nonhalt (fm := fm)
    (P := fun q ↦ ∃ A E, q = ⟨A + 1, 0, 0, 0, A + E + 1⟩ ∧ A ≥ 1)
  · intro c ⟨A, E, hq, hA⟩; subst hq
    obtain ⟨A', rfl⟩ : ∃ A', A = A' + 1 := ⟨A - 1, by omega⟩
    refine ⟨⟨E + 3, 0, 0, 0, 3 * (A' + 1) + E + 2⟩,
           ⟨E + 2, 3 * A' + 2, by ring_nf, by omega⟩,
           main_trans (A' + 1) E⟩
  · exact ⟨1, 2, rfl, by omega⟩

end Sz22_2003_unofficial_877
