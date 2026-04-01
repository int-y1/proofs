import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #1323: [63/10, 1573/2, 2/33, 5/7, 21/13]

Vector representation:
```
-1  2 -1  1  0  0
-1  0  0  0  2  1
 1 -1  0  0 -1  0
 0  0  1 -1  0  0
 0  1  0  1  0 -1
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_1323

def Q := ℕ × ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a+1, b, c+1, d, e, f⟩ => some ⟨a, b+2, c, d+1, e, f⟩
  | ⟨a+1, b, c, d, e, f⟩ => some ⟨a, b, c, d, e+2, f+1⟩
  | ⟨a, b+1, c, d, e+1, f⟩ => some ⟨a+1, b, c, d, e, f⟩
  | ⟨a, b, c, d+1, e, f⟩ => some ⟨a, b, c+1, d, e, f⟩
  | ⟨a, b, c, d, e, f+1⟩ => some ⟨a, b+1, c, d+1, e, f⟩
  | _ => none

-- R4 repeated: move d to c
theorem d_to_c : ∀ k c d e f, ⟨(0 : ℕ), (0 : ℕ), c, d + k, e, f⟩ [fm]⊢*
    ⟨(0 : ℕ), (0 : ℕ), c + k, d, e, f⟩ := by
  intro k; induction' k with k ih
  · intro c d e f; exists 0
  · intro c d e f
    rw [show d + (k + 1) = (d + k) + 1 from by ring]
    step fm
    apply stepStar_trans (ih (c + 1) d e f)
    ring_nf; finish

-- R3+R1 chain: k rounds, each round is R3 then R1
theorem r3r1_chain : ∀ k b c d e f, ⟨(0 : ℕ), b + 1, c + k, d, e + k, f⟩ [fm]⊢*
    ⟨(0 : ℕ), b + k + 1, c, d + k, e, f⟩ := by
  intro k; induction' k with k ih
  · intro b c d e f; exists 0
  · intro b c d e f
    rw [show c + (k + 1) = (c + k) + 1 from by ring,
        show e + (k + 1) = (e + k) + 1 from by ring,
        show b + 1 = b + 1 from rfl]
    step fm; step fm
    rw [show b + 2 = (b + 1) + 1 from by ring,
        show c + k = c + k from rfl]
    apply stepStar_trans (ih (b + 1) c (d + 1) e f)
    rw [show b + 1 + k + 1 = b + (k + 1) + 1 from by ring,
        show d + 1 + k = d + (k + 1) from by ring]
    finish

-- R3+R2 chain: k rounds draining b while increasing e and f
theorem r3r2_chain : ∀ k b d e f, ⟨(0 : ℕ), b + k, (0 : ℕ), d, e + 1, f⟩ [fm]⊢*
    ⟨(0 : ℕ), b, (0 : ℕ), d, e + k + 1, f + k⟩ := by
  intro k; induction' k with k ih
  · intro b d e f; exists 0
  · intro b d e f
    rw [show b + (k + 1) = (b + k) + 1 from by ring,
        show e + 1 = e + 1 from rfl]
    step fm; step fm
    rw [show e + 2 = (e + 1) + 1 from by ring]
    apply stepStar_trans (ih b d (e + 1) (f + 1))
    rw [show e + 1 + k + 1 = e + (k + 1) + 1 from by ring,
        show f + 1 + k = f + (k + 1) from by ring]
    finish

-- Combine phases into the main transition
theorem main_transition (n f : ℕ) :
    ⟨(0 : ℕ), (0 : ℕ), 0, n, n + 2, f + 1⟩ [fm]⊢⁺
    ⟨(0 : ℕ), (0 : ℕ), 0, n + 1, n + 3, f + n + 1⟩ := by
  -- Phase 1: d_to_c (n steps of R4)
  have phase1 := d_to_c n 0 0 (n + 2) (f + 1)
  rw [show (0 : ℕ) + n = n from by ring] at phase1
  -- Phase 2: R5 step
  have phase2 : (⟨0, 0, n, 0, n + 2, f + 1⟩ : Q) [fm]⊢ ⟨0, 1, n, 1, n + 2, f⟩ := by
    simp [fm]
  -- Phase 3: R3+R1 chain (n rounds)
  have phase3 := r3r1_chain n 0 0 1 2 f
  simp only [Nat.zero_add, Nat.add_comm 2 n, Nat.add_comm 1 n] at phase3
  -- Phase 4: R3+R2 chain (n+1 rounds)
  have phase4 := r3r2_chain (n + 1) 0 (n + 1) 1 f
  rw [show 0 + (n + 1) = n + 1 from by ring,
      show (1 : ℕ) + 1 = 2 from by ring,
      show 1 + (n + 1) + 1 = n + 3 from by ring,
      show f + (n + 1) = f + n + 1 from by ring] at phase4
  -- Compose all phases
  exact stepStar_stepPlus_stepPlus phase1
    (step_stepStar_stepPlus phase2
      (stepStar_trans phase3 phase4))

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨0, 0, 0, 0, 2, 1⟩) (by execute fm 1)
  apply progress_nonhalt (fm := fm)
    (P := fun q ↦ ∃ n f, q = ⟨0, 0, 0, n, n + 2, f⟩ ∧ f ≥ 1)
  · intro c ⟨n, f, hq, hf⟩; subst hq
    obtain ⟨F, rfl⟩ : ∃ F, f = F + 1 := ⟨f - 1, by omega⟩
    refine ⟨⟨0, 0, 0, n + 1, n + 3, F + n + 1⟩,
      ⟨n + 1, F + n + 1, rfl, ?_⟩,
      main_transition n F⟩
    · omega
  · exact ⟨0, 1, rfl, by omega⟩

end Sz22_2003_unofficial_1323
