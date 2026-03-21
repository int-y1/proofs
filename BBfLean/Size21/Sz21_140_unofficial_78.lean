import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz21_140_unofficial #78: [5/6, 4/35, 539/2, 3/7, 14/11]

Vector representation:
```
-1 -1  1  0  0
 2  0 -1 -1  0
-1  0  0  2  1
 0  1  0 -1  0
 1  0  0  1 -1
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz21_140_unofficial_78

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a+1, b+1, c, d, e⟩ => some ⟨a, b, c+1, d, e⟩
  | ⟨a, b, c+1, d+1, e⟩ => some ⟨a+2, b, c, d, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b, c, d+2, e+1⟩
  | ⟨a, b, c, d+1, e⟩ => some ⟨a, b+1, c, d, e⟩
  | ⟨a, b, c, d, e+1⟩ => some ⟨a+1, b, c, d+1, e⟩
  | _ => none

-- R4 repeated: d → b
theorem d_to_b : ∀ k, ∀ b d, ⟨0, b, 0, d+k, e⟩ [fm]⊢* ⟨0, b+k, 0, d, e⟩ := by
  intro k; induction k with
  | zero => intro b d; exists 0
  | succ k ih =>
    intro b d
    rw [show d + (k + 1) = (d + k) + 1 from by ring]
    step fm
    apply stepStar_trans (ih _ _)
    ring_nf; finish

-- 5-step round: consumes 3 from b, 1 from e, adds 2 to c
theorem five_step_round : ⟨0, b+3, c, 0, e+1⟩ [fm]⊢* ⟨0, b, c+2, 0, e⟩ := by
  step fm
  rw [show b + 3 = (b + 2) + 1 from by ring]
  step fm
  step fm
  rw [show b + 2 = (b + 1) + 1 from by ring]
  step fm
  rw [show b + 1 = b + 1 from rfl]
  step fm
  finish

-- 5-step round iterated j times
theorem phase2_rounds : ∀ j, ∀ b c e, ⟨0, b+3*j, c, 0, e+j⟩ [fm]⊢* ⟨0, b, c+2*j, 0, e⟩ := by
  intro j; induction j with
  | zero => intro b c e; exists 0
  | succ j ih =>
    intro b c e
    rw [show b + 3 * (j + 1) = (b + 3 * j) + 3 from by ring,
        show e + (j + 1) = (e + j) + 1 from by ring]
    rw [show (b + 3 * j) + 3 = (b + 3 * j) + 3 from rfl]
    apply stepStar_trans five_step_round
    apply stepStar_trans (ih b (c + 2) e)
    ring_nf; finish

-- Phase 3: consume 2 from b, add 1 to c
theorem phase3 : ⟨0, 2, c, 0, e+1⟩ [fm]⊢* ⟨0, 0, c+1, 2, e+1⟩ := by
  step fm
  step fm
  step fm
  step fm
  step fm
  finish

-- R2R2R3 round: consumes 2 from c, adds 3 to a, adds 1 to e
theorem r2r2r3_round : ⟨a, 0, c+2, 2, e⟩ [fm]⊢* ⟨a+3, 0, c, 2, e+1⟩ := by
  rw [show c + 2 = (c + 1) + 1 from by ring]
  step fm
  step fm
  rw [show a + 4 = (a + 3) + 1 from by ring]
  step fm
  finish

-- R2R2R3 round iterated j times
theorem phase4_rounds : ∀ j, ∀ a c e, ⟨a, 0, c+2*j, 2, e⟩ [fm]⊢* ⟨a+3*j, 0, c, 2, e+j⟩ := by
  intro j; induction j with
  | zero => intro a c e; exists 0
  | succ j ih =>
    intro a c e
    rw [show c + 2 * (j + 1) = (c + 2 * j) + 2 from by ring,
        show a + 3 * (j + 1) = (a + 3 * j) + 3 from by ring,
        show e + (j + 1) = (e + j) + 1 from by ring]
    apply stepStar_trans (r2r2r3_round (a := a) (c := c + 2 * j) (e := e))
    rw [show a + 3 = a + 3 from rfl]
    apply stepStar_trans (ih (a + 3) c (e + 1))
    ring_nf; finish

-- Phase 4b: final R2 when c=1
theorem phase4_final : ⟨a, 0, 1, 2, e⟩ [fm]⊢* ⟨a+2, 0, 0, 1, e⟩ := by
  step fm
  finish

-- R3 repeated: a → d,e
theorem a_to_de : ∀ k, ∀ a d e, ⟨a+k, 0, 0, d, e⟩ [fm]⊢* ⟨a, 0, 0, d+2*k, e+k⟩ := by
  intro k; induction k with
  | zero => intro a d e; exists 0
  | succ k ih =>
    intro a d e
    rw [show a + (k + 1) = (a + k) + 1 from by ring]
    step fm
    apply stepStar_trans (ih a _ _)
    ring_nf; finish

-- Main transition
theorem main_trans (j e : ℕ) (he : e ≥ j + 1) :
    ⟨0, 0, 0, 3*j+2, e⟩ [fm]⊢⁺ ⟨0, 0, 0, 6*j+5, e+3*j+2⟩ := by
  -- Phase 1: R4 × (3j+2): d → b
  apply stepStar_stepPlus_stepPlus (c₂ := ⟨0, 3*j+2, 0, 0, e⟩)
  · have h := d_to_b (3*j+2) 0 0 (e := e)
    simp only [Nat.zero_add] at h; exact h
  -- Phase 2: j 5-step rounds
  apply stepStar_stepPlus_stepPlus (c₂ := ⟨0, 2, 2*j, 0, e-j⟩)
  · have h := phase2_rounds j 2 0 (e - j)
    rw [show 2 + 3 * j = 3 * j + 2 from by ring,
        show 0 + 2 * j = 2 * j from by ring,
        show (e - j) + j = e from by omega] at h
    exact h
  -- Phase 3: 5 steps
  apply stepStar_stepPlus_stepPlus (c₂ := ⟨0, 0, 2*j+1, 2, e-j⟩)
  · have hej : e - j ≥ 1 := by omega
    obtain ⟨e', he'⟩ : ∃ e', e - j = e' + 1 := ⟨e - j - 1, by omega⟩
    rw [he']
    apply stepStar_trans (phase3 (c := 2*j) (e := e'))
    rw [show e' + 1 = e - j from by omega]
    finish
  -- Phase 4: R2R2R3 rounds + final R2
  apply stepStar_stepPlus_stepPlus (c₂ := ⟨3*j+2, 0, 0, 1, e⟩)
  · apply stepStar_trans (c₂ := ⟨3*j, 0, 1, 2, e-j+j⟩)
    · have h := phase4_rounds j 0 1 (e - j)
      rw [show 1 + 2 * j = 2 * j + 1 from by ring,
          show 0 + 3 * j = 3 * j from by ring] at h
      exact h
    rw [show e - j + j = e from by omega]
    exact phase4_final
  -- Phase 5: R3 × (3j+2): a → d,e
  apply step_stepStar_stepPlus (c₂ := ⟨3*j+1, 0, 0, 3, e+1⟩)
  · show fm ⟨(3*j+1)+1, 0, 0, 1, e⟩ = some ⟨3*j+1, 0, 0, 3, e+1⟩
    simp [fm]
  have h := a_to_de (3*j+1) 0 3 (e+1)
  simp only [Nat.zero_add] at h
  apply stepStar_trans h
  ring_nf; finish

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨0, 0, 0, 2, 1⟩) (by execute fm 1)
  apply progress_nonhalt (fm := fm)
    (P := fun q ↦ ∃ j e, q = ⟨0, 0, 0, 3*j+2, e⟩ ∧ e ≥ j + 1)
  · intro c ⟨j, e, hq, he⟩; subst hq
    refine ⟨_, ⟨2*j+1, e+3*j+2, ?_, by omega⟩, main_trans j e he⟩
    ring_nf
  · exact ⟨0, 1, rfl, by omega⟩
