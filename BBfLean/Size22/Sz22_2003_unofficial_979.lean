import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #979: [4/15, 33/14, 65/2, 7/11, 165/13]

Vector representation:
```
 2 -1 -1  0  0  0
-1  1  0 -1  1  0
-1  0  1  0  0  1
 0  0  0  1 -1  0
 0  1  1  0  1 -1
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_979

def Q := ℕ × ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a, b+1, c+1, d, e, f⟩ => some ⟨a+2, b, c, d, e, f⟩
  | ⟨a+1, b, c, d+1, e, f⟩ => some ⟨a, b+1, c, d, e+1, f⟩
  | ⟨a+1, b, c, d, e, f⟩ => some ⟨a, b, c+1, d, e, f+1⟩
  | ⟨a, b, c, d, e+1, f⟩ => some ⟨a, b, c, d+1, e, f⟩
  | ⟨a, b, c, d, e, f+1⟩ => some ⟨a, b+1, c+1, d, e+1, f⟩
  | _ => none

theorem r4_drain : ∀ k, ∀ c d f,
    ⟨(0 : ℕ), 0, c, d, k, f⟩ [fm]⊢* ⟨0, 0, c, d + k, 0, f⟩ := by
  intro k; induction k with
  | zero => intro c d f; ring_nf; finish
  | succ k ih =>
    intro c d f
    rw [show (k : ℕ) + 1 = k + 1 from rfl]
    step fm
    apply stepStar_trans (ih c (d + 1) f)
    refine ⟨0, ?_⟩; simp only [stepNat, Nat.repeat]; ring_nf

theorem r3_drain : ∀ k, ∀ c e f,
    ⟨k, (0 : ℕ), c, 0, e, f⟩ [fm]⊢* ⟨0, 0, c + k, 0, e, f + k⟩ := by
  intro k; induction k with
  | zero => intro c e f; ring_nf; finish
  | succ k ih =>
    intro c e f
    rw [show (k : ℕ) + 1 = k + 1 from rfl]
    step fm
    apply stepStar_trans (ih (c + 1) e (f + 1))
    refine ⟨0, ?_⟩; simp only [stepNat, Nat.repeat]; ring_nf

theorem r2r1_chain : ∀ k, ∀ a c d e f,
    ⟨a + 1, (0 : ℕ), c + k, d + k, e, f⟩ [fm]⊢* ⟨a + k + 1, 0, c, d, e + k, f⟩ := by
  intro k; induction k with
  | zero => intro a c d e f; ring_nf; finish
  | succ k ih =>
    intro a c d e f
    rw [show c + (k + 1) = (c + k) + 1 from by ring,
        show d + (k + 1) = (d + k) + 1 from by ring,
        show (k : ℕ) + 1 = k + 1 from rfl]
    step fm; step fm
    apply stepStar_trans (ih (a + 1) c d (e + 1) f)
    refine ⟨0, ?_⟩; simp only [stepNat, Nat.repeat]; ring_nf


theorem main_trans (e f : ℕ) :
    ⟨(0 : ℕ), 0, 2 * e + 1, 0, e, f + 1⟩ [fm]⊢⁺
    ⟨0, 0, 2 * (e + 1) + 1, 0, e + 1, f + e + 2⟩ := by
  rcases e with _ | e
  · -- e = 0
    apply step_stepStar_stepPlus
    · show fm ⟨0, 0, 1, 0, 0, f + 1⟩ = some ⟨0, 1, 2, 0, 1, f⟩
      unfold fm; simp only
    · step fm; step fm; step fm; ring_nf; finish
  · -- e + 1 ≥ 1
    -- Phase 1: R4 drain e+1 to d
    have h1 : ⟨(0 : ℕ), 0, 2 * (e + 1) + 1, 0, e + 1, f + 1⟩ [fm]⊢*
              ⟨0, 0, 2 * (e + 1) + 1, e + 1, 0, f + 1⟩ := by
      have := r4_drain (e + 1) (2 * (e + 1) + 1) 0 (f + 1)
      rw [show 0 + (e + 1) = e + 1 from by ring] at this
      exact this
    -- Phase 2: R5 then R1 (2 steps)
    have h2 : ⟨(0 : ℕ), 0, 2 * (e + 1) + 1, e + 1, 0, f + 1⟩ [fm]⊢⁺
              ⟨2, 0, 2 * (e + 1) + 1, e + 1, 1, f⟩ := by
      rw [show 2 * (e + 1) + 1 = (2 * e + 2) + 1 from by ring]
      apply step_stepStar_stepPlus
      · show fm ⟨0, 0, (2 * e + 2) + 1, e + 1, 0, f + 1⟩ =
          some ⟨0, 1, (2 * e + 2) + 1 + 1, e + 1, 1, f⟩
        unfold fm; simp only
      · apply step_stepStar
        show fm ⟨0, 1, (2 * e + 2) + 1 + 1, e + 1, 1, f⟩ =
          some ⟨2, 0, (2 * e + 2) + 1, e + 1, 1, f⟩
        unfold fm; simp only
    -- Phase 3: R2/R1 chain (e+1 rounds)
    have h3 : ⟨2, (0 : ℕ), 2 * (e + 1) + 1, e + 1, 1, f⟩ [fm]⊢*
              ⟨e + 3, 0, e + 2, 0, e + 2, f⟩ := by
      have := r2r1_chain (e + 1) 1 (e + 2) 0 1 f
      rw [show (e + 2) + (e + 1) = 2 * (e + 1) + 1 from by ring,
          show 0 + (e + 1) = e + 1 from by ring,
          show 1 + 1 = 2 from rfl,
          show 1 + (e + 1) + 1 = e + 3 from by ring,
          show 1 + (e + 1) = e + 2 from by ring] at this
      exact this
    -- Phase 4: R3 drain a to c and f
    have h4 : ⟨e + 3, (0 : ℕ), e + 2, 0, e + 2, f⟩ [fm]⊢*
              ⟨0, 0, 2 * e + 5, 0, e + 2, f + e + 3⟩ := by
      have := r3_drain (e + 3) (e + 2) (e + 2) f
      rw [show (e + 2) + (e + 3) = 2 * e + 5 from by ring,
          show f + (e + 3) = f + e + 3 from by ring] at this
      exact this
    -- Compose
    rw [show 2 * (e + 1 + 1) + 1 = 2 * e + 5 from by ring,
        show e + 1 + 1 = e + 2 from by ring,
        show f + (e + 1) + 2 = f + e + 3 from by ring]
    exact stepStar_stepPlus_stepPlus h1
      (stepPlus_stepStar_stepPlus h2 (stepStar_trans h3 h4))

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨0, 0, 5, 0, 2, 4⟩) (by execute fm 13)
  apply progress_nonhalt_simple (fm := fm) (A := ℕ × ℕ)
    (fun ⟨e, f⟩ ↦ ⟨0, 0, 2 * e + 1, 0, e, f + 1⟩) ⟨2, 3⟩
  intro ⟨e, f⟩
  refine ⟨⟨e + 1, f + e + 1⟩, ?_⟩
  show ⟨(0 : ℕ), 0, 2 * e + 1, 0, e, f + 1⟩ [fm]⊢⁺
    ⟨0, 0, 2 * (e + 1) + 1, 0, e + 1, (f + e + 1) + 1⟩
  rw [show (f + e + 1) + 1 = f + e + 2 from by ring]
  exact main_trans e f
