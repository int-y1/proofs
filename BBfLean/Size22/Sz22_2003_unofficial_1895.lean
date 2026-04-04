import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #1895: [9/35, 55/6, 8/5, 7/11, 55/2]

Vector representation:
```
 0  2 -1 -1  0
-1 -1  1  0  1
 3  0 -1  0  0
 0  0  0  1 -1
-1  0  1  0  1
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_1895

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a, b, c+1, d+1, e⟩ => some ⟨a, b+2, c, d, e⟩
  | ⟨a+1, b+1, c, d, e⟩ => some ⟨a, b, c+1, d, e+1⟩
  | ⟨a, b, c+1, d, e⟩ => some ⟨a+3, b, c, d, e⟩
  | ⟨a, b, c, d, e+1⟩ => some ⟨a, b, c, d+1, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b, c+1, d, e+1⟩
  | _ => none

theorem e_to_d : ∀ k, ⟨a, 0, 0, d, e + k⟩ [fm]⊢* ⟨a, 0, 0, d + k, e⟩ := by
  intro k; induction' k with k ih generalizing a d e
  · exists 0
  · rw [show e + (k + 1) = (e + k) + 1 from by ring]
    step fm
    apply stepStar_trans (ih (a := a) (d := d + 1) (e := e))
    ring_nf; finish

theorem r2r1_chain : ∀ k, ⟨a + k, b + 1, 0, d + k, e⟩ [fm]⊢* ⟨a, b + k + 1, 0, d, e + k⟩ := by
  intro k; induction' k with k ih generalizing a b d e
  · exists 0
  · rw [show a + (k + 1) = (a + k) + 1 from by ring,
        show d + (k + 1) = (d + k) + 1 from by ring]
    step fm
    step fm
    apply stepStar_trans (ih (a := a) (b := b + 1) (d := d) (e := e + 1))
    ring_nf; finish

theorem r3_chain : ∀ k, ⟨a, 0, k, 0, e⟩ [fm]⊢* ⟨a + 3 * k, 0, 0, 0, e⟩ := by
  intro k; induction' k with k ih generalizing a e
  · exists 0
  · step fm
    apply stepStar_trans (ih (a := a + 3) (e := e))
    ring_nf; finish

theorem drain : ∀ B, ∀ A C E, ⟨A + 1, B, C, 0, E⟩ [fm]⊢* ⟨A + 1 + 2 * B + 3 * C, 0, 0, 0, E + B⟩ := by
  intro B; induction' B with B ih <;> intro A C E
  · rw [show A + 1 + 2 * 0 + 3 * C = (A + 1) + 3 * C from by ring]
    exact r3_chain C (a := A + 1) (e := E)
  · step fm
    rcases A with _ | A'
    · step fm
      apply stepStar_trans (ih 2 C (E + 1))
      ring_nf; finish
    · apply stepStar_trans (ih A' (C + 1) (E + 1))
      ring_nf; finish

theorem r5_r1 : ⟨a + 1, 0, 0, d + 1, 0⟩ [fm]⊢⁺ ⟨a, 2, 0, d, 1⟩ := by
  step fm; step fm; finish

theorem main_phase : ⟨F + 2 + e, 2, 0, e, 1⟩ [fm]⊢* ⟨2 * e + F + 6, 0, 0, 0, 2 * e + 3⟩ := by
  have h1 : ⟨(F + 2) + e, (1 : ℕ) + 1, 0, 0 + e, 1⟩ [fm]⊢* ⟨F + 2, 1 + e + 1, 0, 0, 1 + e⟩ :=
    r2r1_chain e (a := F + 2) (b := 1) (d := 0) (e := 1)
  rw [show (F + 2 : ℕ) + e = F + 2 + e from rfl,
      show (1 : ℕ) + 1 = 2 from by ring,
      show (0 : ℕ) + e = e from by ring,
      show 1 + e + 1 = e + 2 from by ring,
      show 1 + e = e + 1 from by ring] at h1
  apply stepStar_trans h1
  apply stepStar_trans (drain (e + 2) (F + 1) 0 (e + 1))
  ring_nf; finish

theorem main_trans : ⟨e + F + 3, 0, 0, 0, e + 1⟩ [fm]⊢⁺ ⟨2 * e + F + 6, 0, 0, 0, 2 * e + 3⟩ := by
  rw [show e + 1 = 0 + (e + 1) from by ring]
  apply stepStar_stepPlus_stepPlus (e_to_d (e + 1) (a := e + F + 3) (d := 0) (e := 0))
  rw [show e + F + 3 = (e + F + 2) + 1 from by ring,
      show (0 : ℕ) + (e + 1) = e + 1 from by ring]
  apply stepPlus_stepStar_stepPlus (r5_r1 (a := e + F + 2) (d := e))
  rw [show e + F + 2 = F + 2 + e from by ring]
  exact main_phase

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨3, 0, 0, 0, 1⟩) (by execute fm 2)
  apply progress_nonhalt_simple (fm := fm) (A := ℕ × ℕ)
    (fun ⟨F, e⟩ ↦ ⟨e + F + 3, 0, 0, 0, e + 1⟩) ⟨0, 0⟩
  intro ⟨F, e⟩
  refine ⟨⟨F + 1, 2 * e + 2⟩, ?_⟩
  show ⟨e + F + 3, 0, 0, 0, e + 1⟩ [fm]⊢⁺ ⟨2 * e + 2 + (F + 1) + 3, 0, 0, 0, 2 * e + 2 + 1⟩
  rw [show 2 * e + 2 + (F + 1) + 3 = 2 * e + F + 6 from by ring,
      show 2 * e + 2 + 1 = 2 * e + 3 from by ring]
  exact main_trans
