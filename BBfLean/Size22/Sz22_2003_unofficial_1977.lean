import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #1977: [99/35, 25/6, 2/5, 7/11, 275/2]

Vector representation:
```
 0  2 -1 -1  1
-1 -1  2  0  0
 1  0 -1  0  0
 0  0  0  1 -1
-1  0  2  0  1
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_1977

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a, b, c+1, d+1, e⟩ => some ⟨a, b+2, c, d, e+1⟩
  | ⟨a+1, b+1, c, d, e⟩ => some ⟨a, b, c+2, d, e⟩
  | ⟨a, b, c+1, d, e⟩ => some ⟨a+1, b, c, d, e⟩
  | ⟨a, b, c, d, e+1⟩ => some ⟨a, b, c, d+1, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b, c+2, d, e+1⟩
  | _ => none

theorem e_to_d : ∀ e, ⟨a, 0, 0, d, e⟩ [fm]⊢* ⟨a, 0, 0, d + e, 0⟩ := by
  intro e; induction' e with e ih generalizing d
  · exists 0
  · rw [show d + (e + 1) = (d + 1) + e from by ring]
    step fm
    exact ih (d := d + 1)

theorem r3_chain : ∀ k, ⟨a, 0, k, 0, e⟩ [fm]⊢* ⟨a + k, 0, 0, 0, e⟩ := by
  intro k; induction' k with k ih generalizing a
  · exists 0
  · step fm
    apply stepStar_trans (ih (a := a + 1))
    ring_nf; finish

theorem flatten : ∀ b, ∀ a c e, ⟨a, b, c + 1, 0, e⟩ [fm]⊢* ⟨a + b + c + 1, 0, 0, 0, e⟩ := by
  intro b; induction' b with b ih <;> intro a c e
  · apply stepStar_trans (r3_chain (c + 1) (a := a) (e := e))
    ring_nf; finish
  · rcases a with _ | a
    · step fm; step fm
      show ⟨0, b, c + 2, 0, e⟩ [fm]⊢* ⟨0 + (b + 1) + c + 1, 0, 0, 0, e⟩
      rw [show c + 2 = (c + 1) + 1 from by ring]
      apply stepStar_trans (ih 0 (c + 1) e)
      ring_nf; finish
    · step fm
      show ⟨a, b, c + 3, 0, e⟩ [fm]⊢* ⟨a + 1 + (b + 1) + c + 1, 0, 0, 0, e⟩
      rw [show c + 3 = (c + 2) + 1 from by ring]
      apply stepStar_trans (ih a (c + 2) e)
      ring_nf; finish

theorem drain : ∀ D, ∀ F B E, ⟨F + D + 1, B + 1, 0, D, E⟩ [fm]⊢* ⟨F + 2 * D + B + 2, 0, 0, 0, E + D⟩ := by
  intro D; induction' D using Nat.strongRecOn with D ih
  intro F B E
  rcases D with _ | _ | D
  · -- D = 0: R2 then flatten
    step fm
    show ⟨F, B, 2, 0, E⟩ [fm]⊢* ⟨F + 2 * 0 + B + 2, 0, 0, 0, E + 0⟩
    rw [show (2 : ℕ) = 1 + 1 from by ring]
    apply stepStar_trans (flatten B F 1 E)
    ring_nf; finish
  · -- D = 1: R2, R1, then flatten
    step fm; step fm
    show ⟨F + 1, B + 2, 1, 0, E + 1⟩ [fm]⊢* ⟨F + 2 * 1 + B + 2, 0, 0, 0, E + 1⟩
    rw [show (1 : ℕ) = 0 + 1 from by ring]
    apply stepStar_trans (flatten (B + 2) (F + 1) 0 (E + 1))
    ring_nf; finish
  · -- D + 2: R2, R1, R1, then IH for D
    rw [show F + (D + 1 + 1) + 1 = (F + 1) + (D + 1) + 1 from by ring]
    step fm; step fm; step fm
    rw [show F + 1 + (D + 1) = (F + 1) + D + 1 from by ring,
        show B + 2 + 2 = (B + 3) + 1 from by ring,
        show E + 1 + 1 = E + 2 from by ring,
        show F + 2 * (D + 1 + 1) + B + 2 = (F + 1) + 2 * D + (B + 3) + 2 from by ring,
        show E + (D + 1 + 1) = E + 2 + D from by ring]
    exact ih D (by omega) (F + 1) (B + 3) (E + 2)

theorem trans_e0 : ⟨a + 1, 0, 0, 0, 0⟩ [fm]⊢⁺ ⟨a + 2, 0, 0, 0, 1⟩ := by
  execute fm 3

theorem trans_e1 : ⟨a + 2, 0, 0, 0, 1⟩ [fm]⊢⁺ ⟨a + 4, 0, 0, 0, 2⟩ := by
  step fm; step fm; step fm; step fm
  show ⟨a, 1, 3, 0, 2⟩ [fm]⊢* ⟨a + 4, 0, 0, 0, 2⟩
  rw [show (3 : ℕ) = 2 + 1 from by ring]
  apply stepStar_trans (flatten 1 a 2 2)
  ring_nf; finish

theorem trans_e2 : ⟨a + e + 3, 0, 0, 0, e + 2⟩ [fm]⊢⁺ ⟨a + 2 * e + 6, 0, 0, 0, e + 3⟩ := by
  apply stepStar_stepPlus_stepPlus
  · exact e_to_d (e + 2) (a := a + e + 3) (d := 0)
  rw [show 0 + (e + 2) = e + 2 from by ring]
  step fm; step fm; step fm
  show ⟨a + e + 2, 4, 0, e, 3⟩ [fm]⊢* ⟨a + 2 * e + 6, 0, 0, 0, e + 3⟩
  rw [show a + e + 2 = (a + 1) + e + 1 from by ring,
      show (4 : ℕ) = 3 + 1 from by ring]
  apply stepStar_trans (drain e (a + 1) 3 3)
  ring_nf; finish

theorem main_trans : ∀ e, ⟨a + e + 1, 0, 0, 0, e⟩ [fm]⊢⁺ ⟨a + 2 * e + 2, 0, 0, 0, e + 1⟩ := by
  intro e; rcases e with _ | _ | e
  · show ⟨a + 1, 0, 0, 0, 0⟩ [fm]⊢⁺ ⟨a + 2, 0, 0, 0, 1⟩
    exact trans_e0
  · show ⟨a + 2, 0, 0, 0, 1⟩ [fm]⊢⁺ ⟨a + 4, 0, 0, 0, 2⟩
    exact trans_e1
  · show ⟨a + e + 3, 0, 0, 0, e + 2⟩ [fm]⊢⁺ ⟨a + 2 * e + 6, 0, 0, 0, e + 3⟩
    exact trans_e2

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨4, 0, 0, 0, 2⟩) (by execute fm 13)
  apply progress_nonhalt_simple (fm := fm) (A := ℕ × ℕ)
    (fun ⟨a, e⟩ ↦ ⟨a + e + 1, 0, 0, 0, e⟩) ⟨1, 2⟩
  intro ⟨a, e⟩
  refine ⟨⟨a + e, e + 1⟩, ?_⟩
  show ⟨a + e + 1, 0, 0, 0, e⟩ [fm]⊢⁺ ⟨a + e + (e + 1) + 1, 0, 0, 0, e + 1⟩
  rw [show a + e + (e + 1) + 1 = a + 2 * e + 2 from by ring]
  exact main_trans e
