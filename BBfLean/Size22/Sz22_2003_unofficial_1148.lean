import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #1148: [5/6, 44/35, 539/2, 3/11, 6/7]

Vector representation:
```
-1 -1  1  0  0
 2  0 -1 -1  1
-1  0  0  2  1
 0  1  0  0 -1
 1  1  0 -1  0
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_1148

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a+1, b+1, c, d, e⟩ => some ⟨a, b, c+1, d, e⟩
  | ⟨a, b, c+1, d+1, e⟩ => some ⟨a+2, b, c, d, e+1⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b, c, d+2, e+1⟩
  | ⟨a, b, c, d, e+1⟩ => some ⟨a, b+1, c, d, e⟩
  | ⟨a, b, c, d+1, e⟩ => some ⟨a+1, b+1, c, d, e⟩
  | _ => none

theorem e_to_b : ∀ k, ∀ b d, ⟨0, b, 0, d, k⟩ [fm]⊢* ⟨0, b + k, 0, d, 0⟩ := by
  intro k; induction' k with k ih <;> intro b d
  · exists 0
  · step fm; apply stepStar_trans (ih (b + 1) d); ring_nf; finish

theorem r3_drain : ∀ k, ∀ d e, ⟨k, 0, 0, d, e⟩ [fm]⊢* ⟨0, 0, 0, d + 2 * k, e + k⟩ := by
  intro k; induction' k with k ih <;> intro d e
  · exists 0
  · step fm; apply stepStar_trans (ih (d + 2) (e + 1)); ring_nf; finish

theorem r1r1r2_round (B c D e : ℕ) :
    ⟨2, B + 2, c, D + 1, e⟩ [fm]⊢* ⟨2, B, c + 1, D, e + 1⟩ := by
  step fm; step fm; step fm; ring_nf; finish

theorem r1r1r2_chain : ∀ k, ∀ b c d e,
    ⟨2, b + 2 * k, c, d + k, e⟩ [fm]⊢* ⟨2, b, c + k, d, e + k⟩ := by
  intro k; induction' k with k ih <;> intro b c d e
  · exists 0
  · rw [show b + 2 * (k + 1) = (b + 2 * k) + 2 from by ring,
        show d + (k + 1) = (d + k) + 1 from by ring]
    apply stepStar_trans (r1r1r2_round (b + 2 * k) c (d + k) e)
    apply stepStar_trans (ih b (c + 1) d (e + 1))
    ring_nf; finish

theorem cleanup : ∀ C, ∀ A D E,
    ⟨A + 1, 0, C, D, E⟩ [fm]⊢* ⟨0, 0, 0, D + 2 * A + 3 * C + 2, E + A + 3 * C + 1⟩ := by
  intro C; induction' C with C ih <;> intro A D E
  · apply stepStar_trans (r3_drain (A + 1) D E); ring_nf; finish
  · rcases D with _ | D
    · step fm; step fm
      apply stepStar_trans (ih (A + 1) 1 (E + 2)); ring_nf; finish
    · step fm
      apply stepStar_trans (ih (A + 2) D (E + 1)); ring_nf; finish

theorem opening : ⟨0, b + 1, 0, d + 2, 0⟩ [fm]⊢⁺ ⟨2, b + 1, 0, d, 1⟩ := by
  step fm; step fm; step fm; ring_nf; finish

theorem middle_phase (k : ℕ) (D : ℕ) (hD : D ≥ k + 2) :
    ⟨0, 2 * k + 1, 0, D, 0⟩ [fm]⊢* ⟨0, 0, 0, D + 2 * k + 3, 4 * k + 5⟩ := by
  obtain ⟨d₀, rfl⟩ : ∃ d₀, D = d₀ + (k + 2) := ⟨D - (k + 2), by omega⟩
  rw [show d₀ + (k + 2) = (d₀ + k) + 2 from by ring,
      show 2 * k + 1 = (2 * k) + 1 from by ring]
  apply stepStar_trans (stepPlus_stepStar (opening (b := 2 * k) (d := d₀ + k)))
  rw [show (2 * k) + 1 = 1 + 2 * k from by ring]
  apply stepStar_trans (r1r1r2_chain k 1 0 d₀ 1)
  step fm
  rw [show (0 : ℕ) + k + 1 = k + 1 from by ring,
      show (1 : ℕ) + k = k + 1 from by ring]
  apply stepStar_trans (cleanup (k + 1) 0 d₀ (k + 1))
  ring_nf; finish

theorem full_cycle (k : ℕ) (D : ℕ) (hD : D ≥ k + 2) :
    ⟨0, 0, 0, D, 2 * k + 1⟩ [fm]⊢⁺ ⟨0, 0, 0, D + 2 * k + 3, 4 * k + 5⟩ := by
  apply stepStar_stepPlus_stepPlus (e_to_b (2 * k + 1) 0 D)
  rw [show 0 + (2 * k + 1) = 2 * k + 1 from by ring]
  apply stepStar_stepPlus
  · exact middle_phase k D hD
  · intro h; simp [Q] at h

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨0, 0, 0, 2, 1⟩)
  · execute fm 1
  apply progress_nonhalt_simple (fm := fm) (A := ℕ × ℕ)
    (fun ⟨k, D⟩ ↦ ⟨0, 0, 0, D + k + 2, 2 * k + 1⟩) ⟨0, 0⟩
  intro ⟨k, D⟩
  exists ⟨2 * k + 2, D + k + 1⟩
  show ⟨0, 0, 0, D + k + 2, 2 * k + 1⟩ [fm]⊢⁺
       ⟨0, 0, 0, (D + k + 1) + (2 * k + 2) + 2, 2 * (2 * k + 2) + 1⟩
  rw [show (D + k + 1) + (2 * k + 2) + 2 = (D + k + 2) + 2 * k + 3 from by ring,
      show 2 * (2 * k + 2) + 1 = 4 * k + 5 from by ring]
  exact full_cycle k (D + k + 2) (by omega)

end Sz22_2003_unofficial_1148
