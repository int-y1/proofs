import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #1344: [63/10, 28/33, 121/2, 5/7, 3/11]

Vector representation:
```
-1  2 -1  1  0
 2 -1  0  1 -1
-1  0  0  0  2
 0  0  1 -1  0
 0  1  0  0 -1
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_1344

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a+1, b, c+1, d, e⟩ => some ⟨a, b+2, c, d+1, e⟩
  | ⟨a, b+1, c, d, e+1⟩ => some ⟨a+2, b, c, d+1, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b, c, d, e+2⟩
  | ⟨a, b, c, d+1, e⟩ => some ⟨a, b, c+1, d, e⟩
  | ⟨a, b, c, d, e+1⟩ => some ⟨a, b+1, c, d, e⟩
  | _ => none

theorem r3_chain : ∀ k, ∀ a d e, ⟨a + k, (0 : ℕ), 0, d, e⟩ [fm]⊢* ⟨a, 0, 0, d, e + 2 * k⟩ := by
  intro k; induction' k with k ih <;> intro a d e
  · exists 0
  · rw [show a + (k + 1) = (a + k) + 1 from by ring]
    step fm
    apply stepStar_trans (ih a d (e + 2))
    ring_nf; finish

theorem r4_chain : ∀ k, ∀ c d e, ⟨(0 : ℕ), 0, c, d + k, e⟩ [fm]⊢* ⟨0, 0, c + k, d, e⟩ := by
  intro k; induction' k with k ih <;> intro c d e
  · exists 0
  · rw [show d + (k + 1) = (d + k) + 1 from by ring]
    step fm
    rw [show c + (k + 1) = (c + 1) + k from by ring]
    exact ih (c + 1) d e

theorem r2_chain : ∀ k, ∀ a b d e, ⟨a, b + k, (0 : ℕ), d, e + k⟩ [fm]⊢* ⟨a + 2 * k, b, 0, d + k, e⟩ := by
  intro k; induction' k with k ih <;> intro a b d e
  · exists 0
  · rw [show b + (k + 1) = (b + k) + 1 from by ring,
        show e + (k + 1) = (e + k) + 1 from by ring]
    step fm
    rw [show a + 2 * (k + 1) = (a + 2) + 2 * k from by ring,
        show d + (k + 1) = (d + 1) + k from by ring]
    exact ih (a + 2) b (d + 1) e

theorem gen : ∀ c, ∀ D, ⟨(0 : ℕ), D + 1, c, D, 2 * c + D + 1⟩ [fm]⊢* ⟨3 * c + 2 * D + 2, 0, 0, 3 * c + 2 * D + 1, 0⟩ := by
  intro c; induction' c using Nat.strongRecOn with c ih; intro D
  rcases c with _ | _ | c
  · -- c = 0: R2 drain.
    have h := r2_chain (D + 1) 0 0 D 0
    convert h using 2; ring_nf
  · -- c = 1: R2, R1, then R2 drain.
    rw [show 2 * 1 + D + 1 = (D + 2) + 1 from by ring]
    step fm
    step fm
    have h := r2_chain (D + 2) 1 0 (D + 2) 0
    convert h using 2; ring_nf
  · -- c + 2: R2, R1, R1, then apply IH with c and D+3.
    rw [show 2 * (c + 2) + D + 1 = (2 * c + D + 4) + 1 from by ring]
    step fm
    step fm
    step fm
    rw [show D + 4 = (D + 3) + 1 from by ring,
        show 2 * c + D + 4 = 2 * c + (D + 3) + 1 from by ring]
    apply stepStar_trans (ih c (by omega) (D + 3))
    ring_nf; finish

theorem main_trans (d : ℕ) : ⟨d + 1, (0 : ℕ), 0, d, 0⟩ [fm]⊢⁺ ⟨3 * d + 2, 0, 0, 3 * d + 1, 0⟩ := by
  have h1 : ⟨d + 1, (0 : ℕ), 0, d, 0⟩ [fm]⊢* ⟨0, 0, 0, d, 2 * d + 2⟩ := by
    rw [show d + 1 = 0 + (d + 1) from by ring,
        show 2 * d + 2 = 0 + 2 * (d + 1) from by ring]
    exact r3_chain (d + 1) 0 d 0
  have h2 : ⟨(0 : ℕ), 0, 0, d, 2 * d + 2⟩ [fm]⊢* ⟨0, 0, d, 0, 2 * d + 2⟩ := by
    have := r4_chain d 0 0 (2 * d + 2)
    simpa using this
  have h3 : ⟨(0 : ℕ), 0, d, 0, 2 * d + 2⟩ [fm]⊢⁺ ⟨0, 1, d, 0, 2 * d + 1⟩ := by
    rw [show 2 * d + 2 = (2 * d + 1) + 1 from by ring]
    step fm; finish
  have h4 : ⟨(0 : ℕ), 1, d, 0, 2 * d + 1⟩ [fm]⊢* ⟨3 * d + 2, 0, 0, 3 * d + 1, 0⟩ := by
    rw [show (1 : ℕ) = 0 + 1 from by ring,
        show 2 * d + 1 = 2 * d + 0 + 1 from by ring,
        show 3 * d + 2 = 3 * d + 2 * 0 + 2 from by ring,
        show 3 * d + 1 = 3 * d + 2 * 0 + 1 from by ring]
    exact gen d 0
  exact stepStar_stepPlus_stepPlus h1
    (stepStar_stepPlus_stepPlus h2
      (stepPlus_stepStar_stepPlus h3 h4))

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨2, 0, 0, 1, 0⟩) (by execute fm 3)
  apply progress_nonhalt_simple (fm := fm) (A := ℕ)
    (fun d ↦ ⟨d + 2, 0, 0, d + 1, 0⟩) 0
  intro d; refine ⟨3 * d + 3, ?_⟩
  rw [show d + 2 = (d + 1) + 1 from by ring,
      show 3 * d + 3 + 2 = 3 * (d + 1) + 2 from by ring,
      show 3 * d + 3 + 1 = 3 * (d + 1) + 1 from by ring]
  exact main_trans (d + 1)

end Sz22_2003_unofficial_1344
