import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #754: [35/6, 4/55, 847/2, 3/7, 25/11]

Vector representation:
```
-1 -1  1  1  0
 2  0 -1  0 -1
-1  0  0  1  2
 0  1  0 -1  0
 0  0  2  0 -1
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_754

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a+1, b+1, c, d, e⟩ => some ⟨a, b, c+1, d+1, e⟩
  | ⟨a, b, c+1, d, e+1⟩ => some ⟨a+2, b, c, d, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b, c, d+1, e+2⟩
  | ⟨a, b, c, d+1, e⟩ => some ⟨a, b+1, c, d, e⟩
  | ⟨a, b, c, d, e+1⟩ => some ⟨a, b, c+2, d, e⟩
  | _ => none

theorem r2r1r1_chain : ∀ j, ∀ c d e, ⟨0, 2 * j, c + 1, d, e + j⟩ [fm]⊢* ⟨0, 0, c + j + 1, d + 2 * j, e⟩ := by
  intro j; induction' j with j ih <;> intro c d e
  · exists 0
  · rw [show 2 * (j + 1) = (2 * j + 1) + 1 from by ring,
        show e + (j + 1) = (e + j) + 1 from by ring]
    step fm
    rw [show 2 * j + 1 = (2 * j) + 1 from by ring]
    step fm; step fm
    apply stepStar_trans (ih (c + 1) (d + 2) e)
    ring_nf; finish

theorem r2_chain : ∀ j, ∀ a c d e, ⟨a, 0, c + j, d, e + j⟩ [fm]⊢* ⟨a + 2 * j, 0, c, d, e⟩ := by
  intro j; induction' j with j ih <;> intro a c d e
  · exists 0
  · rw [show c + (j + 1) = (c + j) + 1 from by ring,
        show e + (j + 1) = (e + j) + 1 from by ring]
    step fm
    apply stepStar_trans (ih (a + 2) c d e)
    ring_nf; finish

theorem r3_chain : ∀ j, ∀ a d e, ⟨a + j, 0, 0, d, e⟩ [fm]⊢* ⟨a, 0, 0, d + j, e + 2 * j⟩ := by
  intro j; induction' j with j ih <;> intro a d e
  · exists 0
  · rw [show a + (j + 1) = (a + j) + 1 from by ring]
    step fm
    apply stepStar_trans (ih a (d + 1) (e + 2))
    ring_nf; finish

theorem r4_chain : ∀ j, ∀ b d e, ⟨0, b, 0, d + j, e⟩ [fm]⊢* ⟨0, b + j, 0, d, e⟩ := by
  intro j; induction' j with j ih <;> intro b d e
  · exists 0
  · rw [show d + (j + 1) = (d + j) + 1 from by ring]
    step fm
    apply stepStar_trans (ih (b + 1) d e)
    ring_nf; finish

theorem main_trans (k g : ℕ) :
    ⟨0, 2 * k, 0, 0, 2 * k + g + 3⟩ [fm]⊢⁺ ⟨0, 4 * k + 4, 0, 0, 4 * k + g + 8⟩ := by
  rw [show 2 * k + g + 3 = (2 * k + g + 2) + 1 from by ring]
  apply step_stepStar_stepPlus
  · show fm ⟨0, 2 * k, 0, 0, (2 * k + g + 2) + 1⟩ = some ⟨0, 2 * k, 0 + 2, 0, 2 * k + g + 2⟩
    simp [fm]
  rw [show 2 * k + g + 2 = (k + g + 2) + k from by ring]
  apply stepStar_trans (r2r1r1_chain k 1 0 (k + g + 2))
  rw [show 1 + k + 1 = 0 + (k + 2) from by ring,
      show 0 + 2 * k = 2 * k from by ring,
      show k + g + 2 = g + (k + 2) from by ring]
  apply stepStar_trans (r2_chain (k + 2) 0 0 (2 * k) g)
  rw [show 0 + 2 * (k + 2) = 0 + (2 * k + 4) from by ring]
  apply stepStar_trans (r3_chain (2 * k + 4) 0 (2 * k) g)
  rw [show 2 * k + (2 * k + 4) = 0 + (4 * k + 4) from by ring,
      show g + 2 * (2 * k + 4) = 4 * k + g + 8 from by ring]
  apply stepStar_trans (r4_chain (4 * k + 4) 0 0 (4 * k + g + 8))
  ring_nf; finish

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨0, 16, 0, 0, 19⟩)
  · apply stepStar_trans (show c₀ [fm]⊢* ⟨0, 6, 0, 0, 8⟩ from by execute fm 18)
    step fm
    rw [show (7 : ℕ) = 4 + 3 from by ring]
    apply stepStar_trans (r2r1r1_chain 3 1 0 4)
    rw [show 1 + 3 + 1 = 0 + 5 from by ring,
        show 0 + 2 * 3 = 6 from by ring,
        show (4 : ℕ) = 0 + 4 from by ring]
    apply stepStar_trans (r2_chain 4 0 1 6 0)
    rw [show 0 + 2 * 4 = 8 from by ring]
    step fm
    step fm
    apply stepStar_trans (r3_chain 9 0 7 1)
    rw [show 7 + 9 = 0 + 16 from by ring,
        show 1 + 2 * 9 = 19 from by ring]
    exact r4_chain 16 0 0 19
  apply progress_nonhalt_simple (fm := fm) (A := ℕ × ℕ)
    (fun ⟨k, g⟩ ↦ ⟨0, 2 * k, 0, 0, 2 * k + g + 3⟩) ⟨8, 0⟩
  intro ⟨k, g⟩
  exact ⟨⟨2 * k + 2, g + 1⟩, by convert main_trans k g using 2; ring_nf⟩

end Sz22_2003_unofficial_754
