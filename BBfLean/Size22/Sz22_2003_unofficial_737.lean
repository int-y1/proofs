import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #737: [35/6, 4/55, 143/2, 3/7, 75/13]

Vector representation:
```
-1 -1  1  1  0  0
 2  0 -1  0 -1  0
-1  0  0  0  1  1
 0  1  0 -1  0  0
 0  1  2  0  0 -1
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_737

def Q := ℕ × ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a+1, b+1, c, d, e, f⟩ => some ⟨a, b, c+1, d+1, e, f⟩
  | ⟨a, b, c+1, d, e+1, f⟩ => some ⟨a+2, b, c, d, e, f⟩
  | ⟨a+1, b, c, d, e, f⟩ => some ⟨a, b, c, d, e+1, f+1⟩
  | ⟨a, b, c, d+1, e, f⟩ => some ⟨a, b+1, c, d, e, f⟩
  | ⟨a, b, c, d, e, f+1⟩ => some ⟨a, b+1, c+2, d, e, f⟩
  | _ => none

theorem r4_chain : ∀ k b e f, ⟨0, b, 0, k, e, f⟩ [fm]⊢* ⟨0, b + k, 0, 0, e, f⟩ := by
  intro k; induction' k with k ih <;> intro b e f
  · exists 0
  · step fm
    apply stepStar_trans (ih (b + 1) e f)
    ring_nf; finish

theorem r3_chain : ∀ k a d e f, ⟨a + k, 0, 0, d, e, f⟩ [fm]⊢* ⟨a, 0, 0, d, e + k, f + k⟩ := by
  intro k; induction' k with k ih <;> intro a d e f
  · exists 0
  · rw [show a + (k + 1) = (a + k) + 1 from by ring]
    step fm
    apply stepStar_trans (ih a d (e + 1) (f + 1))
    ring_nf; finish

theorem r2_chain : ∀ k a c d e f, ⟨a, 0, c + k, d, e + k, f⟩ [fm]⊢* ⟨a + 2 * k, 0, c, d, e, f⟩ := by
  intro k; induction' k with k ih <;> intro a c d e f
  · exists 0
  · rw [show c + (k + 1) = (c + k) + 1 from by ring,
        show e + (k + 1) = (e + k) + 1 from by ring]
    step fm
    apply stepStar_trans (ih (a + 2) c d e f)
    ring_nf; finish

theorem r1r1r2_chain : ∀ k b c d e f,
    ⟨2, b + 2 * k, c, d, e + k, f⟩ [fm]⊢* ⟨2, b, c + k, d + 2 * k, e, f⟩ := by
  intro k; induction' k with k ih <;> intro b c d e f
  · exists 0
  · rw [show b + 2 * (k + 1) = (b + 2 * k) + 2 from by ring,
        show e + (k + 1) = (e + k) + 1 from by ring]
    step fm; step fm; step fm
    apply stepStar_trans (ih b (c + 1) (d + 2) e f)
    ring_nf; finish

theorem main_even (m g : ℕ) :
    ⟨0, 0, 0, 2 * m + 2, 4 * m + 5, g + 1⟩ [fm]⊢⁺
    ⟨0, 0, 0, 2 * m + 3, 4 * m + 7, g + 2 * m + 7⟩ := by
  apply stepStar_stepPlus_stepPlus (r4_chain (2 * m + 2) 0 (4 * m + 5) (g + 1))
  rw [show 0 + (2 * m + 2) = (2 * m + 2) from by ring,
      show 4 * m + 5 = (4 * m + 4) + 1 from by ring]
  step fm; step fm
  rw [show 2 * m + 2 + 1 = 1 + 2 * (m + 1) from by ring,
      show 4 * m + 4 = (3 * m + 3) + (m + 1) from by ring]
  apply stepStar_trans (r1r1r2_chain (m + 1) 1 1 0 (3 * m + 3) g)
  rw [show 1 + (m + 1) = m + 2 from by ring,
      show 0 + 2 * (m + 1) = 2 * m + 2 from by ring]
  step fm
  rw [show m + 2 + 1 = 0 + (m + 3) from by ring,
      show 2 * m + 2 + 1 = 2 * m + 3 from by ring,
      show 3 * m + 3 = (2 * m) + (m + 3) from by ring]
  apply stepStar_trans (r2_chain (m + 3) 1 0 (2 * m + 3) (2 * m) g)
  rw [show 1 + 2 * (m + 3) = 0 + (2 * m + 7) from by ring]
  apply stepStar_trans (r3_chain (2 * m + 7) 0 (2 * m + 3) (2 * m) g)
  ring_nf; finish

theorem main_odd (m g : ℕ) :
    ⟨0, 0, 0, 2 * m + 3, 4 * m + 7, g + 1⟩ [fm]⊢⁺
    ⟨0, 0, 0, 2 * m + 4, 4 * m + 9, g + 2 * m + 8⟩ := by
  apply stepStar_stepPlus_stepPlus (r4_chain (2 * m + 3) 0 (4 * m + 7) (g + 1))
  rw [show 0 + (2 * m + 3) = (2 * m + 3) from by ring,
      show 4 * m + 7 = (4 * m + 6) + 1 from by ring]
  step fm; step fm
  rw [show 2 * m + 3 + 1 = 0 + 2 * (m + 2) from by ring,
      show 4 * m + 6 = (3 * m + 4) + (m + 2) from by ring]
  apply stepStar_trans (r1r1r2_chain (m + 2) 0 1 0 (3 * m + 4) g)
  rw [show 1 + (m + 2) = 0 + (m + 3) from by ring,
      show 0 + 2 * (m + 2) = 2 * m + 4 from by ring,
      show 3 * m + 4 = (2 * m + 1) + (m + 3) from by ring]
  apply stepStar_trans (r2_chain (m + 3) 2 0 (2 * m + 4) (2 * m + 1) g)
  rw [show 2 + 2 * (m + 3) = 0 + (2 * m + 8) from by ring]
  apply stepStar_trans (r3_chain (2 * m + 8) 0 (2 * m + 4) (2 * m + 1) g)
  ring_nf; finish

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨0, 0, 0, 2, 5, 10⟩) (by execute fm 25)
  apply progress_nonhalt (fm := fm)
    (P := fun q ↦ ∃ n g, q = ⟨0, 0, 0, n + 2, 2 * n + 5, g + 1⟩)
  · intro c ⟨n, g, hq⟩; subst hq
    rcases Nat.even_or_odd n with ⟨m, hm⟩ | ⟨m, hm⟩
    · rw [show m + m = 2 * m from by ring] at hm; subst hm
      refine ⟨⟨0, 0, 0, 2 * m + 3, 4 * m + 7, g + 2 * m + 7⟩,
        ⟨2 * m + 1, g + 2 * m + 6, by ring_nf⟩, ?_⟩
      convert main_even m g using 2; ring_nf
    · subst hm
      refine ⟨⟨0, 0, 0, 2 * m + 4, 4 * m + 9, g + 2 * m + 8⟩,
        ⟨2 * m + 2, g + 2 * m + 7, by ring_nf⟩, ?_⟩
      convert main_odd m g using 2; ring_nf
  · exact ⟨0, 9, by ring_nf⟩

end Sz22_2003_unofficial_737
