import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #833: [35/6, 8/55, 847/2, 3/7, 5/3]

Vector representation:
```
-1 -1  1  1  0
 3  0 -1  0 -1
-1  0  0  1  2
 0  1  0 -1  0
 0 -1  1  0  0
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_833

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a+1, b+1, c, d, e⟩ => some ⟨a, b, c+1, d+1, e⟩
  | ⟨a, b, c+1, d, e+1⟩ => some ⟨a+3, b, c, d, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b, c, d+1, e+2⟩
  | ⟨a, b, c, d+1, e⟩ => some ⟨a, b+1, c, d, e⟩
  | ⟨a, b+1, c, d, e⟩ => some ⟨a, b, c+1, d, e⟩
  | _ => none

theorem d_to_b : ∀ k b d, ⟨(0 : ℕ), b, (0 : ℕ), d + k, e⟩ [fm]⊢* ⟨(0 : ℕ), b + k, (0 : ℕ), d, e⟩ := by
  intro k; induction' k with k ih <;> intro b d
  · exists 0
  · rw [show d + (k + 1) = (d + k) + 1 from by ring]
    step fm; apply stepStar_trans (ih (b + 1) d); ring_nf; finish

theorem r3_drain : ∀ k d e, ⟨k, (0 : ℕ), (0 : ℕ), d, e⟩ [fm]⊢* ⟨(0 : ℕ), (0 : ℕ), (0 : ℕ), d + k, e + 2 * k⟩ := by
  intro k; induction' k with k ih <;> intro d e
  · exists 0
  · step fm; apply stepStar_trans (ih (d + 1) (e + 2)); ring_nf; finish

theorem r2_drain : ∀ k a d e, ⟨a, (0 : ℕ), k, d, e + k⟩ [fm]⊢* ⟨a + 3 * k, (0 : ℕ), (0 : ℕ), d, e⟩ := by
  intro k; induction' k with k ih <;> intro a d e
  · exists 0
  · rw [show e + (k + 1) = (e + k) + 1 from by ring]
    step fm; apply stepStar_trans (ih (a + 3) d e); ring_nf; finish

theorem rounds : ∀ k b c d e, ⟨(3 : ℕ), b + 3 * k, c, d, e + k⟩ [fm]⊢* ⟨(3 : ℕ), b, c + 2 * k, d + 3 * k, e⟩ := by
  intro k; induction' k with k ih <;> intro b c d e
  · exists 0
  · rw [show b + 3 * (k + 1) = (b + 3) + 3 * k from by ring,
        show e + (k + 1) = (e + 1) + k from by ring]
    apply stepStar_trans (ih (b + 3) c d (e + 1))
    step fm; step fm; step fm; step fm
    ring_nf; finish

theorem opening (d : ℕ) : ⟨(0 : ℕ), (0 : ℕ), (0 : ℕ), d + 1, e + 1⟩ [fm]⊢* ⟨(3 : ℕ), d, (0 : ℕ), (0 : ℕ), e⟩ := by
  apply stepStar_trans
  · rw [show d + 1 = 0 + (d + 1) from by ring]
    exact d_to_b (d + 1) 0 0
  rw [show (0 : ℕ) + (d + 1) = d + 1 from by ring]
  step fm; step fm; finish

theorem transition (m e : ℕ) :
    ⟨(0 : ℕ), (0 : ℕ), (0 : ℕ), 3 * m + 1, e + 3 * m + 1⟩ [fm]⊢⁺
    ⟨(0 : ℕ), (0 : ℕ), (0 : ℕ), 9 * m + 3, e + 12 * m + 6⟩ := by
  suffices h : ⟨(0 : ℕ), (0 : ℕ), (0 : ℕ), 3 * m + 1, e + 3 * m + 1⟩ [fm]⊢*
      ⟨(0 : ℕ), (0 : ℕ), (0 : ℕ), 9 * m + 3, e + 12 * m + 6⟩ from
    stepStar_stepPlus h (by simp only [Q, ne_eq, Prod.mk.injEq]; omega)
  rw [show e + 3 * m + 1 = (e + 3 * m) + 1 from by ring]
  apply stepStar_trans (opening (3 * m) (e := e + 3 * m))
  rw [show e + 3 * m = (e + 2 * m) + m from by ring,
      show (3 : ℕ) * m = 0 + 3 * m from by ring]
  apply stepStar_trans (rounds m 0 0 0 (e + 2 * m))
  rw [show (0 : ℕ) + 2 * m = 2 * m from by ring,
      show (0 : ℕ) + 3 * m = 3 * m from by ring,
      show e + 2 * m = e + (2 * m) from by ring]
  apply stepStar_trans (r2_drain (2 * m) 3 (3 * m) e)
  rw [show 3 + 3 * (2 * m) = 6 * m + 3 from by ring]
  apply stepStar_trans (r3_drain (6 * m + 3) (3 * m) e)
  ring_nf; finish

theorem transition1 (m e : ℕ) :
    ⟨(0 : ℕ), (0 : ℕ), (0 : ℕ), 3 * m + 2, e + 3 * m + 2⟩ [fm]⊢⁺
    ⟨(0 : ℕ), (0 : ℕ), (0 : ℕ), 9 * m + 6, e + 12 * m + 10⟩ := by
  suffices h : ⟨(0 : ℕ), (0 : ℕ), (0 : ℕ), 3 * m + 2, e + 3 * m + 2⟩ [fm]⊢*
      ⟨(0 : ℕ), (0 : ℕ), (0 : ℕ), 9 * m + 6, e + 12 * m + 10⟩ from
    stepStar_stepPlus h (by simp only [Q, ne_eq, Prod.mk.injEq]; omega)
  rw [show e + 3 * m + 2 = (e + 3 * m + 1) + 1 from by ring]
  apply stepStar_trans (opening (3 * m + 1) (e := e + 3 * m + 1))
  rw [show e + 3 * m + 1 = (e + 2 * m + 1) + m from by ring,
      show (3 : ℕ) * m + 1 = 1 + 3 * m from by ring]
  apply stepStar_trans (rounds m 1 0 0 (e + 2 * m + 1))
  rw [show (0 : ℕ) + 2 * m = 2 * m from by ring,
      show (0 : ℕ) + 3 * m = 3 * m from by ring]
  step fm
  rw [show e + 2 * m + 1 = e + (2 * m + 1) from by ring]
  apply stepStar_trans (r2_drain (2 * m + 1) 2 (3 * m + 1) e)
  rw [show 2 + 3 * (2 * m + 1) = 6 * m + 5 from by ring]
  apply stepStar_trans (r3_drain (6 * m + 5) (3 * m + 1) e)
  ring_nf; finish

theorem transition2 (m e : ℕ) :
    ⟨(0 : ℕ), (0 : ℕ), (0 : ℕ), 3 * m + 3, e + 3 * m + 3⟩ [fm]⊢⁺
    ⟨(0 : ℕ), (0 : ℕ), (0 : ℕ), 9 * m + 9, e + 12 * m + 14⟩ := by
  suffices h : ⟨(0 : ℕ), (0 : ℕ), (0 : ℕ), 3 * m + 3, e + 3 * m + 3⟩ [fm]⊢*
      ⟨(0 : ℕ), (0 : ℕ), (0 : ℕ), 9 * m + 9, e + 12 * m + 14⟩ from
    stepStar_stepPlus h (by simp only [Q, ne_eq, Prod.mk.injEq]; omega)
  rw [show e + 3 * m + 3 = (e + 3 * m + 2) + 1 from by ring]
  apply stepStar_trans (opening (3 * m + 2) (e := e + 3 * m + 2))
  rw [show e + 3 * m + 2 = (e + 2 * m + 2) + m from by ring,
      show (3 : ℕ) * m + 2 = 2 + 3 * m from by ring]
  apply stepStar_trans (rounds m 2 0 0 (e + 2 * m + 2))
  rw [show (0 : ℕ) + 2 * m = 2 * m from by ring,
      show (0 : ℕ) + 3 * m = 3 * m from by ring]
  step fm; step fm
  rw [show e + 2 * m + 2 = e + (2 * m + 2) from by ring]
  apply stepStar_trans (r2_drain (2 * m + 2) 1 (3 * m + 2) e)
  rw [show 1 + 3 * (2 * m + 2) = 6 * m + 7 from by ring]
  apply stepStar_trans (r3_drain (6 * m + 7) (3 * m + 2) e)
  ring_nf; finish

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨0, 0, 0, 1, 2⟩) (by execute fm 1)
  apply progress_nonhalt (fm := fm)
    (P := fun q ↦ ∃ d e, q = ⟨0, 0, 0, d + 1, e + d + 1⟩)
  · intro c ⟨d, e, hq⟩; subst hq
    obtain ⟨m, rfl | rfl | rfl⟩ : ∃ m, d = 3 * m ∨ d = 3 * m + 1 ∨ d = 3 * m + 2 :=
      ⟨d / 3, by omega⟩
    · exact ⟨⟨0, 0, 0, 9 * m + 3, e + 12 * m + 6⟩,
        ⟨9 * m + 2, e + 3 * m + 3, by ring_nf⟩, transition m e⟩
    · exact ⟨⟨0, 0, 0, 9 * m + 6, e + 12 * m + 10⟩,
        ⟨9 * m + 5, e + 3 * m + 4, by ring_nf⟩, transition1 m e⟩
    · exact ⟨⟨0, 0, 0, 9 * m + 9, e + 12 * m + 14⟩,
        ⟨9 * m + 8, e + 3 * m + 5, by ring_nf⟩, transition2 m e⟩
  · exact ⟨0, 1, by ring_nf⟩
