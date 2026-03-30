import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #749: [35/6, 4/55, 5929/2, 3/7, 5/3]

Vector representation:
```
-1 -1  1  1  0
 2  0 -1  0 -1
-1  0  0  2  2
 0  1  0 -1  0
 0 -1  1  0  0
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_749

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a+1, b+1, c, d, e⟩ => some ⟨a, b, c+1, d+1, e⟩
  | ⟨a, b, c+1, d, e+1⟩ => some ⟨a+2, b, c, d, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b, c, d+2, e+2⟩
  | ⟨a, b, c, d+1, e⟩ => some ⟨a, b+1, c, d, e⟩
  | ⟨a, b+1, c, d, e⟩ => some ⟨a, b, c+1, d, e⟩
  | _ => none

theorem r4_chain : ∀ k, ∀ b d e, ⟨0, b, 0, d + k, e⟩ [fm]⊢* ⟨0, b + k, 0, d, e⟩ := by
  intro k; induction' k with k ih <;> intro b d e
  · exists 0
  · rw [show d + (k + 1) = (d + k) + 1 from by ring]
    step fm
    apply stepStar_trans (ih (b + 1) d e)
    ring_nf; finish

theorem r1r1r2_even : ∀ k, ∀ c d e, ⟨2, 2 * k, c, d, e + k⟩ [fm]⊢* ⟨2, 0, c + k, d + 2 * k, e⟩ := by
  intro k; induction' k with k ih <;> intro c d e
  · exists 0
  · rw [show 2 * (k + 1) = (2 * k + 1) + 1 from by ring,
        show e + (k + 1) = (e + k) + 1 from by ring]
    step fm; step fm; step fm
    apply stepStar_trans (ih (c + 1) (d + 2) e)
    ring_nf; finish

theorem r1r1r2_odd : ∀ k, ∀ c d e, ⟨2, 2 * k + 1, c, d, e + k⟩ [fm]⊢* ⟨1, 0, c + k + 1, d + 2 * k + 1, e⟩ := by
  intro k; induction' k with k ih <;> intro c d e
  · step fm; finish
  · rw [show 2 * (k + 1) + 1 = (2 * k + 2) + 1 from by ring,
        show e + (k + 1) = (e + k) + 1 from by ring]
    step fm; step fm; step fm
    apply stepStar_trans (ih (c + 1) (d + 2) e)
    ring_nf; finish

theorem r2_chain : ∀ k, ∀ a c d, ⟨a, 0, c + k, d, k⟩ [fm]⊢* ⟨a + 2 * k, 0, c, d, 0⟩ := by
  intro k; induction' k with k ih <;> intro a c d
  · exists 0
  · rw [show c + (k + 1) = (c + k) + 1 from by ring]
    step fm
    apply stepStar_trans (ih (a + 2) c d)
    ring_nf; finish

theorem r3r2r2_chain : ∀ k, ∀ a d, ⟨a + 1, 0, 2 * k, d, 0⟩ [fm]⊢* ⟨a + 3 * k + 1, 0, 0, d + 2 * k, 0⟩ := by
  intro k; induction' k with k ih <;> intro a d
  · exists 0
  · rw [show 2 * (k + 1) = (2 * k + 1) + 1 from by ring]
    step fm; step fm; step fm
    apply stepStar_trans (ih (a + 3) (d + 2))
    ring_nf; finish

theorem r3r2_odd : ∀ k, ∀ a d, ⟨a + 1, 0, 2 * k + 1, d, 0⟩ [fm]⊢* ⟨a + 3 * k + 2, 0, 0, d + 2 * k + 2, 1⟩ := by
  intro k; induction' k with k ih <;> intro a d
  · step fm; step fm; finish
  · rw [show 2 * (k + 1) + 1 = (2 * k + 2) + 1 from by ring]
    step fm; step fm; step fm
    apply stepStar_trans (ih (a + 3) (d + 2))
    ring_nf; finish

theorem r3_drain : ∀ k, ∀ d e, ⟨k, 0, 0, d, e⟩ [fm]⊢* ⟨0, 0, 0, d + 2 * k, e + 2 * k⟩ := by
  intro k; induction' k with k ih <;> intro d e
  · exists 0
  · step fm
    apply stepStar_trans (ih (d + 2) (e + 2))
    ring_nf; finish

theorem phase12 (g h : ℕ) :
    ⟨0, 0, 0, 2 * g + h + 2, g + h + 2⟩ [fm]⊢⁺ ⟨2, 2 * g + h + 1, 0, 0, g + h + 1⟩ := by
  rw [show 2 * g + h + 2 = 0 + (2 * g + h + 1) + 1 from by ring]
  step fm
  apply stepStar_trans (r4_chain (2 * g + h + 1) 1 0 (g + h + 2))
  rw [show 1 + (2 * g + h + 1) = (2 * g + h + 1) + 1 from by ring]
  step fm; step fm; finish

theorem phase34_heven (g p : ℕ) :
    ⟨2, 2 * g + 2 * p + 1, 0, 0, g + 2 * p + 1⟩ [fm]⊢*
    ⟨2 * p + 3, 0, g, 2 * g + 2 * p + 1, 0⟩ := by
  rw [show 2 * g + 2 * p + 1 = 2 * (g + p) + 1 from by ring,
      show g + 2 * p + 1 = (p + 1) + (g + p) from by ring]
  apply stepStar_trans (r1r1r2_odd (g + p) 0 0 (p + 1))
  rw [show 0 + (g + p) + 1 = g + p + 1 from by ring,
      show 0 + 2 * (g + p) + 1 = 2 * g + 2 * p + 1 from by ring,
      show g + p + 1 = g + (p + 1) from by ring]
  apply stepStar_trans (r2_chain (p + 1) 1 g (2 * g + 2 * p + 1))
  ring_nf; finish

theorem phase34_hodd (g p : ℕ) :
    ⟨2, 2 * g + 2 * p + 2, 0, 0, g + 2 * p + 2⟩ [fm]⊢*
    ⟨2 * p + 4, 0, g, 2 * g + 2 * p + 2, 0⟩ := by
  rw [show 2 * g + 2 * p + 2 = 2 * (g + p + 1) from by ring,
      show g + 2 * p + 2 = (p + 1) + (g + p + 1) from by ring]
  apply stepStar_trans (r1r1r2_even (g + p + 1) 0 0 (p + 1))
  rw [show 0 + (g + p + 1) = g + p + 1 from by ring,
      show 0 + 2 * (g + p + 1) = 2 * g + 2 * p + 2 from by ring,
      show g + p + 1 = g + (p + 1) from by ring]
  apply stepStar_trans (r2_chain (p + 1) 2 g (2 * g + 2 * p + 2))
  ring_nf; finish

theorem phase56_geven (h j : ℕ) :
    ⟨h + 3, 0, 2 * j, 4 * j + h + 1, 0⟩ [fm]⊢*
    ⟨0, 0, 0, 12 * j + 3 * h + 7, 6 * j + 2 * h + 6⟩ := by
  rw [show h + 3 = (h + 2) + 1 from by ring]
  apply stepStar_trans (r3r2r2_chain j (h + 2) (4 * j + h + 1))
  rw [show h + 2 + 3 * j + 1 = h + 3 * j + 3 from by ring,
      show 4 * j + h + 1 + 2 * j = 6 * j + h + 1 from by ring]
  apply stepStar_trans (r3_drain (h + 3 * j + 3) (6 * j + h + 1) 0)
  ring_nf; finish

theorem phase56_godd (h j : ℕ) :
    ⟨h + 3, 0, 2 * j + 1, 4 * j + h + 3, 0⟩ [fm]⊢*
    ⟨0, 0, 0, 12 * j + 3 * h + 13, 6 * j + 2 * h + 9⟩ := by
  rw [show h + 3 = (h + 2) + 1 from by ring]
  apply stepStar_trans (r3r2_odd j (h + 2) (4 * j + h + 3))
  rw [show h + 2 + 3 * j + 2 = h + 3 * j + 4 from by ring,
      show 4 * j + h + 3 + 2 * j + 2 = 6 * j + h + 5 from by ring]
  apply stepStar_trans (r3_drain (h + 3 * j + 4) (6 * j + h + 5) 1)
  ring_nf; finish

theorem main_trans (g h : ℕ) :
    ⟨0, 0, 0, 2 * g + h + 2, g + h + 2⟩ [fm]⊢⁺
    ⟨0, 0, 0, 6 * g + 3 * h + 7, 3 * g + 2 * h + 6⟩ := by
  rcases Nat.even_or_odd h with ⟨p, hp⟩ | ⟨p, hp⟩
  · rw [show p + p = 2 * p from by ring] at hp; subst hp
    rcases Nat.even_or_odd g with ⟨j, hj⟩ | ⟨j, hj⟩
    · rw [show j + j = 2 * j from by ring] at hj; subst hj
      apply stepPlus_stepStar_stepPlus (phase12 (2 * j) (2 * p))
      apply stepStar_trans (phase34_heven (2 * j) p)
      convert phase56_geven (2 * p) j using 2; ring_nf
    · subst hj
      apply stepPlus_stepStar_stepPlus (phase12 (2 * j + 1) (2 * p))
      apply stepStar_trans (phase34_heven (2 * j + 1) p)
      convert phase56_godd (2 * p) j using 2; ring_nf
  · subst hp
    rcases Nat.even_or_odd g with ⟨j, hj⟩ | ⟨j, hj⟩
    · rw [show j + j = 2 * j from by ring] at hj; subst hj
      apply stepPlus_stepStar_stepPlus (phase12 (2 * j) (2 * p + 1))
      apply stepStar_trans (phase34_hodd (2 * j) p)
      convert phase56_geven (2 * p + 1) j using 2; ring_nf
    · subst hj
      apply stepPlus_stepStar_stepPlus (phase12 (2 * j + 1) (2 * p + 1))
      apply stepStar_trans (phase34_hodd (2 * j + 1) p)
      convert phase56_godd (2 * p + 1) j using 2; ring_nf

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨0, 0, 0, 2, 2⟩) (by execute fm 1)
  apply progress_nonhalt_simple (fm := fm) (A := ℕ × ℕ)
    (fun ⟨g, h⟩ ↦ ⟨0, 0, 0, 2 * g + h + 2, g + h + 2⟩) ⟨0, 0⟩
  intro ⟨g, h⟩
  refine ⟨⟨3 * g + h + 1, h + 3⟩, ?_⟩
  show ⟨0, 0, 0, 2 * g + h + 2, g + h + 2⟩ [fm]⊢⁺
    ⟨0, 0, 0, 2 * (3 * g + h + 1) + (h + 3) + 2, (3 * g + h + 1) + (h + 3) + 2⟩
  convert main_trans g h using 2; ring_nf

end Sz22_2003_unofficial_749
