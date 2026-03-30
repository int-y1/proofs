import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #730: [35/6, 4/55, 143/2, 3/7, 30/13]

Vector representation:
```
-1 -1  1  1  0  0
 2  0 -1  0 -1  0
-1  0  0  0  1  1
 0  1  0 -1  0  0
 1  1  1  0  0 -1
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_730

def Q := ℕ × ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a+1, b+1, c, d, e, f⟩ => some ⟨a, b, c+1, d+1, e, f⟩
  | ⟨a, b, c+1, d, e+1, f⟩ => some ⟨a+2, b, c, d, e, f⟩
  | ⟨a+1, b, c, d, e, f⟩ => some ⟨a, b, c, d, e+1, f+1⟩
  | ⟨a, b, c, d+1, e, f⟩ => some ⟨a, b+1, c, d, e, f⟩
  | ⟨a, b, c, d, e, f+1⟩ => some ⟨a+1, b+1, c+1, d, e, f⟩
  | _ => none

theorem r2_chain : ∀ k, ∀ a c d e g,
    ⟨a, 0, c + k, d, e + k, g⟩ [fm]⊢* ⟨a + 2 * k, 0, c, d, e, g⟩ := by
  intro k; induction' k with k ih <;> intro a c d e g
  · exists 0
  · rw [show c + (k + 1) = (c + k) + 1 from by ring,
        show e + (k + 1) = (e + k) + 1 from by ring]
    step fm
    apply stepStar_trans (ih (a + 2) c d e g)
    ring_nf; finish

theorem r3_drain : ∀ k, ∀ d e g,
    ⟨k, 0, 0, d, e, g⟩ [fm]⊢* ⟨0, 0, 0, d, e + k, g + k⟩ := by
  intro k; induction' k with k ih <;> intro d e g
  · exists 0
  · rw [show k + 1 = k + 1 from rfl]
    step fm
    apply stepStar_trans (ih d (e + 1) (g + 1))
    ring_nf; finish

theorem r4_drain : ∀ k, ∀ b e g,
    ⟨0, b, 0, k, e, g⟩ [fm]⊢* ⟨0, b + k, 0, 0, e, g⟩ := by
  intro k; induction' k with k ih <;> intro b e g
  · exists 0
  · rw [show k + 1 = k + 1 from rfl]
    step fm
    apply stepStar_trans (ih (b + 1) e g)
    ring_nf; finish

theorem interleaved_even : ∀ k, ∀ c d e g,
    ⟨0, 2 * k, c + 1, d, e + k, g⟩ [fm]⊢* ⟨0, 0, c + k + 1, d + 2 * k, e, g⟩ := by
  intro k; induction' k with k ih <;> intro c d e g
  · exists 0
  · rw [show 2 * (k + 1) = (2 * k + 1) + 1 from by ring,
        show e + (k + 1) = (e + k) + 1 from by ring]
    step fm
    rw [show 2 * k + 1 = (2 * k) + 1 from by ring]
    step fm; step fm
    apply stepStar_trans (ih (c + 1) (d + 2) e g)
    ring_nf; finish

theorem interleaved_odd : ∀ k, ∀ c d e g,
    ⟨0, 2 * k + 1, c + 1, d, e + k + 1, g⟩ [fm]⊢*
    ⟨0, 1, c + k + 1, d + 2 * k, e + 1, g⟩ := by
  intro k; induction' k with k ih <;> intro c d e g
  · exists 0
  · rw [show 2 * (k + 1) + 1 = (2 * k + 2) + 1 from by ring,
        show e + (k + 1) + 1 = (e + k + 1) + 1 from by ring]
    step fm
    rw [show 2 * k + 2 = (2 * k + 1) + 1 from by ring]
    step fm; step fm
    apply stepStar_trans (ih (c + 1) (d + 2) e g)
    ring_nf; finish

theorem main_even (m p : ℕ) :
    ⟨0, 2 * m + 1, 0, 0, 4 * m + 3, p + 1⟩ [fm]⊢⁺
    ⟨0, 2 * m + 2, 0, 0, 4 * m + 5, p + 2 * m + 5⟩ := by
  step fm; step fm
  rw [show 2 * m + 1 = 2 * m + 1 from rfl,
      show 4 * m + 3 = (3 * m + 2) + m + 1 from by ring]
  apply stepStar_trans (interleaved_odd m 1 1 (3 * m + 2) p)
  rw [show 1 + m + 1 = (m + 1) + 1 from by ring,
      show 1 + 2 * m = 2 * m + 1 from by ring,
      show 3 * m + 2 + 1 = (3 * m + 2) + 1 from by ring]
  step fm
  rw [show (2 : ℕ) = 1 + 1 from rfl]
  step fm
  rw [show m + 1 + 1 = 0 + (m + 2) from by ring,
      show 2 * m + 1 + 1 = 2 * m + 2 from by ring,
      show 3 * m + 2 = 2 * m + (m + 2) from by ring]
  apply stepStar_trans (r2_chain (m + 2) 1 0 (2 * m + 2) (2 * m) p)
  rw [show 1 + 2 * (m + 2) = 2 * m + 5 from by ring]
  apply stepStar_trans (r3_drain (2 * m + 5) (2 * m + 2) (2 * m) p)
  rw [show 2 * m + (2 * m + 5) = 4 * m + 5 from by ring,
      show p + (2 * m + 5) = p + 2 * m + 5 from by ring]
  convert r4_drain (2 * m + 2) 0 (4 * m + 5) (p + 2 * m + 5) using 2
  ring_nf

theorem main_odd (m p : ℕ) :
    ⟨0, 2 * m + 2, 0, 0, 4 * m + 5, p + 1⟩ [fm]⊢⁺
    ⟨0, 2 * m + 3, 0, 0, 4 * m + 7, p + 2 * m + 6⟩ := by
  step fm; step fm
  rw [show 2 * m + 2 = 2 * (m + 1) from by ring,
      show 4 * m + 5 = (3 * m + 4) + (m + 1) from by ring]
  apply stepStar_trans (interleaved_even (m + 1) 1 1 (3 * m + 4) p)
  rw [show 1 + (m + 1) + 1 = 0 + (m + 3) from by ring,
      show 1 + 2 * (m + 1) = 2 * m + 3 from by ring,
      show 3 * m + 4 = (2 * m + 1) + (m + 3) from by ring]
  apply stepStar_trans (r2_chain (m + 3) 0 0 (2 * m + 3) (2 * m + 1) p)
  rw [show 0 + 2 * (m + 3) = 2 * m + 6 from by ring]
  apply stepStar_trans (r3_drain (2 * m + 6) (2 * m + 3) (2 * m + 1) p)
  rw [show 2 * m + 1 + (2 * m + 6) = 4 * m + 7 from by ring,
      show p + (2 * m + 6) = p + 2 * m + 6 from by ring]
  convert r4_drain (2 * m + 3) 0 (4 * m + 7) (p + 2 * m + 6) using 2
  ring_nf

theorem main_trans (n p : ℕ) :
    ⟨0, n + 1, 0, 0, 2 * n + 3, p + 1⟩ [fm]⊢⁺
    ⟨0, n + 2, 0, 0, 2 * n + 5, p + n + 5⟩ := by
  rcases Nat.even_or_odd n with ⟨m, hm⟩ | ⟨m, hm⟩
  · rw [show m + m = 2 * m from by ring] at hm; subst hm
    convert main_even m p using 2; ring_nf
  · subst hm
    convert main_odd m p using 2; ring_nf

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨0, 1, 0, 0, 3, 4⟩) (by execute fm 10)
  apply progress_nonhalt_simple (fm := fm) (A := ℕ × ℕ)
    (fun ⟨n, p⟩ ↦ ⟨0, n + 1, 0, 0, 2 * n + 3, p + 1⟩) ⟨0, 3⟩
  intro ⟨n, p⟩; exact ⟨⟨n + 1, p + n + 4⟩, main_trans n p⟩

end Sz22_2003_unofficial_730
