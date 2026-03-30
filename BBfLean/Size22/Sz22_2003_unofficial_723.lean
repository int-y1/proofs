import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #723: [35/6, 4/55, 143/2, 3/7, 15/13]

Vector representation:
```
-1 -1  1  1  0  0
 2  0 -1  0 -1  0
-1  0  0  0  1  1
 0  1  0 -1  0  0
 0  1  1  0  0 -1
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_723

def Q := ℕ × ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a+1, b+1, c, d, e, f⟩ => some ⟨a, b, c+1, d+1, e, f⟩
  | ⟨a, b, c+1, d, e+1, f⟩ => some ⟨a+2, b, c, d, e, f⟩
  | ⟨a+1, b, c, d, e, f⟩ => some ⟨a, b, c, d, e+1, f+1⟩
  | ⟨a, b, c, d+1, e, f⟩ => some ⟨a, b+1, c, d, e, f⟩
  | ⟨a, b, c, d, e, f+1⟩ => some ⟨a, b+1, c+1, d, e, f⟩
  | _ => none

theorem r4_chain : ∀ k, ∀ b d e f, ⟨0, b, 0, d + k, e, f⟩ [fm]⊢* ⟨0, b + k, 0, d, e, f⟩ := by
  intro k; induction' k with k ih <;> intro b d e f
  · exists 0
  · rw [show d + (k + 1) = (d + k) + 1 from by ring]
    step fm
    apply stepStar_trans (ih (b + 1) d e f)
    ring_nf; finish

theorem r3_chain : ∀ k, ∀ a d e f, ⟨a + k, 0, 0, d, e, f⟩ [fm]⊢* ⟨a, 0, 0, d, e + k, f + k⟩ := by
  intro k; induction' k with k ih <;> intro a d e f
  · exists 0
  · rw [show a + (k + 1) = (a + k) + 1 from by ring]
    step fm
    apply stepStar_trans (ih a d (e + 1) (f + 1))
    ring_nf; finish

theorem r2_drain : ∀ k, ∀ a c d e f, ⟨a, 0, c + k, d, e + k, f⟩ [fm]⊢* ⟨a + 2 * k, 0, c, d, e, f⟩ := by
  intro k; induction' k with k ih <;> intro a c d e f
  · exists 0
  · rw [show c + (k + 1) = (c + k) + 1 from by ring,
        show e + (k + 1) = (e + k) + 1 from by ring]
    step fm
    apply stepStar_trans (ih (a + 2) c d e f)
    ring_nf; finish

theorem r1r1r2_even : ∀ k, ∀ c d e f, ⟨2, 2 * k, c, d, e + k, f⟩ [fm]⊢* ⟨2, 0, c + k, d + 2 * k, e, f⟩ := by
  intro k; induction' k with k ih <;> intro c d e f
  · exists 0
  · rw [show 2 * (k + 1) = (2 * k + 1) + 1 from by ring,
        show e + (k + 1) = (e + k) + 1 from by ring]
    step fm
    rw [show 2 * k + 1 = (2 * k) + 1 from by ring]
    step fm; step fm
    apply stepStar_trans (ih (c + 1) (d + 2) e f)
    ring_nf; finish

theorem r1r1r2_odd : ∀ k, ∀ c d e f, ⟨2, 2 * k + 1, c, d, e + k + 1, f⟩ [fm]⊢* ⟨1, 0, c + k + 1, d + 2 * k + 1, e + 1, f⟩ := by
  intro k; induction' k with k ih <;> intro c d e f
  · step fm; finish
  · rw [show 2 * (k + 1) + 1 = (2 * k + 2) + 1 from by ring,
        show e + (k + 1) + 1 = (e + k + 1) + 1 from by ring]
    step fm
    rw [show 2 * k + 2 = (2 * k + 1) + 1 from by ring]
    step fm; step fm
    apply stepStar_trans (ih (c + 1) (d + 2) e f)
    ring_nf; finish

-- Combined: R1R1R2 even chain + R2 drain
theorem interleaved_even (m f : ℕ) :
    ⟨2, 2 * (m + 1), 0, 0, m + (m + 1), f⟩ [fm]⊢* ⟨2 + 2 * m, 0, 1, 2 * m + 2, 0, f⟩ := by
  apply stepStar_trans (r1r1r2_even (m + 1) 0 0 m f)
  have h := r2_drain m 2 1 (2 * m + 2) 0 f
  convert h using 2; ring_nf

-- Combined: R1R1R2 odd chain + R2 drain
theorem interleaved_odd (m f : ℕ) :
    ⟨2, 2 * (m + 1) + 1, 0, 0, m + (m + 1) + 1, f⟩ [fm]⊢* ⟨1 + 2 * (m + 1), 0, 1, 2 * m + 3, 0, f⟩ := by
  apply stepStar_trans (r1r1r2_odd (m + 1) 0 0 m f)
  have h := r2_drain (m + 1) 1 1 (2 * m + 3) 0 f
  convert h using 2; ring_nf

-- Even case
theorem main_even (m g : ℕ) :
    ⟨0, 0, 0, 2 * m + 1, 2 * m + 2, g + 3⟩ [fm]⊢⁺ ⟨0, 0, 0, 2 * m + 2, 2 * m + 3, g + 2 * m + 6⟩ := by
  rw [show (2 * m + 1 : ℕ) = 0 + (2 * m + 1) from by ring,
      show g + 3 = (g + 2) + 1 from by ring]
  apply stepStar_stepPlus_stepPlus (r4_chain (2 * m + 1) 0 0 (2 * m + 2) ((g + 2) + 1))
  rw [show 0 + (2 * m + 1) = (2 * m) + 1 from by ring]
  step fm
  rw [show (2 * m + 2 : ℕ) = (2 * m + 1) + 1 from by ring]
  step fm
  rw [show 2 * m + 2 = 2 * (m + 1) from by ring,
      show 2 * m + 1 = m + (m + 1) from by ring]
  apply stepStar_trans (interleaved_even m (g + 2))
  rw [show 2 + 2 * m = (2 * m + 1) + 1 from by ring]
  step fm
  rw [show (1 : ℕ) = 0 + 1 from by ring]
  step fm
  rw [show 2 * m + 1 + 2 = 0 + (2 * m + 3) from by ring]
  apply stepStar_trans (r3_chain (2 * m + 3) 0 (2 * m + 2) 0 (g + 3))
  ring_nf; finish

-- Odd case
theorem main_odd (m g : ℕ) :
    ⟨0, 0, 0, 2 * m + 2, 2 * m + 3, g + 3⟩ [fm]⊢⁺ ⟨0, 0, 0, 2 * m + 3, 2 * m + 4, g + 2 * m + 7⟩ := by
  rw [show (2 * m + 2 : ℕ) = 0 + (2 * m + 2) from by ring,
      show g + 3 = (g + 2) + 1 from by ring]
  apply stepStar_stepPlus_stepPlus (r4_chain (2 * m + 2) 0 0 (2 * m + 3) ((g + 2) + 1))
  rw [show 0 + (2 * m + 2) = (2 * m + 1) + 1 from by ring]
  step fm
  rw [show (2 * m + 3 : ℕ) = (2 * m + 2) + 1 from by ring]
  step fm
  rw [show 2 * m + 3 = 2 * (m + 1) + 1 from by ring,
      show 2 * m + 2 = m + (m + 1) + 1 from by ring]
  apply stepStar_trans (interleaved_odd m (g + 2))
  rw [show 1 + 2 * (m + 1) = (2 * m + 2) + 1 from by ring]
  step fm
  rw [show (1 : ℕ) = 0 + 1 from by ring]
  step fm
  rw [show 2 * m + 2 + 2 = 0 + (2 * m + 4) from by ring]
  apply stepStar_trans (r3_chain (2 * m + 4) 0 (2 * m + 3) 0 (g + 3))
  ring_nf; finish

theorem main_trans (n g : ℕ) :
    ⟨0, 0, 0, n + 1, n + 2, g + 3⟩ [fm]⊢⁺ ⟨0, 0, 0, n + 2, n + 3, g + n + 6⟩ := by
  rcases Nat.even_or_odd n with ⟨m, hm⟩ | ⟨m, hm⟩
  · rw [show m + m = 2 * m from by ring] at hm; subst hm
    exact main_even m g
  · subst hm
    rw [show 2 * m + 1 + 1 = 2 * m + 2 from by ring,
        show 2 * m + 1 + 2 = 2 * m + 3 from by ring,
        show g + (2 * m + 1) + 6 = g + 2 * m + 7 from by ring,
        show 2 * m + 1 + 3 = 2 * m + 4 from by ring]
    exact main_odd m g

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨0, 0, 0, 1, 2, 3⟩) (by execute fm 8)
  apply progress_nonhalt_simple (fm := fm) (A := ℕ × ℕ)
    (fun ⟨n, g⟩ ↦ ⟨0, 0, 0, n + 1, n + 2, g + 3⟩) ⟨0, 0⟩
  intro ⟨n, g⟩; exact ⟨⟨n + 1, g + n + 3⟩, main_trans n g⟩

end Sz22_2003_unofficial_723
