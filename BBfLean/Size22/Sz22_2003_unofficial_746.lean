import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #746: [35/6, 4/55, 1859/2, 3/7, 35/13]

Vector representation:
```
-1 -1  1  1  0  0
 2  0 -1  0 -1  0
-1  0  0  0  1  2
 0  1  0 -1  0  0
 0  0  1  1  0 -1
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_746

def Q := ℕ × ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a+1, b+1, c, d, e, f⟩ => some ⟨a, b, c+1, d+1, e, f⟩
  | ⟨a, b, c+1, d, e+1, f⟩ => some ⟨a+2, b, c, d, e, f⟩
  | ⟨a+1, b, c, d, e, f⟩ => some ⟨a, b, c, d, e+1, f+2⟩
  | ⟨a, b, c, d+1, e, f⟩ => some ⟨a, b+1, c, d, e, f⟩
  | ⟨a, b, c, d, e, f+1⟩ => some ⟨a, b, c+1, d+1, e, f⟩
  | _ => none

theorem r3_chain : ∀ k, ∀ a d e f, ⟨a + k, 0, 0, d, e, f⟩ [fm]⊢* ⟨a, 0, 0, d, e + k, f + 2 * k⟩ := by
  intro k; induction' k with k ih <;> intro a d e f
  · exists 0
  · rw [show a + (k + 1) = (a + k) + 1 from by ring]
    step fm
    apply stepStar_trans (ih a d (e + 1) (f + 2))
    ring_nf; finish

theorem r4_chain : ∀ k, ∀ b d e f, ⟨0, b, 0, d + k, e, f⟩ [fm]⊢* ⟨0, b + k, 0, d, e, f⟩ := by
  intro k; induction' k with k ih <;> intro b d e f
  · exists 0
  · rw [show d + (k + 1) = (d + k) + 1 from by ring]
    step fm
    apply stepStar_trans (ih (b + 1) d e f)
    ring_nf; finish

theorem r2r1r1_cycle : ∀ k, ∀ b c d e f, ⟨0, b + 2 * k, c + 1, d, e + k, f⟩ [fm]⊢* ⟨0, b, c + k + 1, d + 2 * k, e, f⟩ := by
  intro k; induction' k with k ih <;> intro b c d e f
  · exists 0
  · rw [show b + 2 * (k + 1) = (b + 2 * k) + 2 from by ring,
        show e + (k + 1) = (e + k) + 1 from by ring]
    step fm; step fm; step fm
    apply stepStar_trans (ih b (c + 1) (d + 2) e f)
    ring_nf; finish

theorem r2_drain : ∀ k, ∀ a c d e f, ⟨a, 0, c + k, d, e + k, f⟩ [fm]⊢* ⟨a + 2 * k, 0, c, d, e, f⟩ := by
  intro k; induction' k with k ih <;> intro a c d e f
  · exists 0
  · rw [show c + (k + 1) = (c + k) + 1 from by ring,
        show e + (k + 1) = (e + k) + 1 from by ring]
    step fm
    apply stepStar_trans (ih (a + 2) c d e f)
    ring_nf; finish

theorem phase12 (n : ℕ) : ⟨n + 1, 0, 0, n, 0, n * n⟩ [fm]⊢⁺ ⟨0, n, 0, 0, n + 1, n * n + 2 * n + 2⟩ := by
  rw [show n + 1 = 0 + (n + 1) from by ring,
      show n * n + 2 * n + 2 = n * n + 2 * (n + 1) from by ring]
  apply step_stepStar_stepPlus
  · show fm ⟨0 + n + 1, 0, 0, n, 0, n * n⟩ = some ⟨0 + n, 0, 0, n, 1, n * n + 2⟩
    simp [fm]
  apply stepStar_trans
  · exact r3_chain n 0 n 1 (n * n + 2)
  convert r4_chain n 0 0 (n + 1) (n * n + 2 * (n + 1)) using 2
  all_goals ring_nf

theorem phase3 (n : ℕ) : ⟨0, n, 0, 0, n + 1, n * n + 2 * n + 2⟩ [fm]⊢* ⟨0, n, 1, 1, n + 1, n * n + 2 * n + 1⟩ := by
  rw [show n * n + 2 * n + 2 = (n * n + 2 * n + 1) + 1 from by ring]
  step fm; finish

theorem phase4_even (m f : ℕ) :
    ⟨0, 2 * m, 1, 1, 2 * m + 1, f⟩ [fm]⊢*
    ⟨2 * m + 2, 0, 0, 2 * m + 1, 0, f⟩ := by
  apply stepStar_trans (c₂ := ⟨0, 0, m + 1, 2 * m + 1, m + 1, f⟩)
  · convert r2r1r1_cycle m 0 0 1 (m + 1) f using 2
    all_goals ring_nf
  · convert r2_drain (m + 1) 0 0 (2 * m + 1) 0 f using 2
    all_goals ring_nf

theorem phase4_odd (m f : ℕ) :
    ⟨0, 2 * m + 1, 1, 1, 2 * m + 2, f⟩ [fm]⊢*
    ⟨2 * m + 3, 0, 0, 2 * m + 2, 0, f⟩ := by
  apply stepStar_trans (c₂ := ⟨0, 1, m + 1, 2 * m + 1, m + 2, f⟩)
  · convert r2r1r1_cycle m 1 0 1 (m + 2) f using 2
    all_goals ring_nf
  apply stepStar_trans (c₂ := ⟨1, 0, m + 1, 2 * m + 2, m + 1, f⟩)
  · step fm; step fm; finish
  · convert r2_drain (m + 1) 1 0 (2 * m + 2) 0 f using 2
    all_goals ring_nf

theorem main_trans (n : ℕ) :
    ⟨n + 1, 0, 0, n, 0, n * n⟩ [fm]⊢⁺ ⟨n + 2, 0, 0, n + 1, 0, (n + 1) * (n + 1)⟩ := by
  apply stepPlus_stepStar_stepPlus (phase12 n)
  apply stepStar_trans (phase3 n)
  rcases Nat.even_or_odd n with ⟨m, hm⟩ | ⟨m, hm⟩
  · rw [show m + m = 2 * m from by ring] at hm; subst hm
    convert phase4_even m (2 * m * (2 * m) + 2 * (2 * m) + 1) using 2
    all_goals ring_nf
  · subst hm
    convert phase4_odd m ((2 * m + 1) * (2 * m + 1) + 2 * (2 * m + 1) + 1) using 2
    all_goals ring_nf

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨1, 0, 0, 0, 0, 0⟩) (by finish)
  apply progress_nonhalt_simple (fm := fm) (A := ℕ)
    (fun n ↦ ⟨n + 1, 0, 0, n, 0, n * n⟩) 0
  intro n; exact ⟨n + 1, main_trans n⟩

end Sz22_2003_unofficial_746
