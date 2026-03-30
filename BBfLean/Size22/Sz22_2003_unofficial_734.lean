import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #734: [35/6, 4/55, 143/2, 3/7, 6/13]

Vector representation:
```
-1 -1  1  1  0  0
 2  0 -1  0 -1  0
-1  0  0  0  1  1
 0  1  0 -1  0  0
 1  1  0  0  0 -1
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_734

def Q := ℕ × ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a+1, b+1, c, d, e, f⟩ => some ⟨a, b, c+1, d+1, e, f⟩
  | ⟨a, b, c+1, d, e+1, f⟩ => some ⟨a+2, b, c, d, e, f⟩
  | ⟨a+1, b, c, d, e, f⟩ => some ⟨a, b, c, d, e+1, f+1⟩
  | ⟨a, b, c, d+1, e, f⟩ => some ⟨a, b+1, c, d, e, f⟩
  | ⟨a, b, c, d, e, f+1⟩ => some ⟨a+1, b+1, c, d, e, f⟩
  | _ => none

theorem r3_chain : ∀ k, ∀ d e f, ⟨a + k, 0, 0, d, e, f⟩ [fm]⊢* ⟨a, 0, 0, d, e + k, f + k⟩ := by
  intro k; induction' k with k ih <;> intro d e f
  · exists 0
  · rw [show a + (k + 1) = (a + k) + 1 from by ring]
    step fm
    apply stepStar_trans (ih d (e + 1) (f + 1))
    ring_nf; finish

theorem r4_chain : ∀ k, ∀ b e f, ⟨0, b, 0, d + k, e, f⟩ [fm]⊢* ⟨0, b + k, 0, d, e, f⟩ := by
  intro k; induction' k with k ih <;> intro b e f
  · exists 0
  · rw [show d + (k + 1) = (d + k) + 1 from by ring]
    step fm
    apply stepStar_trans (ih (b + 1) e f)
    ring_nf; finish

theorem r2_chain : ∀ k, ∀ a d f, ⟨a, 0, c + k, d, e + k, f⟩ [fm]⊢* ⟨a + 2 * k, 0, c, d, e, f⟩ := by
  intro k; induction' k with k ih <;> intro a d f
  · exists 0
  · rw [show c + (k + 1) = (c + k) + 1 from by ring,
        show e + (k + 1) = (e + k) + 1 from by ring]
    step fm
    apply stepStar_trans (ih (a + 2) d f)
    ring_nf; finish

theorem r1r1r2_chain : ∀ k, ∀ c d e f,
    ⟨2, b + 2 * k, c, d, e + k, f⟩ [fm]⊢* ⟨2, b, c + k, d + 2 * k, e, f⟩ := by
  intro k; induction' k with k ih <;> intro c d e f
  · exists 0
  · rw [show b + 2 * (k + 1) = (b + 2 * k + 1) + 1 from by ring,
        show e + (k + 1) = (e + k) + 1 from by ring]
    step fm
    rw [show b + 2 * k + 1 = (b + 2 * k) + 1 from by ring]
    step fm; step fm
    apply stepStar_trans (ih (c + 1) (d + 2) e f)
    ring_nf; finish

theorem mid_even (m f : ℕ) :
    ⟨2, 2 * m, 0, 1, 2 * m, f⟩ [fm]⊢* ⟨2 * m + 2, 0, 0, 2 * m + 1, 0, f⟩ := by
  have h1 := r1r1r2_chain (b := 0) m 0 1 m f
  have h2 := r2_chain (c := 0) (e := 0) m 2 (2 * m + 1) f
  have goal1 : (2, 0 + 2 * m, 0, 1, m + m, f) [fm]⊢* ⟨2 * m + 2, 0, 0, 2 * m + 1, 0, f⟩ := by
    apply stepStar_trans h1
    convert h2 using 3
    all_goals ring_nf
  convert goal1 using 3
  all_goals ring_nf

theorem mid_odd (m f : ℕ) :
    ⟨2, 2 * m + 1, 0, 1, 2 * m + 1, f⟩ [fm]⊢* ⟨2 * m + 3, 0, 0, 2 * m + 2, 0, f⟩ := by
  have h1 := r1r1r2_chain (b := 1) m 0 1 (m + 1) f
  have goal1 : (2, 1 + 2 * m, 0, 1, m + 1 + m, f) [fm]⊢* ⟨2 * m + 3, 0, 0, 2 * m + 2, 0, f⟩ := by
    apply stepStar_trans h1
    rw [show 1 + 2 * m = (2 * m) + 1 from by ring]
    step fm
    have h2 := r2_chain (c := 0) (e := 0) (m + 1) 1 (2 * m + 2) f
    convert h2 using 3
    all_goals ring_nf
  convert goal1 using 3
  all_goals ring_nf

theorem main_trans (n f : ℕ) :
    ⟨n + 2, 0, 0, n + 1, 0, f⟩ [fm]⊢⁺ ⟨n + 3, 0, 0, n + 2, 0, f + n + 1⟩ := by
  rw [show n + 2 = 0 + (n + 2) from by ring]
  apply step_stepStar_stepPlus
  · show fm ⟨0 + ((n + 1) + 1), 0, 0, n + 1, 0, f⟩ = some ⟨0 + (n + 1), 0, 0, n + 1, 0 + 1, f + 1⟩
    simp [fm]
  have h1 := r3_chain (a := 0) (n + 1) (n + 1) 1 (f + 1)
  have h2 := r4_chain (d := 0) (n + 1) 0 (n + 2) (f + n + 2)
  have phase12 : (0 + (n + 1), 0, 0, n + 1, 1, f + 1) [fm]⊢* ⟨0, n + 1, 0, 0, n + 2, f + n + 2⟩ := by
    apply stepStar_trans h1
    convert h2 using 3
    all_goals ring_nf
  apply stepStar_trans
  · convert phase12 using 3
  rw [show f + n + 2 = (f + n + 1) + 1 from by ring]
  step fm
  rw [show n + 1 + 1 = n + 2 from by ring]
  step fm; step fm
  rcases Nat.even_or_odd (n + 1) with ⟨m, hm⟩ | ⟨m, hm⟩
  · rw [show m + m = 2 * m from by ring] at hm
    have key := mid_even m (f + n + 1)
    rw [show n + 1 = 2 * m from hm]
    rw [show n + 2 = 2 * m + 1 from by omega,
        show n + 3 = 2 * m + 2 from by omega]
    convert key using 3
    all_goals ring_nf
  · have key := mid_odd m (f + n + 1)
    rw [show n + 1 = 2 * m + 1 from hm]
    rw [show n + 2 = 2 * m + 2 from by omega,
        show n + 3 = 2 * m + 3 from by omega]
    convert key using 3
    all_goals ring_nf

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨2, 0, 0, 1, 0, 0⟩) (by execute fm 4)
  apply progress_nonhalt (fm := fm)
    (P := fun q ↦ ∃ n f, q = ⟨n + 2, 0, 0, n + 1, 0, f⟩)
  · intro c ⟨n, f, hq⟩; subst hq
    exact ⟨⟨n + 3, 0, 0, n + 2, 0, f + n + 1⟩, ⟨n + 1, f + n + 1, by ring_nf⟩, main_trans n f⟩
  · exact ⟨0, 0, rfl⟩

end Sz22_2003_unofficial_734
