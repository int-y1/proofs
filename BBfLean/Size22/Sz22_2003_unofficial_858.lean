import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #858: [385/6, 4/65, 91/2, 3/11, 15/7]

Vector representation:
```
-1 -1  1  1  1  0
 2  0 -1  0  0 -1
-1  0  0  1  0  1
 0  1  0  0 -1  0
 0  1  1 -1  0  0
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_858

def Q := ℕ × ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a+1, b+1, c, d, e, f⟩ => some ⟨a, b, c+1, d+1, e+1, f⟩
  | ⟨a, b, c+1, d, e, f+1⟩ => some ⟨a+2, b, c, d, e, f⟩
  | ⟨a+1, b, c, d, e, f⟩ => some ⟨a, b, c, d+1, e, f+1⟩
  | ⟨a, b, c, d, e+1, f⟩ => some ⟨a, b+1, c, d, e, f⟩
  | ⟨a, b, c, d+1, e, f⟩ => some ⟨a, b+1, c+1, d, e, f⟩
  | _ => none

theorem r3_chain : ∀ k, ∀ a d e f, ⟨a + k, 0, 0, d, e, f⟩ [fm]⊢* ⟨a, 0, 0, d + k, e, f + k⟩ := by
  intro k; induction' k with k ih <;> intro a d e f
  · exists 0
  · rw [show a + (k + 1) = (a + k) + 1 from by ring]; step fm
    apply stepStar_trans (ih a (d + 1) e (f + 1)); ring_nf; finish

theorem r4_chain : ∀ k, ∀ b d e f, ⟨0, b, 0, d, e + k, f⟩ [fm]⊢* ⟨0, b + k, 0, d, e, f⟩ := by
  intro k; induction' k with k ih <;> intro b d e f
  · exists 0
  · rw [show e + (k + 1) = (e + k) + 1 from by ring]; step fm
    apply stepStar_trans (ih (b + 1) d e f); ring_nf; finish

theorem r2_chain : ∀ k, ∀ a c d e f, ⟨a, 0, c + k, d, e, f + k⟩ [fm]⊢* ⟨a + 2 * k, 0, c, d, e, f⟩ := by
  intro k; induction' k with k ih <;> intro a c d e f
  · exists 0
  · rw [show c + (k + 1) = (c + k) + 1 from by ring,
        show f + (k + 1) = (f + k) + 1 from by ring]; step fm
    apply stepStar_trans (ih (a + 2) c d e f); ring_nf; finish

theorem r1r1r2_chain : ∀ k, ∀ b c d e f, ⟨2, b + 2 * k, c, d, e, f + k⟩ [fm]⊢* ⟨2, b, c + k, d + 2 * k, e + 2 * k, f⟩ := by
  intro k; induction' k with k ih <;> intro b c d e f
  · exists 0
  · rw [show b + 2 * (k + 1) = (b + 2 * k) + 2 from by ring,
        show f + (k + 1) = (f + k) + 1 from by ring]
    step fm; step fm; step fm
    apply stepStar_trans (ih b (c + 1) (d + 2) (e + 2) f); ring_nf; finish

theorem phases123 (N D E : ℕ) :
    ⟨N + 1, 0, 0, D, E, 0⟩ [fm]⊢⁺ ⟨2, E + 1, 0, D + N, 0, N⟩ := by
  step fm
  apply stepStar_trans (c₂ := ⟨0, 0, 0, D + 1 + N, E, 1 + N⟩)
  · convert r3_chain N 0 (D + 1) E 1 using 2; ring_nf
  apply stepStar_trans (c₂ := ⟨0, 0 + E, 0, D + 1 + N, 0, 1 + N⟩)
  · convert r4_chain E 0 (D + 1 + N) 0 (1 + N) using 2; ring_nf
  rw [show 0 + E = E from by ring,
      show D + 1 + N = (D + N) + 1 from by ring,
      show 1 + N = N + 1 from by ring]
  step fm; step fm; finish

theorem main_even (m : ℕ) :
    ⟨2 * m + 2, 0, 0, (2 * m + 1) * (2 * m + 2), 2 * m + 1, 0⟩ [fm]⊢⁺
    ⟨2 * m + 3, 0, 0, (2 * m + 2) * (2 * m + 3), 2 * m + 2, 0⟩ := by
  rw [show 2 * m + 2 = (2 * m + 1) + 1 from by ring]
  apply stepPlus_stepStar_stepPlus
    (phases123 (2 * m + 1) ((2 * m + 1) * (2 * m + 2)) (2 * m + 1))
  apply stepStar_trans (c₂ := ⟨2, 0, m + 1,
    (2 * m + 1) * (2 * m + 2) + (2 * m + 1) + 2 * (m + 1), 2 * (m + 1), m⟩)
  · convert r1r1r2_chain (m + 1) 0 0
      ((2 * m + 1) * (2 * m + 2) + (2 * m + 1)) 0 m using 2; ring_nf
  apply stepStar_trans (c₂ := ⟨2 + 2 * m, 0, 1,
    (2 * m + 1) * (2 * m + 2) + (2 * m + 1) + 2 * (m + 1), 2 * (m + 1), 0⟩)
  · convert r2_chain m 2 1
      ((2 * m + 1) * (2 * m + 2) + (2 * m + 1) + 2 * (m + 1)) (2 * (m + 1)) 0
      using 2; ring_nf
  rw [show 2 + 2 * m = (2 * m + 1) + 1 from by omega]
  step fm; step fm
  have : (⟨2 * m + 1 + 2, 0, 0,
    (2 * m + 1) * (2 * m + 2) + (2 * m + 1) + 2 * (m + 1) + 1,
    2 * (m + 1), 0⟩ : Q) =
    ⟨2 * m + 3, 0, 0, (2 * m + 1 + 1) * (2 * m + 3), 2 * m + 1 + 1, 0⟩ := by
    ext <;> simp <;> ring
  rw [this]; finish

theorem main_odd (m : ℕ) :
    ⟨2 * m + 3, 0, 0, (2 * m + 2) * (2 * m + 3), 2 * m + 2, 0⟩ [fm]⊢⁺
    ⟨2 * m + 4, 0, 0, (2 * m + 3) * (2 * m + 4), 2 * m + 3, 0⟩ := by
  rw [show 2 * m + 3 = (2 * m + 2) + 1 from by ring]
  apply stepPlus_stepStar_stepPlus
    (phases123 (2 * m + 2) ((2 * m + 2) * (2 * m + 3)) (2 * m + 2))
  apply stepStar_trans (c₂ := ⟨2, 1, m + 1,
    (2 * m + 2) * (2 * m + 3) + (2 * m + 2) + 2 * (m + 1), 2 * (m + 1), m + 1⟩)
  · convert r1r1r2_chain (m + 1) 1 0
      ((2 * m + 2) * (2 * m + 3) + (2 * m + 2)) 0 (m + 1) using 2; ring_nf
  apply stepStar_trans (c₂ := ⟨1, 0, m + 2,
    (2 * m + 2) * (2 * m + 3) + (2 * m + 2) + 2 * (m + 1) + 1,
    2 * (m + 1) + 1, m + 1⟩)
  · step fm; ring_nf; finish
  apply stepStar_trans (c₂ := ⟨1 + 2 * (m + 1), 0, 1,
    (2 * m + 2) * (2 * m + 3) + (2 * m + 2) + 2 * (m + 1) + 1,
    2 * (m + 1) + 1, 0⟩)
  · convert r2_chain (m + 1) 1 1
      ((2 * m + 2) * (2 * m + 3) + (2 * m + 2) + 2 * (m + 1) + 1)
      (2 * (m + 1) + 1) 0 using 2; ring_nf
  rw [show 1 + 2 * (m + 1) = (2 * m + 2) + 1 from by omega]
  step fm; step fm
  have : (⟨2 * m + 2 + 2, 0, 0,
    (2 * m + 2) * (2 * m + 3) + (2 * m + 2) + 2 * (m + 1) + 1 + 1,
    2 * (m + 1) + 1, 0⟩ : Q) =
    ⟨2 * m + 4, 0, 0, (2 * m + 2 + 1) * (2 * m + 4), 2 * m + 2 + 1, 0⟩ := by
    ext <;> simp <;> ring
  rw [this]; finish

theorem main_transition (n : ℕ) :
    ⟨n + 2, 0, 0, (n + 1) * (n + 2), n + 1, 0⟩ [fm]⊢⁺
    ⟨n + 3, 0, 0, (n + 2) * (n + 3), n + 2, 0⟩ := by
  rcases Nat.even_or_odd n with ⟨m, hm⟩ | ⟨m, hm⟩
  · subst hm; rw [show m + m = 2 * m from by ring]; exact main_even m
  · subst hm; exact main_odd m

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨2, 0, 0, 2, 1, 0⟩)
  · unfold c₀; execute fm 6
  apply progress_nonhalt_simple (fm := fm) (A := ℕ)
    (fun n ↦ ⟨n + 2, 0, 0, (n + 1) * (n + 2), n + 1, 0⟩) 0
  intro n; exists n + 1; exact main_transition n
