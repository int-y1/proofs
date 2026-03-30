import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #724: [35/6, 4/55, 143/2, 3/7, 154/13]

Vector representation:
```
-1 -1  1  1  0  0
 2  0 -1  0 -1  0
-1  0  0  0  1  1
 0  1  0 -1  0  0
 1  0  0  1  1 -1
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_724

def Q := ℕ × ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a+1, b+1, c, d, e, f⟩ => some ⟨a, b, c+1, d+1, e, f⟩
  | ⟨a, b, c+1, d, e+1, f⟩ => some ⟨a+2, b, c, d, e, f⟩
  | ⟨a+1, b, c, d, e, f⟩ => some ⟨a, b, c, d, e+1, f+1⟩
  | ⟨a, b, c, d+1, e, f⟩ => some ⟨a, b+1, c, d, e, f⟩
  | ⟨a, b, c, d, e, f+1⟩ => some ⟨a+1, b, c, d+1, e+1, f⟩
  | _ => none

theorem r3_chain : ∀ k, ∀ a d e f, ⟨a + k, 0, 0, d, e, f⟩ [fm]⊢* ⟨a, 0, 0, d, e + k, f + k⟩ := by
  intro k; induction' k with k ih <;> intro a d e f
  · exists 0
  · rw [show a + (k + 1) = (a + k) + 1 from by ring]
    step fm
    apply stepStar_trans (ih a d (e + 1) (f + 1))
    ring_nf; finish

theorem r4_chain : ∀ k, ∀ b d e f, ⟨0, b, 0, d + k, e, f⟩ [fm]⊢* ⟨0, b + k, 0, d, e, f⟩ := by
  intro k; induction' k with k ih <;> intro b d e f
  · exists 0
  · rw [show d + (k + 1) = (d + k) + 1 from by ring]
    step fm
    apply stepStar_trans (ih (b + 1) d e f)
    ring_nf; finish

theorem r2_chain : ∀ k, ∀ a c d e f, ⟨a, 0, c + k, d, e + k, f⟩ [fm]⊢* ⟨a + 2 * k, 0, c, d, e, f⟩ := by
  intro k; induction' k with k ih <;> intro a c d e f
  · exists 0
  · rw [show c + (k + 1) = (c + k) + 1 from by ring,
        show e + (k + 1) = (e + k) + 1 from by ring]
    step fm
    apply stepStar_trans (ih (a + 2) c d e f)
    ring_nf; finish

theorem r1r1r2_chain : ∀ k, ∀ b c d e f, ⟨2, b + 2 * k, c, d, e + k, f⟩ [fm]⊢* ⟨2, b, c + k, d + 2 * k, e, f⟩ := by
  intro k; induction' k with k ih <;> intro b c d e f
  · exists 0
  · rw [show b + 2 * (k + 1) = (b + 2 * k) + 1 + 1 from by ring,
        show e + (k + 1) = (e + k) + 1 from by ring]
    step fm; step fm; step fm
    apply stepStar_trans (ih b (c + 1) (d + 2) e f)
    ring_nf; finish

theorem interleave_even (k f : ℕ) :
    ⟨1, 2 * k + 1, 0, 1, 4 * k + 4, f⟩ [fm]⊢* ⟨2 * k + 2, 0, 0, 2 * k + 2, 2 * k + 3, f⟩ := by
  rw [show 2 * k + 1 = (0 + 2 * k) + 1 from by ring,
      show 4 * k + 4 = (3 * k + 3 + k) + 1 from by ring]
  step fm; step fm
  apply stepStar_trans (r1r1r2_chain k 0 0 2 (3 * k + 3) f)
  rw [show 2 + 2 * k = 2 * k + 2 from by ring]
  have h := r2_chain k 2 0 (2 * k + 2) (2 * k + 3) f
  rw [show 2 + 2 * k = 2 * k + 2 from by ring] at h
  convert h using 2; ring_nf

theorem interleave_odd (k f : ℕ) :
    ⟨1, 2 * k + 2, 0, 1, 4 * k + 6, f⟩ [fm]⊢* ⟨2 * k + 3, 0, 0, 2 * k + 3, 2 * k + 4, f⟩ := by
  rw [show 2 * k + 2 = (1 + 2 * k) + 1 from by ring,
      show 4 * k + 6 = (3 * k + 5 + k) + 1 from by ring]
  step fm; step fm
  apply stepStar_trans (r1r1r2_chain k 1 0 2 (3 * k + 5) f)
  rw [show 2 + 2 * k = 2 * k + 2 from by ring]
  step fm
  have h := r2_chain (k + 1) 1 0 (2 * k + 3) (2 * k + 4) f
  rw [show 1 + 2 * (k + 1) = 2 * k + 3 from by ring] at h
  convert h using 2; ring_nf

theorem main_even (k f : ℕ) :
    ⟨2 * k + 2, 0, 0, 2 * k + 2, 2 * k + 3, f⟩ [fm]⊢⁺ ⟨2 * k + 3, 0, 0, 2 * k + 3, 2 * k + 4, f + 2 * k + 1⟩ := by
  have h1 := r3_chain (2 * k + 2) 0 (2 * k + 2) (2 * k + 3) f
  rw [show 0 + (2 * k + 2) = 2 * k + 2 from by ring] at h1
  apply stepStar_stepPlus_stepPlus h1
  rw [show 2 * k + 3 + (2 * k + 2) = 4 * k + 5 from by ring,
      show f + (2 * k + 2) = f + 2 * k + 2 from by ring]
  have h2 := r4_chain (2 * k + 2) 0 0 (4 * k + 5) (f + 2 * k + 2)
  rw [show 0 + (2 * k + 2) = 2 * k + 2 from by ring] at h2
  apply stepStar_stepPlus_stepPlus h2
  rw [show f + 2 * k + 2 = (f + 2 * k + 1) + 1 from by ring]
  apply step_stepStar_stepPlus
  · show fm ⟨0, 2 * k + 2, 0, 0, 4 * k + 5, (f + 2 * k + 1) + 1⟩ = some ⟨1, 2 * k + 2, 0, 1, 4 * k + 6, f + 2 * k + 1⟩
    simp [fm]
  exact interleave_odd k (f + 2 * k + 1)

theorem main_odd (k f : ℕ) :
    ⟨2 * k + 3, 0, 0, 2 * k + 3, 2 * k + 4, f⟩ [fm]⊢⁺ ⟨2 * k + 4, 0, 0, 2 * k + 4, 2 * k + 5, f + 2 * k + 2⟩ := by
  have h1 := r3_chain (2 * k + 3) 0 (2 * k + 3) (2 * k + 4) f
  rw [show 0 + (2 * k + 3) = 2 * k + 3 from by ring] at h1
  apply stepStar_stepPlus_stepPlus h1
  rw [show 2 * k + 4 + (2 * k + 3) = 4 * k + 7 from by ring,
      show f + (2 * k + 3) = f + 2 * k + 3 from by ring]
  have h2 := r4_chain (2 * k + 3) 0 0 (4 * k + 7) (f + 2 * k + 3)
  rw [show 0 + (2 * k + 3) = 2 * k + 3 from by ring] at h2
  apply stepStar_stepPlus_stepPlus h2
  rw [show f + 2 * k + 3 = (f + 2 * k + 2) + 1 from by ring]
  apply step_stepStar_stepPlus
  · show fm ⟨0, 2 * k + 3, 0, 0, 4 * k + 7, (f + 2 * k + 2) + 1⟩ = some ⟨1, 2 * k + 3, 0, 1, 4 * k + 8, f + 2 * k + 2⟩
    simp [fm]
  rw [show 2 * k + 3 = 2 * (k + 1) + 1 from by ring,
      show 4 * k + 8 = 4 * (k + 1) + 4 from by ring]
  exact interleave_even (k + 1) (f + 2 * k + 2)

theorem main_trans (n f : ℕ) :
    ⟨n + 2, 0, 0, n + 2, n + 3, f⟩ [fm]⊢⁺ ⟨n + 3, 0, 0, n + 3, n + 4, f + n + 1⟩ := by
  rcases Nat.even_or_odd n with ⟨k, hk⟩ | ⟨k, hk⟩
  · rw [show k + k = 2 * k from by ring] at hk; subst hk
    exact main_even k f
  · subst hk
    exact main_odd k f

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨2, 0, 0, 2, 3, 0⟩) (by execute fm 7)
  apply progress_nonhalt_simple (fm := fm) (A := ℕ × ℕ)
    (fun ⟨n, f⟩ ↦ ⟨n + 2, 0, 0, n + 2, n + 3, f⟩) ⟨0, 0⟩
  intro ⟨n, f⟩; exact ⟨⟨n + 1, f + n + 1⟩, main_trans n f⟩

end Sz22_2003_unofficial_724
