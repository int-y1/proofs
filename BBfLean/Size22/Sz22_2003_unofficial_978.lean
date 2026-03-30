import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #978: [4/15, 33/14, 65/2, 7/11, 154/13]

Vector representation:
```
 2 -1 -1  0  0  0
-1  1  0 -1  1  0
-1  0  1  0  0  1
 0  0  0  1 -1  0
 1  0  0  1  1 -1
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_978

def Q := ℕ × ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a, b+1, c+1, d, e, f⟩ => some ⟨a+2, b, c, d, e, f⟩
  | ⟨a+1, b, c, d+1, e, f⟩ => some ⟨a, b+1, c, d, e+1, f⟩
  | ⟨a+1, b, c, d, e, f⟩ => some ⟨a, b, c+1, d, e, f+1⟩
  | ⟨a, b, c, d, e+1, f⟩ => some ⟨a, b, c, d+1, e, f⟩
  | ⟨a, b, c, d, e, f+1⟩ => some ⟨a+1, b, c, d+1, e+1, f⟩
  | _ => none

theorem r3_drain : ∀ k, ∀ c e f,
    ⟨k, 0, c, 0, e, f⟩ [fm]⊢* ⟨0, 0, c + k, 0, e, f + k⟩ := by
  intro k; induction' k with k ih <;> intro c e f
  · ring_nf; finish
  · step fm; apply stepStar_trans (ih (c + 1) e (f + 1)); ring_nf; finish

theorem r4_drain : ∀ k, ∀ c d f,
    ⟨0, 0, c, d, k, f⟩ [fm]⊢* ⟨0, 0, c, d + k, 0, f⟩ := by
  intro k; induction' k with k ih <;> intro c d f
  · ring_nf; finish
  · rw [show (k : ℕ) + 1 = k + 1 from rfl]
    step fm; apply stepStar_trans (ih c (d + 1) f); ring_nf; finish

theorem r2r1_chain : ∀ k, ∀ a c d e f,
    ⟨a + 1, 0, c + k, d + k, e, f⟩ [fm]⊢* ⟨a + 1 + k, 0, c, d, e + k, f⟩ := by
  intro k; induction' k with k ih <;> intro a c d e f
  · ring_nf; finish
  · rw [show c + (k + 1) = (c + k) + 1 from by ring,
        show d + (k + 1) = (d + k) + 1 from by ring]
    step fm; step fm
    apply stepStar_trans (ih (a + 1) c d (e + 1) f); ring_nf; finish

theorem r2_drain : ∀ k, ∀ a b e f,
    ⟨a + k, b, 0, k, e, f⟩ [fm]⊢* ⟨a, b + k, 0, 0, e + k, f⟩ := by
  intro k; induction' k with k ih <;> intro a b e f
  · ring_nf; finish
  · rw [show a + (k + 1) = (a + k) + 1 from by ring,
        show (k : ℕ) + 1 = k + 1 from rfl]
    step fm; apply stepStar_trans (ih a (b + 1) (e + 1) f); ring_nf; finish

theorem r3r1_chain : ∀ k, ∀ a e f,
    ⟨a + 1, k, 0, 0, e, f⟩ [fm]⊢* ⟨a + 1 + k, 0, 0, 0, e, f + k⟩ := by
  intro k; induction' k with k ih <;> intro a e f
  · ring_nf; finish
  · rw [show (k : ℕ) + 1 = k + 1 from rfl]
    step fm; step fm
    apply stepStar_trans (ih (a + 1) e (f + 1)); ring_nf; finish

theorem main_trans (n f : ℕ) :
    ⟨n + 1, 0, 0, 0, 2 * n, f⟩ [fm]⊢⁺
    ⟨n + 2, 0, 0, 0, 2 * n + 2, f + 2 * n⟩ := by
  have h1 : ⟨n + 1, 0, 0, 0, 2 * n, f⟩ [fm]⊢*
      ⟨0, 0, n + 1, 0, 2 * n, f + n + 1⟩ := by
    have := r3_drain (n + 1) 0 (2 * n) f
    rw [show 0 + (n + 1) = n + 1 from by ring,
        show f + (n + 1) = f + n + 1 from by ring] at this
    exact this
  have h2 : ⟨0, 0, n + 1, 0, 2 * n, f + n + 1⟩ [fm]⊢*
      ⟨0, 0, n + 1, 2 * n, 0, f + n + 1⟩ := by
    have := r4_drain (2 * n) (n + 1) 0 (f + n + 1)
    rw [show 0 + 2 * n = 2 * n from by ring] at this
    exact this
  have h3 : ⟨0, 0, n + 1, 2 * n, 0, f + n + 1⟩ [fm]⊢⁺
      ⟨1, 0, n + 1, 2 * n + 1, 1, f + n⟩ := by
    rw [show f + n + 1 = (f + n) + 1 from by ring]
    apply step_stepPlus
    show fm ⟨0, 0, n + 1, 2 * n, 0, (f + n) + 1⟩ =
      some ⟨1, 0, n + 1, 2 * n + 1, 1, f + n⟩
    unfold fm; simp only
  have h4 : ⟨1, 0, n + 1, 2 * n + 1, 1, f + n⟩ [fm]⊢*
      ⟨n + 2, 0, 0, n, n + 2, f + n⟩ := by
    have := r2r1_chain (n + 1) 0 0 n 1 (f + n)
    simp only [Nat.zero_add] at this
    rw [show n + (n + 1) = 2 * n + 1 from by ring,
        show 1 + (n + 1) = n + 2 from by ring] at this
    exact this
  have h5 : ⟨n + 2, 0, 0, n, n + 2, f + n⟩ [fm]⊢*
      ⟨2, n, 0, 0, 2 * n + 2, f + n⟩ := by
    have := r2_drain n 2 0 (n + 2) (f + n)
    rw [show 2 + n = n + 2 from by ring,
        show 0 + n = n from by ring,
        show n + 2 + n = 2 * n + 2 from by ring] at this
    exact this
  have h6 : ⟨2, n, 0, 0, 2 * n + 2, f + n⟩ [fm]⊢*
      ⟨n + 2, 0, 0, 0, 2 * n + 2, f + 2 * n⟩ := by
    have := r3r1_chain n 1 (2 * n + 2) (f + n)
    rw [show 1 + 1 = 2 from by ring,
        show 1 + 1 + n = n + 2 from by ring,
        show f + n + n = f + 2 * n from by ring] at this
    exact this
  exact stepStar_stepPlus_stepPlus h1
    (stepPlus_stepStar_stepPlus
      (stepStar_stepPlus_stepPlus h2 h3)
      (stepStar_trans h4 (stepStar_trans h5 h6)))

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨2, 0, 0, 0, 2, 0⟩) (by execute fm 4)
  apply progress_nonhalt_simple (fm := fm) (A := ℕ × ℕ)
    (fun ⟨n, f⟩ ↦ ⟨n + 1, 0, 0, 0, 2 * n, f⟩) ⟨1, 0⟩
  intro ⟨n, f⟩
  refine ⟨⟨n + 1, f + 2 * n⟩, ?_⟩
  show ⟨n + 1, 0, 0, 0, 2 * n, f⟩ [fm]⊢⁺
    ⟨(n + 1) + 1, 0, 0, 0, 2 * (n + 1), f + 2 * n⟩
  rw [show (n + 1) + 1 = n + 2 from by ring,
      show 2 * (n + 1) = 2 * n + 2 from by ring]
  exact main_trans n f
