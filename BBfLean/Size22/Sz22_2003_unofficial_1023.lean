import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #1023: [4/15, 99/14, 5/2, 7/11, 44/5]

Vector representation:
```
 2 -1 -1  0  0
-1  2  0 -1  1
-1  0  1  0  0
 0  0  0  1 -1
 2  0 -1  0  1
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_1023

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a, b+1, c+1, d, e⟩ => some ⟨a+2, b, c, d, e⟩
  | ⟨a+1, b, c, d+1, e⟩ => some ⟨a, b+2, c, d, e+1⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b, c+1, d, e⟩
  | ⟨a, b, c, d, e+1⟩ => some ⟨a, b, c, d+1, e⟩
  | ⟨a, b, c+1, d, e⟩ => some ⟨a+2, b, c, d, e+1⟩
  | _ => none

theorem r3_drain : ∀ k, ∀ c e,
    ⟨k, (0 : ℕ), c, 0, e⟩ [fm]⊢* ⟨0, 0, c + k, 0, e⟩ := by
  intro k; induction k with
  | zero => intro c e; exists 0
  | succ k ih =>
    intro c e
    rw [show c + (k + 1) = (c + 1) + k from by ring]
    step fm
    apply stepStar_trans (ih (c + 1) e)
    ring_nf; finish

theorem r4_drain : ∀ k, ∀ c d,
    ⟨(0 : ℕ), 0, c, d, k⟩ [fm]⊢* ⟨0, 0, c, d + k, 0⟩ := by
  intro k; induction k with
  | zero => intro c d; exists 0
  | succ k ih =>
    intro c d
    rw [show d + (k + 1) = (d + 1) + k from by ring]
    step fm
    apply stepStar_trans (ih c (d + 1))
    ring_nf; finish

theorem r2r1r1_chain : ∀ k, ∀ A c d e,
    ⟨A + 2, (0 : ℕ), c + 2 * k, d + k, e⟩ [fm]⊢* ⟨A + 3 * k + 2, 0, c, d, e + k⟩ := by
  intro k; induction k with
  | zero => intro A c d e; ring_nf; finish
  | succ k ih =>
    intro A c d e
    rw [show c + 2 * (k + 1) = (c + 2 * k) + 2 from by ring,
        show d + (k + 1) = (d + k) + 1 from by ring,
        show A + 3 * (k + 1) + 2 = (A + 3) + 3 * k + 2 from by ring,
        show e + (k + 1) = (e + 1) + k from by ring]
    step fm; step fm; step fm
    apply stepStar_trans (ih (A + 3) c d (e + 1))
    ring_nf; finish

theorem main_trans_simple (c e : ℕ) (he : e ≥ 1) (hc : c ≥ 2 * e + 1) :
    ⟨(0 : ℕ), 0, c, 0, e⟩ [fm]⊢⁺ ⟨0, 0, c + e + 1, 0, e + 1⟩ := by
  have h1 : ⟨(0 : ℕ), 0, c, 0, e⟩ [fm]⊢* ⟨0, 0, c, e, 0⟩ := by
    have := r4_drain e c 0
    rw [show (0 : ℕ) + e = e from by ring] at this; exact this
  have h2 : ⟨(0 : ℕ), 0, c, e, 0⟩ [fm]⊢⁺ ⟨2, 0, c - 1, e, 1⟩ := by
    rw [show c = (c - 1) + 1 from by omega]
    step fm; finish
  have h3 : ⟨(2 : ℕ), 0, c - 1, e, 1⟩ [fm]⊢* ⟨3 * e + 2, 0, c - 1 - 2 * e, 0, e + 1⟩ := by
    have := r2r1r1_chain e 0 (c - 1 - 2 * e) 0 1
    rw [show (0 : ℕ) + 2 = 2 from by ring,
        show (c - 1 - 2 * e) + 2 * e = c - 1 from by omega,
        show (0 : ℕ) + e = e from by ring,
        show 0 + 3 * e + 2 = 3 * e + 2 from by ring,
        show (1 : ℕ) + e = e + 1 from by ring] at this; exact this
  have h4 : ⟨3 * e + 2, (0 : ℕ), c - 1 - 2 * e, 0, e + 1⟩ [fm]⊢*
      ⟨0, 0, c + e + 1, 0, e + 1⟩ := by
    have := r3_drain (3 * e + 2) (c - 1 - 2 * e) (e + 1)
    rw [show (c - 1 - 2 * e) + (3 * e + 2) = c + e + 1 from by omega] at this; exact this
  exact stepStar_stepPlus_stepPlus h1
    (stepPlus_stepStar_stepPlus h2 (stepStar_trans h3 h4))

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨0, 0, 7, 0, 3⟩) (by execute fm 31)
  apply progress_nonhalt (fm := fm)
    (P := fun q ↦ ∃ c e, q = ⟨0, 0, c, 0, e⟩ ∧ c ≥ 2 * e + 1 ∧ e ≥ 1)
  · intro q ⟨c, e, hq, hce, he⟩
    subst hq
    refine ⟨⟨0, 0, c + e + 1, 0, e + 1⟩,
      ⟨c + e + 1, e + 1, rfl, by omega, by omega⟩, ?_⟩
    exact main_trans_simple c e he hce
  · exact ⟨7, 3, rfl, by omega, by omega⟩
