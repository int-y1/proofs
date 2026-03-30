import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #1013: [4/15, 9/154, 35/2, 11/5, 15/7]

Vector representation:
```
 2 -1 -1  0  0
-1  2  0 -1 -1
-1  0  1  1  0
 0  0 -1  0  1
 0  1  1 -1  0
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_1013

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a, b+1, c+1, d, e⟩ => some ⟨a+2, b, c, d, e⟩
  | ⟨a+1, b, c, d+1, e+1⟩ => some ⟨a, b+2, c, d, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b, c+1, d+1, e⟩
  | ⟨a, b, c+1, d, e⟩ => some ⟨a, b, c, d, e+1⟩
  | ⟨a, b, c, d+1, e⟩ => some ⟨a, b+1, c+1, d, e⟩
  | _ => none

theorem r3_chain : ∀ n, ∀ c d, (⟨n, 0, c, d, 0⟩ : Q) [fm]⊢* ⟨0, 0, c + n, d + n, 0⟩ := by
  intro n; induction n with
  | zero => intro c d; exists 0
  | succ n ih =>
    intro c d
    step fm
    apply stepStar_trans (ih (c + 1) (d + 1))
    ring_nf; finish

theorem r4_chain : ∀ c, ∀ d e, (⟨0, 0, c, d, e⟩ : Q) [fm]⊢* ⟨0, 0, 0, d, e + c⟩ := by
  intro c; induction c with
  | zero => intro d e; exists 0
  | succ c ih =>
    intro d e
    step fm
    apply stepStar_trans (ih d (e + 1))
    ring_nf; finish

theorem r5r1r2r2_loop : ∀ k, ∀ b d e,
    (⟨0, b, 0, d + 3 * k, e + 2 * k⟩ : Q) [fm]⊢* ⟨0, b + 4 * k, 0, d, e⟩ := by
  intro k; induction k with
  | zero => intro b d e; ring_nf; finish
  | succ k ih =>
    intro b d e
    rw [show d + 3 * (k + 1) = (d + 3 * k) + 3 from by ring,
        show e + 2 * (k + 1) = (e + 2 * k) + 2 from by ring]
    step fm; step fm; step fm; step fm
    apply stepStar_trans (ih (b + 4) d e)
    ring_nf; finish

theorem partial_round : ∀ b d, (⟨0, b, 0, d + 2, 1⟩ : Q) [fm]⊢* ⟨1, b + 2, 0, d, 0⟩ := by
  intro b d
  step fm; step fm; step fm; finish

theorem r3r1_drain : ∀ b, ∀ a d,
    (⟨a + 1, b, 0, d, 0⟩ : Q) [fm]⊢* ⟨a + 1 + b, 0, 0, d + b, 0⟩ := by
  intro b; induction b with
  | zero => intro a d; ring_nf; finish
  | succ b ih =>
    intro a d
    step fm; step fm
    apply stepStar_trans (ih (a + 1) (d + 1))
    ring_nf; finish

theorem main_trans (k : ℕ) (d : ℕ) (hd : d ≥ k + 1) :
    (⟨2 * k + 1, 0, 0, d, 0⟩ : Q) [fm]⊢⁺ ⟨4 * k + 3, 0, 0, d + 3 * k + 1, 0⟩ := by
  have h1 : (⟨2 * k + 1, 0, 0, d, 0⟩ : Q) [fm]⊢⁺ ⟨0, 0, 2 * k + 1, d + 2 * k + 1, 0⟩ := by
    step fm
    apply stepStar_trans (r3_chain (2 * k) 1 (d + 1))
    ring_nf; finish
  have h2 : (⟨0, 0, 2 * k + 1, d + 2 * k + 1, 0⟩ : Q) [fm]⊢*
      ⟨0, 0, 0, d + 2 * k + 1, 2 * k + 1⟩ := by
    have := r4_chain (2 * k + 1) (d + 2 * k + 1) 0
    rw [show (0 : ℕ) + (2 * k + 1) = 2 * k + 1 from by ring] at this; exact this
  have h3 : (⟨0, 0, 0, d + 2 * k + 1, 2 * k + 1⟩ : Q) [fm]⊢*
      ⟨0, 4 * k, 0, d - k + 1, 1⟩ := by
    rw [show d + 2 * k + 1 = (d - k + 1) + 3 * k from by omega,
        show 2 * k + 1 = 1 + 2 * k from by ring]
    have := r5r1r2r2_loop k 0 (d - k + 1) 1
    rw [show (0 : ℕ) + 4 * k = 4 * k from by ring] at this; exact this
  have h4 : (⟨0, 4 * k, 0, d - k + 1, 1⟩ : Q) [fm]⊢* ⟨1, 4 * k + 2, 0, d - k - 1, 0⟩ := by
    rw [show d - k + 1 = (d - k - 1) + 2 from by omega]
    exact partial_round (4 * k) (d - k - 1)
  have h5 : (⟨1, 4 * k + 2, 0, d - k - 1, 0⟩ : Q) [fm]⊢*
      ⟨4 * k + 3, 0, 0, d + 3 * k + 1, 0⟩ := by
    rw [show (1 : ℕ) = 0 + 1 from by ring]
    have := r3r1_drain (4 * k + 2) 0 (d - k - 1)
    rw [show 0 + 1 + (4 * k + 2) = 4 * k + 3 from by ring,
        show d - k - 1 + (4 * k + 2) = d + 3 * k + 1 from by omega] at this; exact this
  exact stepPlus_stepStar_stepPlus h1
    (stepStar_trans h2 (stepStar_trans h3 (stepStar_trans h4 h5)))

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨7, 0, 0, 5, 0⟩) (by execute fm 34)
  apply progress_nonhalt (fm := fm)
    (P := fun q ↦ ∃ k d, q = ⟨2 * k + 1, 0, 0, d, 0⟩ ∧ d ≥ k + 1)
  · intro q ⟨k, d, hq, hd⟩
    exact ⟨⟨4 * k + 3, 0, 0, d + 3 * k + 1, 0⟩,
      ⟨2 * k + 1, d + 3 * k + 1, by ring_nf, by omega⟩,
      hq ▸ main_trans k d hd⟩
  · exact ⟨3, 5, rfl, by omega⟩

end Sz22_2003_unofficial_1013
