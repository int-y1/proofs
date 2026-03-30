import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #926: [4/15, 33/14, 25/2, 49/11, 22/5]

Vector representation:
```
 2 -1 -1  0  0
-1  1  0 -1  1
-1  0  2  0  0
 0  0  0  2 -1
 1  0 -1  0  1
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_926

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a, b+1, c+1, d, e⟩ => some ⟨a+2, b, c, d, e⟩
  | ⟨a+1, b, c, d+1, e⟩ => some ⟨a, b+1, c, d, e+1⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b, c+2, d, e⟩
  | ⟨a, b, c, d, e+1⟩ => some ⟨a, b, c, d+2, e⟩
  | ⟨a, b, c+1, d, e⟩ => some ⟨a+1, b, c, d, e+1⟩
  | _ => none

theorem r2r1_chain : ∀ k, ∀ a c d e,
    ⟨a + 1, 0, c + k, d + k, e⟩ [fm]⊢* ⟨a + k + 1, 0, c, d, e + k⟩ := by
  intro k; induction' k with k ih <;> intro a c d e
  · exists 0
  · rw [show c + (k + 1) = (c + k) + 1 from by ring,
        show d + (k + 1) = (d + k) + 1 from by ring]
    step fm; step fm
    have := ih (a + 1) c d (e + 1)
    ring_nf at this ⊢; exact this

theorem r3_drain : ∀ j, ∀ c e,
    ⟨j, 0, c, 0, e⟩ [fm]⊢* ⟨0, 0, c + 2 * j, 0, e⟩ := by
  intro j; induction' j with j ih <;> intro c e
  · exists 0
  · step fm
    have := ih (c + 2) e
    ring_nf at this ⊢; exact this

theorem e_to_d : ∀ k, ∀ c d e,
    ⟨0, 0, c, d, e + k⟩ [fm]⊢* ⟨0, 0, c, d + 2 * k, e⟩ := by
  intro k; induction' k with k ih <;> intro c d e
  · exists 0
  · rw [show e + (k + 1) = (e + k) + 1 from by ring]
    step fm
    have := ih c (d + 2) e
    ring_nf at this ⊢; exact this

theorem r2_drain : ∀ k, ∀ a b e,
    ⟨a + k, b, 0, k, e⟩ [fm]⊢* ⟨a, b + k, 0, 0, e + k⟩ := by
  intro k; induction' k with k ih <;> intro a b e
  · exists 0
  · rw [show a + (k + 1) = (a + k) + 1 from by ring]
    step fm
    have := ih a (b + 1) (e + 1)
    ring_nf at this ⊢; exact this

theorem ab_drain : ∀ b, ∀ a e,
    ⟨a + 1, b, 0, 0, e⟩ [fm]⊢* ⟨0, 0, 2 * a + 3 * b + 2, 0, e⟩ := by
  intro b; induction' b using Nat.strongRecOn with b ihb; intro a e
  rcases b with _ | _ | b
  · have := r3_drain (a + 1) 0 e
    ring_nf at this ⊢; exact this
  · step fm; step fm
    have := r3_drain (a + 1 + 1) 1 e
    ring_nf at this ⊢; exact this
  · step fm; step fm; step fm
    have := ihb b (by omega) (a + 3) e
    ring_nf at this ⊢; exact this

theorem main_trans (D G : ℕ) :
    ⟨0, 0, 2 * D + G + 1, 0, D + G⟩ [fm]⊢⁺
    ⟨0, 0, 4 * D + 3 * G + 2, 0, 2 * D + 2 * G + 1⟩ := by
  have h0 : ⟨0, 0, 2 * D + G + 1, 0, D + G⟩ [fm]⊢*
      ⟨0, 0, 2 * D + G + 1, 2 * D + 2 * G, 0⟩ := by
    have := e_to_d (D + G) (2 * D + G + 1) 0 0
    ring_nf at this ⊢; exact this
  apply stepStar_stepPlus_stepPlus h0
  apply step_stepStar_stepPlus
  · show fm ⟨0, 0, 2 * D + G + 1, 2 * D + 2 * G, 0⟩ =
        some ⟨1, 0, 2 * D + G, 2 * D + 2 * G, 1⟩
    unfold fm; simp only
  have h1 : ⟨1, 0, 2 * D + G, 2 * D + 2 * G, 1⟩ [fm]⊢*
      ⟨2 * D + G + 1, 0, 0, G, 2 * D + G + 1⟩ := by
    have := r2r1_chain (2 * D + G) 0 0 G 1
    ring_nf at this ⊢; exact this
  have h2 : ⟨2 * D + G + 1, 0, 0, G, 2 * D + G + 1⟩ [fm]⊢*
      ⟨2 * D + 1, G, 0, 0, 2 * D + 2 * G + 1⟩ := by
    have := r2_drain G (2 * D + 1) 0 (2 * D + G + 1)
    ring_nf at this ⊢; exact this
  have h3 : ⟨2 * D + 1, G, 0, 0, 2 * D + 2 * G + 1⟩ [fm]⊢*
      ⟨0, 0, 4 * D + 3 * G + 2, 0, 2 * D + 2 * G + 1⟩ := by
    have := ab_drain G (2 * D) (2 * D + 2 * G + 1)
    ring_nf at this ⊢; exact this
  exact stepStar_trans h1 (stepStar_trans h2 h3)

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨0, 0, 3, 0, 1⟩)
  · execute fm 3
  apply progress_nonhalt_simple (fm := fm) (A := ℕ × ℕ)
    (fun p ↦ ⟨0, 0, 2 * p.1 + p.2 + 1, 0, p.1 + p.2⟩) ⟨1, 0⟩
  intro ⟨D, G⟩
  refine ⟨⟨2 * D + G, G + 1⟩, ?_⟩
  show ⟨0, 0, 2 * D + G + 1, 0, D + G⟩ [fm]⊢⁺
    ⟨0, 0, 2 * (2 * D + G) + (G + 1) + 1, 0, (2 * D + G) + (G + 1)⟩
  rw [show 2 * (2 * D + G) + (G + 1) + 1 = 4 * D + 3 * G + 2 from by ring,
      show (2 * D + G) + (G + 1) = 2 * D + 2 * G + 1 from by ring]
  exact main_trans D G

end Sz22_2003_unofficial_926
