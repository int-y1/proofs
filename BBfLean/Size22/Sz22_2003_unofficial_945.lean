import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #945: [4/15, 33/14, 275/2, 7/11, 22/5]

Vector representation:
```
 2 -1 -1  0  0
-1  1  0 -1  1
-1  0  2  0  1
 0  0  0  1 -1
 1  0 -1  0  1
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_945

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a, b+1, c+1, d, e⟩ => some ⟨a+2, b, c, d, e⟩
  | ⟨a+1, b, c, d+1, e⟩ => some ⟨a, b+1, c, d, e+1⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b, c+2, d, e+1⟩
  | ⟨a, b, c, d, e+1⟩ => some ⟨a, b, c, d+1, e⟩
  | ⟨a, b, c+1, d, e⟩ => some ⟨a+1, b, c, d, e+1⟩
  | _ => none

theorem r4_drain : ∀ k, ∀ c d,
    ⟨0, 0, c, d, k⟩ [fm]⊢* ⟨0, 0, c, d + k, 0⟩ := by
  intro k; induction' k with k ih <;> intro c d
  · ring_nf; finish
  · rw [show (k : ℕ) + 1 = k + 1 from rfl]
    step fm; apply stepStar_trans (ih c (d + 1)); ring_nf; finish

theorem r2r1_chain : ∀ k, ∀ a c d e,
    ⟨a + 1, 0, c + k, d + k, e + 1⟩ [fm]⊢* ⟨a + k + 1, 0, c, d, e + k + 1⟩ := by
  intro k; induction' k with k ih <;> intro a c d e
  · ring_nf; finish
  · rw [show c + (k + 1) = (c + k) + 1 from by ring,
        show d + (k + 1) = (d + k) + 1 from by ring]
    step fm; step fm
    have := ih (a + 1) c d (e + 1)
    ring_nf at this ⊢; exact this

theorem r3_drain : ∀ j, ∀ c e,
    ⟨j, 0, c, 0, e⟩ [fm]⊢* ⟨0, 0, c + 2 * j, 0, e + j⟩ := by
  intro j; induction' j with j ih <;> intro c e
  · ring_nf; finish
  · step fm
    have := ih (c + 2) (e + 1)
    ring_nf at this ⊢; exact this

theorem r2_drain : ∀ k, ∀ a b e,
    ⟨a + k, b, 0, k, e⟩ [fm]⊢* ⟨a, b + k, 0, 0, e + k⟩ := by
  intro k; induction' k with k ih <;> intro a b e
  · ring_nf; finish
  · rw [show a + (k + 1) = (a + k) + 1 from by ring]
    step fm
    have := ih a (b + 1) (e + 1)
    ring_nf at this ⊢; exact this

theorem ab_drain : ∀ b, ∀ a e,
    ⟨a + 1, b, 0, 0, e⟩ [fm]⊢* ⟨0, 0, 2 * a + 3 * b + 2, 0, e + a + 2 * b + 1⟩ := by
  intro b; induction' b using Nat.strongRecOn with b ihb; intro a e
  rcases b with _ | _ | b
  · have := r3_drain (a + 1) 0 e
    ring_nf at this ⊢; exact this
  · step fm; step fm
    have := r3_drain (a + 1 + 1) 1 (e + 1)
    ring_nf at this ⊢; exact this
  · step fm; step fm; step fm
    have := ihb b (by omega) (a + 3) (e + 1)
    ring_nf at this ⊢; exact this

theorem main_trans (c e : ℕ) (hce : c ≤ e) (h2c : 2 * c ≥ e + 2) :
    ⟨0, 0, c, 0, e⟩ [fm]⊢⁺ ⟨0, 0, c + e + 1, 0, 2 * e + 2⟩ := by
  have hc1 : c ≥ 1 := by omega
  have h0 : ⟨0, 0, c, 0, e⟩ [fm]⊢* ⟨0, 0, c, e, 0⟩ := by
    have := r4_drain e c 0
    ring_nf at this ⊢; exact this
  apply stepStar_stepPlus_stepPlus h0
  obtain ⟨c', rfl⟩ : ∃ c', c = c' + 1 := ⟨c - 1, by omega⟩
  have hr5 : ⟨0, 0, c' + 1, e, 0⟩ [fm]⊢ ⟨1, 0, c', e, 1⟩ := by
    unfold fm; simp only
  have h1 : ⟨1, 0, c', e, 1⟩ [fm]⊢* ⟨c' + 1, 0, 0, e - c', c' + 1⟩ := by
    have := r2r1_chain c' 0 0 (e - c') 0
    simp only [Nat.zero_add] at this
    rw [show (e - c') + c' = e from by omega] at this
    exact this
  have h2 : ⟨c' + 1, 0, 0, e - c', c' + 1⟩ [fm]⊢*
      ⟨2 * c' + 2 - e - 1, e - c', 0, 0, e + 1⟩ := by
    have := r2_drain (e - c') (2 * c' + 2 - e - 1) 0 (c' + 1)
    rw [show (2 * c' + 2 - e - 1) + (e - c') = c' + 1 from by omega,
        show 0 + (e - c') = e - c' from by ring,
        show (c' + 1) + (e - c') = e + 1 from by omega] at this
    exact this
  have h3 : ⟨2 * c' + 2 - e - 1, e - c', 0, 0, e + 1⟩ [fm]⊢*
      ⟨0, 0, c' + 1 + e + 1, 0, 2 * e + 2⟩ := by
    have := ab_drain (e - c') (2 * c' - e) (e + 1)
    rw [show (2 * c' - e) + 1 = 2 * c' + 2 - e - 1 from by omega,
        show 2 * (2 * c' - e) + 3 * (e - c') + 2 = c' + 1 + e + 1 from by omega,
        show (e + 1) + (2 * c' - e) + 2 * (e - c') + 1 = 2 * e + 2 from by omega] at this
    exact this
  exact step_stepStar_stepPlus hr5
    (stepStar_trans h1 (stepStar_trans h2 h3))

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨0, 0, 4, 0, 4⟩) (by execute fm 7)
  apply progress_nonhalt (fm := fm)
    (P := fun q ↦ ∃ c e, q = ⟨0, 0, c, 0, e⟩ ∧ c ≤ e ∧ 2 * c ≥ e + 2)
  · intro q ⟨c, e, hq, hce, h2c⟩
    exact ⟨⟨0, 0, c + e + 1, 0, 2 * e + 2⟩,
      ⟨c + e + 1, 2 * e + 2, rfl, by omega, by omega⟩,
      hq ▸ main_trans c e hce h2c⟩
  · exact ⟨4, 4, rfl, le_refl 4, by omega⟩

end Sz22_2003_unofficial_945
