import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #1139: [5/6, 44/35, 49/2, 9/11, 22/7]

Vector representation:
```
-1 -1  1  0  0
 2  0 -1 -1  1
-1  0  0  2  0
 0  2  0  0 -1
 1  0  0 -1  1
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_1139

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a+1, b+1, c, d, e⟩ => some ⟨a, b, c+1, d, e⟩
  | ⟨a, b, c+1, d+1, e⟩ => some ⟨a+2, b, c, d, e+1⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b, c, d+2, e⟩
  | ⟨a, b, c, d, e+1⟩ => some ⟨a, b+2, c, d, e⟩
  | ⟨a, b, c, d+1, e⟩ => some ⟨a+1, b, c, d, e+1⟩
  | _ => none

theorem r4_drain : ∀ k : ℕ, ∀ b d, ⟨0, b, 0, d, k⟩ [fm]⊢* ⟨0, b + 2 * k, 0, d, 0⟩ := by
  intro k; induction' k with k ih <;> intro b d
  · exists 0
  · step fm
    apply stepStar_trans (ih (b + 2) d)
    ring_nf; finish

theorem a_to_d_drain : ∀ k, ⟨k, 0, 0, d, e⟩ [fm]⊢* ⟨0, 0, 0, d + 2 * k, e⟩ := by
  intro k; induction' k with k ih generalizing d
  · exists 0
  · step fm
    apply stepStar_trans (ih (d := d + 2))
    ring_nf; finish

theorem spiral_chain : ∀ k, ⟨2, b + 2 * k, c, d + k, e⟩ [fm]⊢* ⟨2, b, c + k, d, e + k⟩ := by
  intro k; induction' k with k ih generalizing b c d e
  · exists 0
  · rw [show b + 2 * (k + 1) = (b + 2 * k) + 2 from by ring,
        show d + (k + 1) = (d + k) + 1 from by ring]
    step fm; step fm; step fm
    apply stepStar_trans (ih (b := b) (c := c + 1) (d := d) (e := e + 1))
    ring_nf; finish

theorem r2_chain_d0 : ∀ k, ⟨a, 0, c + k, k, e⟩ [fm]⊢* ⟨a + 2 * k, 0, c, 0, e + k⟩ := by
  intro k; induction' k with k ih generalizing a c e
  · exists 0
  · rw [show c + (k + 1) = (c + k) + 1 from by ring]
    step fm
    apply stepStar_trans (ih (a := a + 2) (c := c) (e := e + 1))
    ring_nf; finish

theorem combined_tail_drain :
    ∀ c, ∀ a e, ⟨a + 1, 0, c, 0, e⟩ [fm]⊢* ⟨0, 0, 0, 2 * a + 3 * c + 2, e + c⟩ := by
  intro c; induction' c using Nat.strongRecOn with c ih; intro a e
  rcases c with _ | _ | c
  · apply stepStar_trans (a_to_d_drain (a + 1) (d := 0) (e := e))
    ring_nf; finish
  · step fm; step fm
    apply stepStar_trans (a_to_d_drain (a + 2) (d := 1) (e := e + 1))
    ring_nf; finish
  · step fm; step fm; step fm
    rw [show a + 4 = (a + 3) + 1 from by ring]
    apply stepStar_trans (ih c (by omega) (a + 3) (e + 2))
    ring_nf; finish

theorem phases_1_to_5 :
    ⟨0, 0, 0, m + e + 2, e + 1⟩ [fm]⊢* ⟨1, 0, e + 1, m, e + 2⟩ := by
  apply stepStar_trans (r4_drain (e + 1) 0 (m + e + 2))
  simp only [Nat.zero_add]
  step fm; step fm; step fm
  simp only [Nat.mul_eq]
  rw [show 2 * e + 1 = 1 + 2 * e from by ring]
  apply stepStar_trans (spiral_chain e (b := 1) (c := 0) (d := m) (e := 2))
  step fm
  ring_nf; finish

theorem phases_6_8_case1 :
    ⟨1, 0, j + d, d, e⟩ [fm]⊢* ⟨0, 0, 0, 4 * d + 3 * j + 2, e + j + d⟩ := by
  apply stepStar_trans (r2_chain_d0 d (a := 1) (c := j) (e := e))
  rw [show 1 + 2 * d = 2 * d + 1 from by ring]
  apply stepStar_trans (combined_tail_drain j (2 * d) (e + d))
  ring_nf; finish

theorem main_trans (hm : m ≤ e + 1) :
    ⟨0, 0, 0, m + e + 2, e + 1⟩ [fm]⊢⁺ ⟨0, 0, 0, m + 3 * e + 5, 2 * e + 3⟩ := by
  obtain ⟨j, hj⟩ : ∃ j, e + 1 = j + m := ⟨e + 1 - m, (Nat.sub_add_cancel hm).symm⟩
  apply stepStar_stepPlus
  · apply stepStar_trans phases_1_to_5
    rw [hj]
    apply stepStar_trans (phases_6_8_case1 (j := j) (d := m) (e := e + 2))
    rw [show 4 * m + 3 * j + 2 = m + 3 * e + 5 from by omega,
        show e + 2 + j + m = 2 * e + 3 from by omega]
    finish
  · simp [Q]; omega

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨0, 0, 0, 3, 1⟩)
  · execute fm 3
  apply progress_nonhalt (fm := fm)
    (P := fun q ↦ ∃ m e, q = ⟨0, 0, 0, m + e + 2, e + 1⟩ ∧ m ≤ e + 1)
  · intro c ⟨m, e, hq, hm⟩; subst hq
    exact ⟨⟨0, 0, 0, m + 3 * e + 5, 2 * e + 3⟩,
      ⟨m + e + 1, 2 * e + 2, by ring_nf, by omega⟩,
      main_trans hm⟩
  · exact ⟨1, 0, by ring_nf, by omega⟩

end Sz22_2003_unofficial_1139
