import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #1887: [9/35, 5/33, 98/3, 11/7, 147/2]

Vector representation:
```
 0  2 -1 -1  0
 0 -1  1  0 -1
 1 -1  0  2  0
 0  0  0 -1  1
-1  1  0  2  0
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_1887

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a, b, c+1, d+1, e⟩ => some ⟨a, b+2, c, d, e⟩
  | ⟨a, b+1, c, d, e+1⟩ => some ⟨a, b, c+1, d, e⟩
  | ⟨a, b+1, c, d, e⟩ => some ⟨a+1, b, c, d+2, e⟩
  | ⟨a, b, c, d+1, e⟩ => some ⟨a, b, c, d, e+1⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b+1, c, d+2, e⟩
  | _ => none

theorem d_to_e : ∀ k d, ⟨a, 0, 0, d + k, 0⟩ [fm]⊢* ⟨a, 0, 0, d, k⟩ := by
  intro k; induction k with
  | zero => intro d; exists 0
  | succ k ih =>
    intro d
    rw [show d + (k + 1) = (d + 1) + k from by ring]
    apply stepStar_trans (ih (d + 1))
    step fm; finish

theorem r3_chain : ∀ k, ∀ a b d, ⟨a, b + k, 0, d, 0⟩ [fm]⊢* ⟨a + k, b, 0, d + 2 * k, 0⟩ := by
  intro k; induction k with
  | zero => intro a b d; exists 0
  | succ k ih =>
    intro a b d
    rw [show b + (k + 1) = b + k + 1 from by ring]
    step fm
    apply stepStar_trans (ih (a + 1) b (d + 2))
    ring_nf; finish

theorem round : ∀ c, ∀ a e, ⟨a + 1, 0, c, 0, e + 5⟩ [fm]⊢* ⟨a, 0, c + 3, 0, e⟩ := by
  intro c; rcases c with _ | _ | c <;> intro a e
  · step fm; step fm; step fm; step fm; step fm; step fm; step fm; step fm; finish
  · step fm; step fm; step fm; step fm; step fm; step fm; step fm; step fm; finish
  · show ⟨a + 1, 0, c + 2, 0, e + 5⟩ [fm]⊢* ⟨a, 0, c + 2 + 3, 0, e⟩
    rw [show c + 2 + 3 = c + 5 from by ring]
    step fm; step fm; step fm; step fm; step fm; step fm; step fm; step fm; finish

theorem rounds : ∀ k, ∀ a c e, ⟨a + k, 0, c, 0, e + 5 * k⟩ [fm]⊢* ⟨a, 0, c + 3 * k, 0, e⟩ := by
  intro k; induction k with
  | zero => intro a c e; simp; exists 0
  | succ k ih =>
    intro a c e
    rw [show a + (k + 1) = (a + 1) + k from by ring,
        show e + 5 * (k + 1) = (e + 5) + 5 * k from by ring]
    apply stepStar_trans (ih (a + 1) c (e + 5))
    apply stepStar_trans (round (c + 3 * k) a e)
    rw [show c + 3 * k + 3 = c + 3 * (k + 1) from by ring]; finish

theorem r1r1r3_chain : ∀ k, ∀ a b c, ⟨a, b, c + 2 * k, 2, 0⟩ [fm]⊢* ⟨a + k, b + 3 * k, c, 2, 0⟩ := by
  intro k; induction k with
  | zero => intro a b c; simp; exists 0
  | succ k ih =>
    intro a b c
    rw [show c + 2 * (k + 1) = (c + 2) + 2 * k from by ring]
    apply stepStar_trans (ih a b (c + 2))
    step fm; step fm; step fm
    ring_nf; finish

theorem combined_drain : ∀ c, ∀ a b, ⟨a, b, c, 2, 0⟩ [fm]⊢* ⟨a + b + 2 * c, 0, 0, 2 * b + 3 * c + 2, 0⟩ := by
  intro c; rcases Nat.even_or_odd c with ⟨k, hk⟩ | ⟨k, hk⟩ <;> intro a b
  · subst hk; rw [show k + k = 2 * k from by ring,
                   show (2 : ℕ) * k = 0 + 2 * k from by ring]
    apply stepStar_trans (r1r1r3_chain k a b 0)
    rw [show b + 3 * k = 0 + (b + 3 * k) from by ring]
    apply stepStar_trans (r3_chain (b + 3 * k) (a + k) 0 2)
    ring_nf; finish
  · subst hk
    rw [show (2 : ℕ) * k + 1 = 1 + 2 * k from by ring]
    apply stepStar_trans (r1r1r3_chain k a b 1)
    step fm
    rw [show b + 3 * k + 2 = 0 + (b + 3 * k + 2) from by ring]
    apply stepStar_trans (r3_chain (b + 3 * k + 2) (a + k) 0 1)
    ring_nf; finish

theorem terminal_c0_e0 : ⟨a + 1, 0, 0, 0, 0⟩ [fm]⊢⁺ ⟨a + 1, 0, 0, 4, 0⟩ := by
  step fm; step fm; finish

theorem terminal_c1_e0 : ⟨a + 1, 0, 1, 0, 0⟩ [fm]⊢⁺ ⟨a + 3, 0, 0, 7, 0⟩ := by
  step fm; step fm; step fm; step fm; step fm; finish

theorem terminal_cge2_e0 : ⟨a + 1, 0, c + 2, 0, 0⟩ [fm]⊢⁺ ⟨a + 2 * c + 5, 0, 0, 3 * c + 10, 0⟩ := by
  step fm; step fm; step fm; step fm
  apply stepStar_trans (combined_drain c (a + 1) 4)
  ring_nf; finish

theorem terminal_c0_e1 : ⟨a + 1, 0, 0, 0, 1⟩ [fm]⊢⁺ ⟨a + 2, 0, 0, 5, 0⟩ := by execute fm 5
theorem terminal_c1_e1 : ⟨a + 1, 0, 1, 0, 1⟩ [fm]⊢⁺ ⟨a + 4, 0, 0, 8, 0⟩ := by execute fm 8

theorem terminal_cge2_e1 : ⟨a + 1, 0, c + 2, 0, 1⟩ [fm]⊢⁺ ⟨a + 2 * c + 6, 0, 0, 3 * c + 11, 0⟩ := by
  step fm; step fm; step fm; step fm; step fm
  apply stepStar_trans (combined_drain (c + 1) (a + 1) 3)
  ring_nf; finish

theorem terminal_c0_e2 : ⟨a + 1, 0, 0, 0, 2⟩ [fm]⊢⁺ ⟨a + 3, 0, 0, 6, 0⟩ := by execute fm 8
theorem terminal_c1_e2 : ⟨a + 1, 0, 1, 0, 2⟩ [fm]⊢⁺ ⟨a + 5, 0, 0, 9, 0⟩ := by execute fm 11

theorem terminal_cge2_e2 : ⟨a + 1, 0, c + 2, 0, 2⟩ [fm]⊢⁺ ⟨a + 2 * c + 7, 0, 0, 3 * c + 12, 0⟩ := by
  step fm; step fm; step fm; step fm; step fm; step fm
  rw [show c + 1 + 1 = c + 2 from by ring]
  apply stepStar_trans (combined_drain (c + 2) (a + 1) 2)
  ring_nf; finish

theorem terminal_c0_e3 : ⟨a + 1, 0, 0, 0, 3⟩ [fm]⊢⁺ ⟨a + 4, 0, 0, 7, 0⟩ := by execute fm 11
theorem terminal_c1_e3 : ⟨a + 1, 0, 1, 0, 3⟩ [fm]⊢⁺ ⟨a + 6, 0, 0, 10, 0⟩ := by execute fm 14

theorem terminal_cge2_e3 : ⟨a + 1, 0, c + 2, 0, 3⟩ [fm]⊢⁺ ⟨a + 2 * c + 8, 0, 0, 3 * c + 13, 0⟩ := by
  step fm; step fm; step fm; step fm; step fm; step fm; step fm
  rw [show c + 2 + 1 = c + 3 from by ring]
  apply stepStar_trans (combined_drain (c + 3) (a + 1) 1)
  ring_nf; finish

theorem terminal_c0_e4 : ⟨a + 1, 0, 0, 0, 4⟩ [fm]⊢⁺ ⟨a + 5, 0, 0, 8, 0⟩ := by execute fm 14
theorem terminal_c1_e4 : ⟨a + 1, 0, 1, 0, 4⟩ [fm]⊢⁺ ⟨a + 7, 0, 0, 11, 0⟩ := by execute fm 17

theorem terminal_cge2_e4 : ⟨a + 1, 0, c + 2, 0, 4⟩ [fm]⊢⁺ ⟨a + 2 * c + 9, 0, 0, 3 * c + 14, 0⟩ := by
  step fm; step fm; step fm; step fm; step fm; step fm; step fm; step fm
  rw [show c + 3 + 1 = c + 4 from by ring]
  apply stepStar_trans (combined_drain (c + 4) (a + 1) 0)
  ring_nf; finish

theorem general_terminal (r : ℕ) (hr : r < 5) (c : ℕ) :
    ⟨a + 1, 0, c, 0, r⟩ [fm]⊢⁺ ⟨a + 2 * c + r + 1, 0, 0, 3 * c + r + 4, 0⟩ := by
  rcases c with _ | _ | c <;> (
    rcases (show r = 0 ∨ r = 1 ∨ r = 2 ∨ r = 3 ∨ r = 4 from by omega) with
      rfl | rfl | rfl | rfl | rfl)
  · exact terminal_c0_e0
  · exact terminal_c0_e1
  · exact terminal_c0_e2
  · exact terminal_c0_e3
  · exact terminal_c0_e4
  · exact terminal_c1_e0
  · exact terminal_c1_e1
  · exact terminal_c1_e2
  · exact terminal_c1_e3
  · exact terminal_c1_e4
  · exact terminal_cge2_e0 (a := a) (c := c)
  · exact terminal_cge2_e1 (a := a) (c := c)
  · exact terminal_cge2_e2 (a := a) (c := c)
  · exact terminal_cge2_e3 (a := a) (c := c)
  · exact terminal_cge2_e4 (a := a) (c := c)

theorem middle_phase (k : ℕ) (r : ℕ) (hr : r < 5) (c : ℕ) :
    ⟨a + 1 + k, 0, c, 0, 5 * k + r⟩ [fm]⊢⁺ ⟨a + 2 * c + 6 * k + r + 1, 0, 0, 3 * c + 9 * k + r + 4, 0⟩ := by
  rw [show 5 * k + r = r + 5 * k from by ring,
      show a + 1 + k = (a + 1) + k from by ring]
  apply stepStar_stepPlus_stepPlus (rounds k (a + 1) c r)
  have := general_terminal r hr (c + 3 * k) (a := a)
  rw [show a + 2 * (c + 3 * k) + r + 1 = a + 2 * c + 6 * k + r + 1 from by ring,
      show 3 * (c + 3 * k) = 3 * c + 9 * k from by ring] at this
  exact this

theorem main_trans (k r : ℕ) (hr : r < 5) :
    ⟨A + 1 + k, 0, 0, 5 * k + r, 0⟩ [fm]⊢⁺ ⟨A + 6 * k + r + 1, 0, 0, 9 * k + r + 4, 0⟩ := by
  apply stepStar_stepPlus_stepPlus
  · rw [show 5 * k + r = 0 + (5 * k + r) from by ring]
    exact d_to_e (5 * k + r) 0 (a := A + 1 + k)
  · have := middle_phase k r hr 0 (a := A)
    simp only [Nat.mul_zero, Nat.zero_add] at this
    exact this

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨1, 0, 0, 4, 0⟩) (by execute fm 2)
  apply progress_nonhalt (fm := fm)
    (P := fun q ↦ ∃ A D, q = ⟨A + 1, 0, 0, D, 0⟩ ∧ D < 5 * (A + 1))
  · intro c ⟨A, D, hq, hD⟩; subst hq
    obtain ⟨k, r, rfl, hr⟩ : ∃ k r, D = 5 * k + r ∧ r < 5 :=
      ⟨D / 5, D % 5, (Nat.div_add_mod D 5).symm, Nat.mod_lt D (by omega)⟩
    have hk : k ≤ A := by omega
    refine ⟨⟨A + 5 * k + r + 1, 0, 0, 9 * k + r + 4, 0⟩, ?_, ?_⟩
    · refine ⟨A + 5 * k + r, 9 * k + r + 4, rfl, ?_⟩
      omega
    · have h := main_trans k r hr (A := A - k)
      rw [show A - k + 1 + k = A + 1 from by omega,
          show A - k + 6 * k + r + 1 = A + 5 * k + r + 1 from by omega] at h
      exact h
  · exact ⟨0, 4, rfl, by omega⟩

end Sz22_2003_unofficial_1887
