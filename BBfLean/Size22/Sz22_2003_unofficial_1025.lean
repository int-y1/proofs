import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #1025: [4/15, 99/14, 65/2, 7/11, 14/13]

Vector representation:
```
 2 -1 -1  0  0  0
-1  2  0 -1  1  0
-1  0  1  0  0  1
 0  0  0  1 -1  0
 1  0  0  1  0 -1
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_1025

def Q := ℕ × ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a, b+1, c+1, d, e, f⟩ => some ⟨a+2, b, c, d, e, f⟩
  | ⟨a+1, b, c, d+1, e, f⟩ => some ⟨a, b+2, c, d, e+1, f⟩
  | ⟨a+1, b, c, d, e, f⟩ => some ⟨a, b, c+1, d, e, f+1⟩
  | ⟨a, b, c, d, e+1, f⟩ => some ⟨a, b, c, d+1, e, f⟩
  | ⟨a, b, c, d, e, f+1⟩ => some ⟨a+1, b, c, d+1, e, f⟩
  | _ => none

def cc : ℕ → ℕ
  | 0 => 3
  | n + 1 => cc n + n + 3

def ff : ℕ → ℕ
  | 0 => 3
  | n + 1 => ff n + 3 * (n + 2)

theorem r3_chain : ∀ k, ∀ c e f,
    ⟨k, (0 : ℕ), c, 0, e, f⟩ [fm]⊢* ⟨0, 0, c + k, 0, e, f + k⟩ := by
  intro k; induction' k with k ih <;> intro c e f
  · ring_nf; finish
  · rw [show c + (k + 1) = (c + 1) + k from by ring,
        show f + (k + 1) = (f + 1) + k from by ring]
    step fm
    apply stepStar_trans (ih (c + 1) e (f + 1))
    ring_nf; finish

theorem r4_chain : ∀ k, ∀ c d f,
    ⟨(0 : ℕ), 0, c, d, k, f⟩ [fm]⊢* ⟨0, 0, c, d + k, 0, f⟩ := by
  intro k; induction' k with k ih <;> intro c d f
  · ring_nf; finish
  · rw [show d + (k + 1) = (d + 1) + k from by ring]
    step fm
    apply stepStar_trans (ih c (d + 1) f)
    ring_nf; finish

theorem r2r1r1_chain : ∀ k, ∀ a c d e f,
    ⟨a + 1, (0 : ℕ), c + 2 * k, d + k, e, f⟩ [fm]⊢*
    ⟨a + 3 * k + 1, 0, c, d, e + k, f⟩ := by
  intro k; induction' k with k ih <;> intro a c d e f
  · ring_nf; finish
  · rw [show c + 2 * (k + 1) = (c + 2 * k) + 2 from by ring,
        show d + (k + 1) = (d + k) + 1 from by ring,
        show a + 3 * (k + 1) + 1 = (a + 3) + 3 * k + 1 from by ring,
        show e + (k + 1) = (e + 1) + k from by ring]
    step fm; step fm; step fm
    apply stepStar_trans (ih (a + 3) c d (e + 1) f)
    ring_nf; finish

theorem cc_ge (n : ℕ) (hn : n ≥ 1) : cc n ≥ 2 * (n + 2) := by
  induction' n with n ih
  · omega
  · simp only [cc]
    by_cases h : n = 0
    · subst h; simp [cc]
    · have : n ≥ 1 := Nat.pos_of_ne_zero h
      have := ih this
      omega

theorem main_trans_base :
    ⟨(1 : ℕ), 0, 3, 2, 0, 3⟩ [fm]⊢⁺ ⟨1, 0, 6, 3, 0, 9⟩ := by
  execute fm 16

theorem main_trans_succ (n : ℕ) (hn : n ≥ 1) :
    ⟨(1 : ℕ), 0, cc n, n + 2, 0, ff n⟩ [fm]⊢⁺
    ⟨1, 0, cc (n + 1), n + 3, 0, ff (n + 1)⟩ := by
  have hge := cc_ge n hn
  have h1 : ⟨(1 : ℕ), 0, cc n, n + 2, 0, ff n⟩ [fm]⊢*
      ⟨3 * (n + 2) + 1, 0, cc n - 2 * (n + 2), 0, n + 2, ff n⟩ := by
    have := r2r1r1_chain (n + 2) 0 (cc n - 2 * (n + 2)) 0 0 (ff n)
    rw [show (cc n - 2 * (n + 2)) + 2 * (n + 2) = cc n from Nat.sub_add_cancel hge,
        show (0 : ℕ) + 1 = 1 from rfl,
        show 0 + 3 * (n + 2) + 1 = 3 * (n + 2) + 1 from by omega,
        show (0 : ℕ) + (n + 2) = n + 2 from by omega] at this
    exact this
  have h2 : ⟨3 * (n + 2) + 1, (0 : ℕ), cc n - 2 * (n + 2), 0, n + 2, ff n⟩ [fm]⊢*
      ⟨0, 0, cc n - 2 * (n + 2) + (3 * (n + 2) + 1), 0, n + 2,
       ff n + (3 * (n + 2) + 1)⟩ :=
    r3_chain (3 * (n + 2) + 1) (cc n - 2 * (n + 2)) (n + 2) (ff n)
  have h3 : ⟨(0 : ℕ), 0, cc n - 2 * (n + 2) + (3 * (n + 2) + 1), 0, n + 2,
       ff n + (3 * (n + 2) + 1)⟩ [fm]⊢*
      ⟨0, 0, cc n - 2 * (n + 2) + (3 * (n + 2) + 1), n + 2, 0,
       ff n + (3 * (n + 2) + 1)⟩ := by
    have := r4_chain (n + 2) (cc n - 2 * (n + 2) + (3 * (n + 2) + 1)) 0
      (ff n + (3 * (n + 2) + 1))
    rw [show (0 : ℕ) + (n + 2) = n + 2 from by omega] at this
    exact this
  have h4 : ⟨(0 : ℕ), 0, cc n - 2 * (n + 2) + (3 * (n + 2) + 1), n + 2, 0,
       ff n + (3 * (n + 2) + 1)⟩ [fm]⊢⁺
      ⟨1, 0, cc n - 2 * (n + 2) + (3 * (n + 2) + 1), n + 3, 0,
       ff n + 3 * (n + 2)⟩ := by
    rw [show ff n + (3 * (n + 2) + 1) = (ff n + 3 * (n + 2)) + 1 from by ring]
    step fm; finish
  have hc : cc n - 2 * (n + 2) + (3 * (n + 2) + 1) = cc (n + 1) := by
    simp only [cc]; omega
  have hf : ff n + 3 * (n + 2) = ff (n + 1) := by
    simp only [ff]
  rw [hc, hf] at h4; rw [hc] at h3; rw [hc] at h2
  exact stepStar_stepPlus_stepPlus h1
    (stepStar_stepPlus_stepPlus h2
      (stepStar_stepPlus_stepPlus h3 h4))

theorem main_trans (n : ℕ) :
    ⟨(1 : ℕ), 0, cc n, n + 2, 0, ff n⟩ [fm]⊢⁺
    ⟨1, 0, cc (n + 1), n + 3, 0, ff (n + 1)⟩ := by
  rcases n with _ | n
  · show ⟨(1 : ℕ), 0, 3, 2, 0, 3⟩ [fm]⊢⁺ ⟨1, 0, 6, 3, 0, 9⟩
    exact main_trans_base
  · exact main_trans_succ (n + 1) (by omega)

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨1, 0, 3, 2, 0, 3⟩) (by execute fm 11)
  apply progress_nonhalt_simple (fm := fm) (A := ℕ)
    (fun n ↦ ⟨1, 0, cc n, n + 2, 0, ff n⟩) 0
  intro n; exact ⟨n + 1, main_trans n⟩
