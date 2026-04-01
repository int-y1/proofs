import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #1442: [7/15, 242/3, 9/77, 5/11, 363/2]

Vector representation:
```
 0 -1 -1  1  0
 1 -1  0  0  2
 0  2  0 -1 -1
 0  0  1  0 -1
-1  1  0  0  2
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_1442

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a, b+1, c+1, d, e⟩ => some ⟨a, b, c, d+1, e⟩
  | ⟨a, b+1, c, d, e⟩ => some ⟨a+1, b, c, d, e+2⟩
  | ⟨a, b, c, d+1, e+1⟩ => some ⟨a, b+2, c, d, e⟩
  | ⟨a, b, c, d, e+1⟩ => some ⟨a, b, c+1, d, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b+1, c, d, e+2⟩
  | _ => none

theorem r4_step_plus : ⟨a, 0, c, 0, e + 1⟩ [fm]⊢⁺ ⟨a, 0, c + 1, 0, e⟩ := by
  step fm; finish

theorem e_to_c : ∀ k c, ⟨a, 0, c, 0, e + k⟩ [fm]⊢* ⟨a, 0, c + k, 0, e⟩ := by
  intro k; induction' k with k ih <;> intro c
  · exists 0
  · rw [Nat.add_succ]; step fm
    apply stepStar_trans (ih (c + 1)); ring_nf; finish

theorem middle_round : ∀ a c D,
    ⟨a + 1, 0, c + 5, D, 0⟩ [fm]⊢* ⟨a, 0, c, D + 3, 0⟩ := by
  intro a c D
  rw [show c + 5 = ((c + 3) + 1) + 1 from by ring]
  step fm; step fm; step fm; step fm; step fm; step fm; step fm; step fm
  ring_nf; finish

theorem middle_chain : ∀ k a c D,
    ⟨a + k, 0, c + 5 * k, D, 0⟩ [fm]⊢* ⟨a, 0, c, D + 3 * k, 0⟩ := by
  intro k; induction' k with k ih <;> intro a c D
  · exists 0
  · rw [show a + (k + 1) = (a + k) + 1 from by ring,
        show c + 5 * (k + 1) = (c + 5 * k) + 5 from by ring]
    apply stepStar_trans (middle_round (a + k) (c + 5 * k) D)
    apply stepStar_trans (ih a c (D + 3)); ring_nf; finish

theorem rem0 : ∀ a D, ⟨a + 1, 0, 0, D, 0⟩ [fm]⊢* ⟨a + 1, 0, 0, D, 4⟩ := by
  intro a D; step fm; step fm; ring_nf; finish

theorem rem1 : ∀ a D, ⟨a + 1, 0, 1, D, 0⟩ [fm]⊢* ⟨a, 0, 0, D + 1, 2⟩ := by
  intro a D; step fm; step fm; ring_nf; finish

theorem rem2 : ∀ a D, ⟨a + 1, 0, 2, D, 0⟩ [fm]⊢* ⟨a + 1, 0, 0, D + 1, 3⟩ := by
  intro a D
  rw [show (2 : ℕ) = 0 + 1 + 1 from rfl]
  step fm; step fm; step fm; step fm; step fm; ring_nf; finish

theorem rem3 : ∀ a D, ⟨a + 1, 0, 3, D, 0⟩ [fm]⊢* ⟨a, 0, 0, D + 2, 1⟩ := by
  intro a D
  rw [show (3 : ℕ) = 0 + 1 + 1 + 1 from rfl]
  step fm; step fm; step fm; step fm; step fm; ring_nf; finish

theorem rem4 : ∀ a D, ⟨a + 1, 0, 4, D, 0⟩ [fm]⊢* ⟨a + 1, 0, 0, D + 2, 2⟩ := by
  intro a D
  rw [show (4 : ℕ) = 0 + 1 + 1 + 1 + 1 from rfl]
  step fm; step fm; step fm; step fm; step fm; step fm; step fm; step fm
  ring_nf; finish

theorem r3r2r2_chain : ∀ k a d e,
    ⟨a, 0, 0, d + k, e + 1⟩ [fm]⊢* ⟨a + 2 * k, 0, 0, d, e + 3 * k + 1⟩ := by
  intro k; induction' k with k ih <;> intro a d e
  · exists 0
  · rw [show d + (k + 1) = (d + k) + 1 from by ring,
        show e + 1 = e + 0 + 1 from by ring]
    step fm; step fm; step fm
    rw [show e + 0 + 4 = (e + 3) + 1 from by ring]
    apply stepStar_trans (ih (a + 2) d (e + 3)); ring_nf; finish

theorem cycle_r1 (a f : ℕ) :
    ⟨a + f + 1, 0, 0, 0, 5 * f + 1⟩ [fm]⊢⁺ ⟨a + 6 * f + 2, 0, 0, 0, 9 * f + 5⟩ := by
  rw [show 5 * f + 1 = (5 * f) + 1 from by ring]
  apply stepPlus_stepStar_stepPlus (r4_step_plus (a := a + f + 1) (c := 0) (e := 5 * f))
  rw [show 0 + 1 = 1 from by ring, show 5 * f = 0 + 5 * f from by ring]
  apply stepStar_trans (e_to_c (5 * f) 1 (a := a + f + 1) (e := 0))
  rw [show 1 + 5 * f = 1 + 5 * f from by ring, show a + f + 1 = (a + 1) + f from by ring]
  apply stepStar_trans (middle_chain f (a + 1) 1 0)
  rw [show 0 + 3 * f = 3 * f from by ring]
  apply stepStar_trans (rem1 a (3 * f))
  rw [show 3 * f + 1 = 0 + (3 * f + 1) from by ring, show (2 : ℕ) = 1 + 1 from rfl]
  apply stepStar_trans (r3r2r2_chain (3 * f + 1) a 0 1)
  ring_nf; finish

theorem cycle_r2 (a f : ℕ) :
    ⟨a + f + 1, 0, 0, 0, 5 * f + 2⟩ [fm]⊢⁺ ⟨a + 6 * f + 3, 0, 0, 0, 9 * f + 6⟩ := by
  rw [show 5 * f + 2 = (5 * f + 1) + 1 from by ring]
  apply stepPlus_stepStar_stepPlus (r4_step_plus (a := a + f + 1) (c := 0) (e := 5 * f + 1))
  rw [show 0 + 1 = 1 from by ring, show 5 * f + 1 = 0 + (5 * f + 1) from by ring]
  apply stepStar_trans (e_to_c (5 * f + 1) 1 (a := a + f + 1) (e := 0))
  rw [show 1 + (5 * f + 1) = 2 + 5 * f from by ring, show a + f + 1 = (a + 1) + f from by ring]
  apply stepStar_trans (middle_chain f (a + 1) 2 0)
  rw [show 0 + 3 * f = 3 * f from by ring]
  apply stepStar_trans (rem2 a (3 * f))
  rw [show 3 * f + 1 = 0 + (3 * f + 1) from by ring, show (3 : ℕ) = 2 + 1 from rfl]
  apply stepStar_trans (r3r2r2_chain (3 * f + 1) (a + 1) 0 2)
  ring_nf; finish

theorem cycle_r3 (a f : ℕ) :
    ⟨a + f + 1, 0, 0, 0, 5 * f + 3⟩ [fm]⊢⁺ ⟨a + 6 * f + 4, 0, 0, 0, 9 * f + 7⟩ := by
  rw [show 5 * f + 3 = (5 * f + 2) + 1 from by ring]
  apply stepPlus_stepStar_stepPlus (r4_step_plus (a := a + f + 1) (c := 0) (e := 5 * f + 2))
  rw [show 0 + 1 = 1 from by ring, show 5 * f + 2 = 0 + (5 * f + 2) from by ring]
  apply stepStar_trans (e_to_c (5 * f + 2) 1 (a := a + f + 1) (e := 0))
  rw [show 1 + (5 * f + 2) = 3 + 5 * f from by ring, show a + f + 1 = (a + 1) + f from by ring]
  apply stepStar_trans (middle_chain f (a + 1) 3 0)
  rw [show 0 + 3 * f = 3 * f from by ring]
  apply stepStar_trans (rem3 a (3 * f))
  rw [show 3 * f + 2 = 0 + (3 * f + 2) from by ring, show (1 : ℕ) = 0 + 1 from rfl]
  apply stepStar_trans (r3r2r2_chain (3 * f + 2) a 0 0)
  ring_nf; finish

theorem cycle_r4 (a f : ℕ) :
    ⟨a + f + 1, 0, 0, 0, 5 * f + 4⟩ [fm]⊢⁺ ⟨a + 6 * f + 5, 0, 0, 0, 9 * f + 8⟩ := by
  rw [show 5 * f + 4 = (5 * f + 3) + 1 from by ring]
  apply stepPlus_stepStar_stepPlus (r4_step_plus (a := a + f + 1) (c := 0) (e := 5 * f + 3))
  rw [show 0 + 1 = 1 from by ring, show 5 * f + 3 = 0 + (5 * f + 3) from by ring]
  apply stepStar_trans (e_to_c (5 * f + 3) 1 (a := a + f + 1) (e := 0))
  rw [show 1 + (5 * f + 3) = 4 + 5 * f from by ring, show a + f + 1 = (a + 1) + f from by ring]
  apply stepStar_trans (middle_chain f (a + 1) 4 0)
  rw [show 0 + 3 * f = 3 * f from by ring]
  apply stepStar_trans (rem4 a (3 * f))
  rw [show 3 * f + 2 = 0 + (3 * f + 2) from by ring, show (2 : ℕ) = 1 + 1 from rfl]
  apply stepStar_trans (r3r2r2_chain (3 * f + 2) (a + 1) 0 1)
  ring_nf; finish

theorem cycle_r0 (a f : ℕ) :
    ⟨a + f + 2, 0, 0, 0, 5 * (f + 1)⟩ [fm]⊢⁺ ⟨a + 6 * f + 7, 0, 0, 0, 9 * f + 13⟩ := by
  rw [show 5 * (f + 1) = (5 * f + 4) + 1 from by ring]
  apply stepPlus_stepStar_stepPlus (r4_step_plus (a := a + f + 2) (c := 0) (e := 5 * f + 4))
  rw [show 0 + 1 = 1 from by ring, show 5 * f + 4 = 0 + (5 * f + 4) from by ring]
  apply stepStar_trans (e_to_c (5 * f + 4) 1 (a := a + f + 2) (e := 0))
  rw [show 1 + (5 * f + 4) = 0 + 5 * (f + 1) from by ring,
      show a + f + 2 = (a + 1) + (f + 1) from by ring]
  apply stepStar_trans (middle_chain (f + 1) (a + 1) 0 0)
  rw [show 0 + 3 * (f + 1) = 3 * f + 3 from by ring]
  apply stepStar_trans (rem0 a (3 * f + 3))
  rw [show 3 * f + 3 = 0 + (3 * f + 3) from by ring, show (4 : ℕ) = 3 + 1 from rfl]
  apply stepStar_trans (r3r2r2_chain (3 * f + 3) (a + 1) 0 3)
  ring_nf; finish

private theorem main_r0 (a f : ℕ) (h : a ≥ f + 1) :
    ∃ a' e', ⟨a + 1, 0, 0, 0, 5 * (f + 1)⟩ [fm]⊢⁺ ⟨a' + 1, 0, 0, 0, e' + 1⟩
    ∧ a' ≥ (e' + 1) / 5 := by
  refine ⟨a - (f + 1) + 6 * f + 6, 9 * f + 12, ?_, ?_⟩
  · rw [show a + 1 = (a - (f + 1)) + f + 2 from by omega,
        show a - (f + 1) + 6 * f + 6 + 1 = (a - (f + 1)) + 6 * f + 7 from by ring,
        show 9 * f + 12 + 1 = 9 * f + 13 from by ring]
    exact cycle_r0 (a - (f + 1)) f
  · omega

private theorem main_r1 (a f : ℕ) (h : a ≥ f) :
    ∃ a' e', ⟨a + 1, 0, 0, 0, 5 * f + 1⟩ [fm]⊢⁺ ⟨a' + 1, 0, 0, 0, e' + 1⟩
    ∧ a' ≥ (e' + 1) / 5 := by
  refine ⟨(a - f) + 6 * f + 1, 9 * f + 4, ?_, ?_⟩
  · rw [show a + 1 = (a - f) + f + 1 from by omega,
        show (a - f) + 6 * f + 1 + 1 = (a - f) + 6 * f + 2 from by ring,
        show 9 * f + 4 + 1 = 9 * f + 5 from by ring]
    exact cycle_r1 (a - f) f
  · omega

private theorem main_r2 (a f : ℕ) (h : a ≥ f) :
    ∃ a' e', ⟨a + 1, 0, 0, 0, 5 * f + 2⟩ [fm]⊢⁺ ⟨a' + 1, 0, 0, 0, e' + 1⟩
    ∧ a' ≥ (e' + 1) / 5 := by
  refine ⟨(a - f) + 6 * f + 2, 9 * f + 5, ?_, ?_⟩
  · rw [show a + 1 = (a - f) + f + 1 from by omega,
        show (a - f) + 6 * f + 2 + 1 = (a - f) + 6 * f + 3 from by ring,
        show 9 * f + 5 + 1 = 9 * f + 6 from by ring]
    exact cycle_r2 (a - f) f
  · omega

private theorem main_r3 (a f : ℕ) (h : a ≥ f) :
    ∃ a' e', ⟨a + 1, 0, 0, 0, 5 * f + 3⟩ [fm]⊢⁺ ⟨a' + 1, 0, 0, 0, e' + 1⟩
    ∧ a' ≥ (e' + 1) / 5 := by
  refine ⟨(a - f) + 6 * f + 3, 9 * f + 6, ?_, ?_⟩
  · rw [show a + 1 = (a - f) + f + 1 from by omega,
        show (a - f) + 6 * f + 3 + 1 = (a - f) + 6 * f + 4 from by ring,
        show 9 * f + 6 + 1 = 9 * f + 7 from by ring]
    exact cycle_r3 (a - f) f
  · omega

private theorem main_r4 (a f : ℕ) (h : a ≥ f) :
    ∃ a' e', ⟨a + 1, 0, 0, 0, 5 * f + 4⟩ [fm]⊢⁺ ⟨a' + 1, 0, 0, 0, e' + 1⟩
    ∧ a' ≥ (e' + 1) / 5 := by
  refine ⟨(a - f) + 6 * f + 4, 9 * f + 7, ?_, ?_⟩
  · rw [show a + 1 = (a - f) + f + 1 from by omega,
        show (a - f) + 6 * f + 4 + 1 = (a - f) + 6 * f + 5 from by ring,
        show 9 * f + 7 + 1 = 9 * f + 8 from by ring]
    exact cycle_r4 (a - f) f
  · omega

theorem main_trans (a e : ℕ) (h : a ≥ (e + 1) / 5) :
    ∃ a' e', ⟨a + 1, 0, 0, 0, e + 1⟩ [fm]⊢⁺ ⟨a' + 1, 0, 0, 0, e' + 1⟩
    ∧ a' ≥ (e' + 1) / 5 := by
  have hrem : (e + 1) % 5 = 0 ∨ (e + 1) % 5 = 1 ∨ (e + 1) % 5 = 2 ∨
    (e + 1) % 5 = 3 ∨ (e + 1) % 5 = 4 := by omega
  rcases hrem with h0 | h1 | h2 | h3 | h4
  · have : e + 1 = 5 * ((e + 1) / 5) := by omega
    rw [show e + 1 = 5 * ((e + 1) / 5 - 1 + 1) from by omega]
    exact main_r0 a ((e + 1) / 5 - 1) (by omega)
  · rw [show e + 1 = 5 * ((e + 1) / 5) + 1 from by omega]
    exact main_r1 a ((e + 1) / 5) h
  · rw [show e + 1 = 5 * ((e + 1) / 5) + 2 from by omega]
    exact main_r2 a ((e + 1) / 5) h
  · rw [show e + 1 = 5 * ((e + 1) / 5) + 3 from by omega]
    exact main_r3 a ((e + 1) / 5) h
  · rw [show e + 1 = 5 * ((e + 1) / 5) + 4 from by omega]
    exact main_r4 a ((e + 1) / 5) h

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨1, 0, 0, 0, 4⟩)
  · execute fm 2
  apply progress_nonhalt (fm := fm)
    (P := fun q ↦ ∃ a e, q = ⟨a + 1, 0, 0, 0, e + 1⟩ ∧ a ≥ (e + 1) / 5)
  · intro q ⟨a, e, hq, hinv⟩
    subst hq
    obtain ⟨a', e', htrans, hinv'⟩ := main_trans a e hinv
    exact ⟨⟨a' + 1, 0, 0, 0, e' + 1⟩, ⟨a', e', rfl, hinv'⟩, htrans⟩
  · exact ⟨0, 3, rfl, by omega⟩

end Sz22_2003_unofficial_1442
