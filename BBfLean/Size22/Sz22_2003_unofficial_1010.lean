import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #1010: [4/15, 9/14, 55/2, 49/5, 10/11]

Vector representation:
```
 2 -1 -1  0  0
-1  2  0 -1  0
-1  0  1  0  1
 0  0 -1  2  0
 1  0  1  0 -1
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_1010

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a, b+1, c+1, d, e⟩ => some ⟨a+2, b, c, d, e⟩
  | ⟨a+1, b, c, d+1, e⟩ => some ⟨a, b+2, c, d, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b, c+1, d, e+1⟩
  | ⟨a, b, c+1, d, e⟩ => some ⟨a, b, c, d+2, e⟩
  | ⟨a, b, c, d, e+1⟩ => some ⟨a+1, b, c+1, d, e⟩
  | _ => none

theorem r3_chain : ∀ k, ∀ a c e,
    ⟨a + k, 0, c, 0, e⟩ [fm]⊢* ⟨a, 0, c + k, 0, e + k⟩ := by
  intro k; induction' k with k ih <;> intro a c e
  · ring_nf; finish
  · rw [show a + (k + 1) = (a + k) + 1 from by ring]
    step fm
    apply stepStar_trans (ih a (c + 1) (e + 1))
    ring_nf; finish

theorem r4_chain : ∀ k, ∀ d e,
    ⟨0, 0, k, d, e⟩ [fm]⊢* ⟨0, 0, 0, d + 2 * k, e⟩ := by
  intro k; induction' k with k ih <;> intro d e
  · ring_nf; finish
  · rw [show (k : ℕ) + 1 = k + 1 from rfl]
    step fm
    apply stepStar_trans (ih (d + 2) e)
    ring_nf; finish

theorem r3r1_chain : ∀ k, ∀ a e,
    ⟨a + 1, k, 0, 0, e⟩ [fm]⊢* ⟨a + k + 1, 0, 0, 0, e + k⟩ := by
  intro k; induction' k with k ih <;> intro a e
  · ring_nf; finish
  · rw [show (k : ℕ) + 1 = k + 1 from rfl]
    step fm; step fm
    apply stepStar_trans (ih (a + 1) (e + 1))
    ring_nf; finish

theorem main_loop_step : ∀ B D E,
    ⟨0, B, 0, D + 3, E + 1⟩ [fm]⊢* ⟨0, B + 5, 0, D, E⟩ := by
  intro B D E
  rcases B with _ | B'
  · step fm; step fm; step fm; step fm; step fm; ring_nf; finish
  · step fm; step fm; step fm; step fm; step fm; ring_nf; finish

theorem main_loop : ∀ k, ∀ B D E,
    ⟨0, B, 0, D + 3 * k, E + k⟩ [fm]⊢* ⟨0, B + 5 * k, 0, D, E⟩ := by
  intro k; induction' k with k ih <;> intro B D E
  · ring_nf; finish
  · rw [show D + 3 * (k + 1) = (D + 3 * k) + 3 from by ring,
        show E + (k + 1) = (E + k) + 1 from by ring]
    apply stepStar_trans (main_loop_step B (D + 3 * k) (E + k))
    rw [show B + 5 * (k + 1) = B + 5 + 5 * k from by ring]
    exact ih (B + 5) D E

theorem endgame_d0 (B E : ℕ) :
    ⟨0, B + 1, 0, 0, E + 1⟩ [fm]⊢⁺ ⟨B + 3, 0, 0, 0, E + B⟩ := by
  step fm; step fm
  apply stepStar_trans (r3r1_chain B 2 E)
  ring_nf; finish

theorem endgame_d1 (B E : ℕ) :
    ⟨0, B + 1, 0, 1, E + 1⟩ [fm]⊢⁺ ⟨B + 4, 0, 0, 0, E + B + 2⟩ := by
  step fm; step fm; step fm; step fm; step fm
  apply stepStar_trans (r3r1_chain (B + 1) 2 (E + 1))
  ring_nf; finish

theorem endgame_d2 (B E : ℕ) :
    ⟨0, B + 1, 0, 2, E + 1⟩ [fm]⊢⁺ ⟨B + 5, 0, 0, 0, E + B + 4⟩ := by
  step fm; step fm; step fm; step fm; step fm; step fm
  apply stepStar_trans (r3r1_chain (B + 3) 1 (E + 1))
  ring_nf; finish

theorem trans_a0 (e : ℕ) :
    ⟨1, 0, 0, 0, e⟩ [fm]⊢⁺ ⟨4, 0, 0, 0, e + 3⟩ := by
  step fm; step fm; step fm; step fm; step fm
  step fm; step fm; step fm
  apply stepStar_trans (r3r1_chain 2 1 (e + 1))
  ring_nf; finish

theorem phases_12 (a e : ℕ) :
    ⟨a + 2, 0, 0, 0, e⟩ [fm]⊢* ⟨0, 0, 0, 2 * a + 4, e + a + 2⟩ := by
  apply stepStar_trans
  · have := r3_chain (a + 2) 0 0 e
    rw [show 0 + (a + 2) = a + 2 from by ring,
        show e + (a + 2) = e + a + 2 from by ring] at this; exact this
  · have := r4_chain (a + 2) 0 (e + a + 2)
    rw [show 0 + 2 * (a + 2) = 2 * a + 4 from by ring] at this; exact this

theorem main_trans (a e : ℕ) :
    ∃ a' e', ⟨a + 1, 0, 0, 0, e⟩ [fm]⊢⁺ ⟨a' + 1, 0, 0, 0, e'⟩ := by
  rcases a with _ | a
  · exact ⟨3, e + 3, trans_a0 e⟩
  · rw [show a + 1 + 1 = a + 2 from by ring]
    -- D = 2*a+4, k = D/3, r = D%3
    let k := (2 * a + 4) / 3
    let r := (2 * a + 4) % 3
    have hDkr : 2 * a + 4 = r + 3 * k := by omega
    have hr_lt : r < 3 := Nat.mod_lt _ (by omega)
    have hk_ge : k ≥ 1 := by omega
    have hEk : e + a + 2 ≥ k := by omega
    have hEk1 : e + a + 2 - k ≥ 1 := by omega
    have hBk : 5 * k ≥ 1 := by omega
    -- Phase 1+2
    have h12 := phases_12 a e
    -- Phase 3: main loop
    have h3 : ⟨0, 0, 0, 2 * a + 4, e + a + 2⟩ [fm]⊢*
        ⟨0, 5 * k, 0, r, e + a + 2 - k⟩ := by
      have := main_loop k 0 r (e + a + 2 - k)
      rw [show 0 + 5 * k = 5 * k from by ring,
          show r + 3 * k = 2 * a + 4 from by omega,
          show e + a + 2 - k + k = e + a + 2 from by omega] at this; exact this
    have h123 := stepStar_trans h12 h3
    -- Case split on remainder
    have : r = 0 ∨ r = 1 ∨ r = 2 := by omega
    rcases this with hr_eq | hr_eq | hr_eq <;> simp only [hr_eq] at h123
    · -- r = 0
      have h4 := endgame_d0 (5 * k - 1) (e + a + 2 - k - 1)
      rw [show 5 * k - 1 + 1 = 5 * k from by omega,
          show e + a + 2 - k - 1 + 1 = e + a + 2 - k from by omega] at h4
      exact ⟨5 * k - 1 + 2, e + a + 2 - k - 1 + (5 * k - 1),
             stepStar_stepPlus_stepPlus h123 h4⟩
    · -- r = 1
      have h4 := endgame_d1 (5 * k - 1) (e + a + 2 - k - 1)
      rw [show 5 * k - 1 + 1 = 5 * k from by omega,
          show e + a + 2 - k - 1 + 1 = e + a + 2 - k from by omega] at h4
      exact ⟨5 * k - 1 + 3, e + a + 2 - k - 1 + (5 * k - 1) + 2,
             stepStar_stepPlus_stepPlus h123 h4⟩
    · -- r = 2
      have h4 := endgame_d2 (5 * k - 1) (e + a + 2 - k - 1)
      rw [show 5 * k - 1 + 1 = 5 * k from by omega,
          show e + a + 2 - k - 1 + 1 = e + a + 2 - k from by omega] at h4
      exact ⟨5 * k - 1 + 4, e + a + 2 - k - 1 + (5 * k - 1) + 4,
             stepStar_stepPlus_stepPlus h123 h4⟩

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨1, 0, 0, 0, 0⟩) (by finish)
  apply progress_nonhalt (fm := fm)
    (P := fun q ↦ ∃ a e, q = ⟨a + 1, 0, 0, 0, e⟩)
  · intro c ⟨a, e, hc⟩
    subst hc
    obtain ⟨a', e', h⟩ := main_trans a e
    exact ⟨⟨a' + 1, 0, 0, 0, e'⟩, ⟨a', e', rfl⟩, h⟩
  · exact ⟨0, 0, rfl⟩
