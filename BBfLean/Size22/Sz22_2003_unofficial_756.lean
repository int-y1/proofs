import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #756: [35/6, 4/55, 847/2, 3/7, 35/11]

Vector representation:
```
-1 -1  1  1  0
 2  0 -1  0 -1
-1  0  0  1  2
 0  1  0 -1  0
 0  0  1  1 -1
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_756

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a+1, b+1, c, d, e⟩ => some ⟨a, b, c+1, d+1, e⟩
  | ⟨a, b, c+1, d, e+1⟩ => some ⟨a+2, b, c, d, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b, c, d+1, e+2⟩
  | ⟨a, b, c, d+1, e⟩ => some ⟨a, b+1, c, d, e⟩
  | ⟨a, b, c, d, e+1⟩ => some ⟨a, b, c+1, d+1, e⟩
  | _ => none

theorem r4_chain : ∀ k, ∀ b d e, ⟨0, b, 0, d + k, e⟩ [fm]⊢* ⟨0, b + k, 0, d, e⟩ := by
  intro k; induction' k with k ih <;> intro b d e
  · exists 0
  · rw [show d + (k + 1) = (d + k) + 1 from by ring]
    step fm
    apply stepStar_trans (ih (b + 1) d e)
    ring_nf; finish

theorem r2_chain : ∀ k, ∀ a c d e, ⟨a, 0, c + k, d, e + k⟩ [fm]⊢* ⟨a + 2 * k, 0, c, d, e⟩ := by
  intro k; induction' k with k ih <;> intro a c d e
  · exists 0
  · rw [show c + (k + 1) = (c + k) + 1 from by ring,
        show e + (k + 1) = (e + k) + 1 from by ring]
    step fm
    apply stepStar_trans (ih (a + 2) c d e)
    ring_nf; finish

theorem r3_chain : ∀ k, ∀ a d e, ⟨a + k, 0, 0, d, e⟩ [fm]⊢* ⟨a, 0, 0, d + k, e + 2 * k⟩ := by
  intro k; induction' k with k ih <;> intro a d e
  · exists 0
  · rw [show a + (k + 1) = (a + k) + 1 from by ring]
    step fm
    apply stepStar_trans (ih a (d + 1) (e + 2))
    ring_nf; finish

theorem r2r1r1_cycle : ∀ k, ∀ c d e, ⟨0, 2 * k + 1, c + 1, d, e + k⟩ [fm]⊢* ⟨0, 1, c + k + 1, d + 2 * k, e⟩ := by
  intro k; induction' k with k ih <;> intro c d e
  · exists 0
  · rw [show 2 * (k + 1) + 1 = (2 * k + 2) + 1 from by ring,
        show e + (k + 1) = (e + k) + 1 from by ring]
    step fm
    rw [show 2 * k + 2 = (2 * k + 1) + 1 from by ring]
    step fm; step fm
    apply stepStar_trans (ih (c + 1) (d + 2) e)
    ring_nf; finish

theorem r3r2r2_even : ∀ j, ∀ A D, ⟨A + 1, 0, 2 * j, D, 0⟩ [fm]⊢* ⟨A + 3 * j + 1, 0, 0, D + j, 0⟩ := by
  intro j; induction' j with j ih <;> intro A D
  · exists 0
  · rw [show 2 * (j + 1) = (2 * j + 1) + 1 from by ring]
    step fm
    rw [show 2 * j + 1 = (2 * j) + 1 from by ring]
    step fm; step fm
    apply stepStar_trans (ih (A + 3) (D + 1))
    ring_nf; finish

theorem r3r2r2_odd : ∀ j, ∀ A D, ⟨A + 1, 0, 2 * j + 1, D, 0⟩ [fm]⊢* ⟨A + 3 * j + 2, 0, 0, D + j + 1, 1⟩ := by
  intro j; induction' j with j ih <;> intro A D
  · step fm; step fm; finish
  · rw [show 2 * (j + 1) + 1 = (2 * j + 2) + 1 from by ring]
    step fm
    rw [show 2 * j + 2 = (2 * j + 1) + 1 from by ring]
    step fm; step fm
    apply stepStar_trans (ih (A + 3) (D + 1))
    ring_nf; finish

theorem main_trans (m e : ℕ) (he : e ≤ m) :
    ⟨0, 0, 0, 2 * m + 1, m + e + 2⟩ [fm]⊢⁺ ⟨0, 0, 0, 4 * m + 5, 3 * m + e + 5⟩ := by
  rw [show (0 : ℕ) = 0 from rfl,
      show 2 * m + 1 = 0 + (2 * m + 1) from by ring]
  apply step_stepStar_stepPlus
  · show fm ⟨0, 0, 0, 0 + (2 * m + 1), m + e + 2⟩ = some ⟨0, 0 + 1, 0, 0 + (2 * m), m + e + 2⟩
    simp [fm]
  rw [show 0 + (2 * m) = 0 + 2 * m from by ring]
  apply stepStar_trans (r4_chain (2 * m) 1 0 (m + e + 2))
  rw [show 0 + 1 + (2 * m) = 2 * m + 1 from by ring]
  rw [show m + e + 2 = (m + e + 1) + 1 from by ring]
  step fm
  rw [show m + e + 1 = (e + 1) + m from by ring]
  apply stepStar_trans (r2r1r1_cycle m 0 1 (e + 1))
  rw [show 0 + m + 1 = m + 1 from by ring,
      show 1 + 2 * m = 2 * m + 1 from by ring]
  rw [show e + 1 = (e) + 1 from by ring]
  step fm
  rw [show (2 : ℕ) = 2 from rfl]
  step fm
  rw [show e = 0 + e from by ring,
      show m + 1 = (m + 1 - e) + e from by omega,
      show 2 * m + 2 = 2 * m + 2 from rfl]
  apply stepStar_trans (r2_chain e 1 (m + 1 - e) (2 * m + 2) 0)
  rw [show 1 + 2 * e = 2 * e + 1 from by ring,
      show 0 + e = e from by ring]
  have hme : m + 1 ≥ e := by omega
  rcases Nat.even_or_odd (m + 1 - e) with ⟨j, hj⟩ | ⟨j, hj⟩
  · rw [show j + j = 2 * j from by ring] at hj
    have hj' : m + 1 = e + 2 * j := by omega
    rw [hj]
    apply stepStar_trans (r3r2r2_even j (2 * e) (2 * m + 2))
    rw [show 2 * e + 3 * j + 1 = 0 + (2 * e + 3 * j + 1) from by ring]
    apply stepStar_trans (r3_chain (2 * e + 3 * j + 1) 0 (2 * m + 2 + j) 0)
    have h1 : 2 * m + 2 + j + (2 * e + 3 * j + 1) = 4 * m + 5 := by omega
    have h2 : 0 + 2 * (2 * e + 3 * j + 1) = 3 * m + e + 5 := by omega
    rw [h1, h2]; finish
  · rw [show 2 * j + 1 = 2 * j + 1 from rfl] at hj
    have hj' : m + 1 = e + (2 * j + 1) := by omega
    rw [hj]
    apply stepStar_trans (r3r2r2_odd j (2 * e) (2 * m + 2))
    rw [show 2 * e + 3 * j + 2 = 0 + (2 * e + 3 * j + 2) from by ring]
    apply stepStar_trans (r3_chain (2 * e + 3 * j + 2) 0 (2 * m + 2 + j + 1) 1)
    have h1 : 2 * m + 2 + j + 1 + (2 * e + 3 * j + 2) = 4 * m + 5 := by omega
    have h2 : 1 + 2 * (2 * e + 3 * j + 2) = 3 * m + e + 5 := by omega
    rw [h1, h2]; finish

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨0, 0, 0, 1, 2⟩) (by execute fm 1)
  apply progress_nonhalt (fm := fm)
    (P := fun q ↦ ∃ m e, q = ⟨0, 0, 0, 2 * m + 1, m + e + 2⟩ ∧ e ≤ m)
  · intro c ⟨m, e, hq, he⟩; subst hq
    refine ⟨⟨0, 0, 0, 4 * m + 5, 3 * m + e + 5⟩,
      ⟨2 * m + 2, m + e + 1, by ring_nf, by omega⟩,
      main_trans m e he⟩
  · exact ⟨0, 0, by ring_nf, by omega⟩

end Sz22_2003_unofficial_756
