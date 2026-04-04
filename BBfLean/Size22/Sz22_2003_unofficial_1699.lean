import BBfLean.FM
import Mathlib.Tactic.Ring
import Mathlib.Tactic.IntervalCases

/-!
# sz22_2003_unofficial #1699: [77/15, 9/70, 22/3, 5/11, 9/2]

Vector representation:
```
 0 -1 -1  1  1
-1  2 -1 -1  0
 1 -1  0  0  1
 0  0  1  0 -1
-1  2  0  0  0
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_1699

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a, b+1, c+1, d, e⟩ => some ⟨a, b, c, d+1, e+1⟩
  | ⟨a+1, b, c+1, d+1, e⟩ => some ⟨a, b+2, c, d, e⟩
  | ⟨a, b+1, c, d, e⟩ => some ⟨a+1, b, c, d, e+1⟩
  | ⟨a, b, c, d, e+1⟩ => some ⟨a, b, c+1, d, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b+2, c, d, e⟩
  | _ => none

theorem r1r1r2_chain : ∀ k, ∀ a c d e,
    ⟨a+k, 2, c+3*k, d, e⟩ [fm]⊢* ⟨a, 2, c, d+k, e+2*k⟩ := by
  intro k; induction' k with k ih <;> intro a c d e
  · exists 0
  rw [show a + (k + 1) = (a + k) + 1 from by ring,
      show c + 3 * (k + 1) = (c + 3 * k + 2) + 1 from by ring]
  step fm
  rw [show c + 3 * k + 2 = (c + 3 * k + 1) + 1 from by ring]
  step fm
  rw [show c + 3 * k + 1 = (c + 3 * k) + 1 from by ring,
      show d + 2 = (d + 1) + 1 from by ring]
  step fm
  apply stepStar_trans (ih a c (d + 1) (e + 2))
  ring_nf; finish

theorem e_to_c : ∀ k, ∀ a c,
    ⟨a, 0, c, 0, k⟩ [fm]⊢* ⟨a, 0, c+k, 0, 0⟩ := by
  intro k; induction' k with k ih <;> intro a c
  · exists 0
  step fm
  apply stepStar_trans (ih a (c + 1))
  ring_nf; finish

theorem d_drain : ∀ k, ∀ a e,
    ⟨a+1, 0, 0, k, e+1⟩ [fm]⊢* ⟨a+k+1, 0, 0, 0, e+k+1⟩ := by
  intro k; induction' k with k ih <;> intro a e
  · exists 0
  step fm
  rw [show (1 : ℕ) = 0 + 1 from rfl]
  step fm
  rw [show (2 : ℕ) = 1 + 1 from rfl]
  step fm
  step fm
  apply stepStar_trans (ih (a + 1) (e + 1))
  ring_nf; finish

theorem trans_mod0 (j : ℕ) :
    ⟨3*j+2, 0, 6*j+2, 0, 0⟩ [fm]⊢⁺ ⟨3*j+3, 0, 6*j+4, 0, 0⟩ := by
  rw [show 3 * j + 2 = (3 * j + 1) + 1 from by ring]
  step fm
  apply stepStar_trans
  · rw [show 3 * j + 1 = (j + 1) + 2 * j from by ring,
        show 6 * j + 2 = 2 + 3 * (2 * j) from by ring]
    exact r1r1r2_chain (2*j) (j+1) 2 0 0
  rw [show 0 + 2 * j = 2 * j from by ring,
      show 0 + 2 * (2 * j) = 4 * j from by ring,
      show (2 : ℕ) = (1 : ℕ) + 1 from rfl]
  step fm
  step fm
  apply stepStar_trans
  · rw [show j + 1 = j + 1 from rfl,
        show 4 * j + 2 = (4 * j + 1) + 1 from by ring]
    exact d_drain (2*j+2) j (4*j+1)
  rw [show j + (2 * j + 2) + 1 = 3 * j + 3 from by ring,
      show 4 * j + 1 + (2 * j + 2) + 1 = 6 * j + 4 from by ring]
  have h := e_to_c (6*j+4) (3*j+3) 0
  rw [show (0 : ℕ) + (6 * j + 4) = 6 * j + 4 from by ring] at h
  exact h

theorem trans_mod1 (j : ℕ) :
    ⟨3*j+3, 0, 6*j+4, 0, 0⟩ [fm]⊢⁺ ⟨3*j+4, 0, 6*j+6, 0, 0⟩ := by
  rw [show 3 * j + 3 = (3 * j + 2) + 1 from by ring]
  step fm
  apply stepStar_trans
  · rw [show 3 * j + 2 = (j + 1) + (2 * j + 1) from by ring,
        show 6 * j + 4 = 1 + 3 * (2 * j + 1) from by ring]
    exact r1r1r2_chain (2*j+1) (j+1) 1 0 0
  rw [show 0 + (2 * j + 1) = 2 * j + 1 from by ring,
      show 0 + 2 * (2 * j + 1) = 4 * j + 2 from by ring,
      show (1 : ℕ) = 0 + 1 from rfl]
  step fm
  step fm
  apply stepStar_trans
  · rw [show j + 2 = (j + 1) + 1 from by ring,
        show 4 * j + 4 = (4 * j + 3) + 1 from by ring]
    exact d_drain (2*j+2) (j+1) (4*j+3)
  rw [show j + 1 + (2 * j + 2) + 1 = 3 * j + 4 from by ring,
      show 4 * j + 3 + (2 * j + 2) + 1 = 6 * j + 6 from by ring]
  have h := e_to_c (6*j+6) (3*j+4) 0
  rw [show (0 : ℕ) + (6 * j + 6) = 6 * j + 6 from by ring] at h
  exact h

theorem trans_mod2 (j : ℕ) :
    ⟨3*j+4, 0, 6*j+6, 0, 0⟩ [fm]⊢⁺ ⟨3*j+5, 0, 6*j+8, 0, 0⟩ := by
  rw [show 3 * j + 4 = (3 * j + 3) + 1 from by ring]
  step fm
  apply stepStar_trans
  · rw [show 3 * j + 3 = (j + 1) + (2 * j + 2) from by ring,
        show 6 * j + 6 = 0 + 3 * (2 * j + 2) from by ring]
    exact r1r1r2_chain (2*j+2) (j+1) 0 0 0
  rw [show 0 + (2 * j + 2) = 2 * j + 2 from by ring,
      show 0 + 2 * (2 * j + 2) = 4 * j + 4 from by ring]
  step fm
  step fm
  apply stepStar_trans
  · rw [show j + 3 = (j + 2) + 1 from by ring,
        show 4 * j + 6 = (4 * j + 5) + 1 from by ring]
    exact d_drain (2*j+2) (j+2) (4*j+5)
  rw [show j + 2 + (2 * j + 2) + 1 = 3 * j + 5 from by ring,
      show 4 * j + 5 + (2 * j + 2) + 1 = 6 * j + 8 from by ring]
  have h := e_to_c (6*j+8) (3*j+5) 0
  rw [show (0 : ℕ) + (6 * j + 8) = 6 * j + 8 from by ring] at h
  exact h

theorem main_trans (n : ℕ) :
    ⟨n+2, 0, 2*n+2, 0, 0⟩ [fm]⊢⁺ ⟨n+3, 0, 2*n+4, 0, 0⟩ := by
  have h3 : n % 3 < 3 := Nat.mod_lt _ (by omega)
  obtain ⟨j, hj⟩ : ∃ j, n = 3 * j + n % 3 := ⟨n / 3, by omega⟩
  interval_cases (n % 3)
  · rw [Nat.add_zero] at hj; subst hj
    rw [show 2 * (3 * j) + 2 = 6 * j + 2 from by ring,
        show 3 * j + 3 = 3 * j + 3 from rfl,
        show 2 * (3 * j) + 4 = 6 * j + 4 from by ring]
    exact trans_mod0 j
  · subst hj
    rw [show 3 * j + 1 + 2 = 3 * j + 3 from by ring,
        show 2 * (3 * j + 1) + 2 = 6 * j + 4 from by ring,
        show 3 * j + 1 + 3 = 3 * j + 4 from by ring,
        show 2 * (3 * j + 1) + 4 = 6 * j + 6 from by ring]
    exact trans_mod1 j
  · subst hj
    rw [show 3 * j + 2 + 2 = 3 * j + 4 from by ring,
        show 2 * (3 * j + 2) + 2 = 6 * j + 6 from by ring,
        show 3 * j + 2 + 3 = 3 * j + 5 from by ring,
        show 2 * (3 * j + 2) + 4 = 6 * j + 8 from by ring]
    exact trans_mod2 j

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨2, 0, 2, 0, 0⟩)
  · execute fm 5
  apply progress_nonhalt_simple (fm := fm) (A := ℕ)
    (fun n ↦ ⟨n+2, 0, 2*n+2, 0, 0⟩) 0
  intro n; exact ⟨n + 1, main_trans n⟩

end Sz22_2003_unofficial_1699
