import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #750: [35/6, 4/55, 77/2, 3/49, 10/11]

Vector representation:
```
-1 -1  1  1  0
 2  0 -1  0 -1
-1  0  0  1  1
 0  1  0 -2  0
 1  0  1  0 -1
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_750

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a+1, b+1, c, d, e⟩ => some ⟨a, b, c+1, d+1, e⟩
  | ⟨a, b, c+1, d, e+1⟩ => some ⟨a+2, b, c, d, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b, c, d+1, e+1⟩
  | ⟨a, b, c, d+2, e⟩ => some ⟨a, b+1, c, d, e⟩
  | ⟨a, b, c, d, e+1⟩ => some ⟨a+1, b, c+1, d, e⟩
  | _ => none

theorem r3_chain : ∀ k, ∀ a d e, ⟨a + k, 0, 0, d, e⟩ [fm]⊢* ⟨a, 0, 0, d + k, e + k⟩ := by
  intro k; induction' k with k ih <;> intro a d e
  · exists 0
  · rw [show a + (k + 1) = (a + k) + 1 from by ring]
    step fm
    apply stepStar_trans (ih a (d + 1) (e + 1))
    ring_nf; finish

theorem r4_chain : ∀ k, ∀ b d e, ⟨0, b, 0, d + 2 * k, e⟩ [fm]⊢* ⟨0, b + k, 0, d, e⟩ := by
  intro k; induction' k with k ih <;> intro b d e
  · exists 0
  · rw [show d + 2 * (k + 1) = (d + 2 * k) + 2 from by ring]
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

theorem r2r1r1_cycle : ∀ k, ∀ b c d e, ⟨0, b + 2 * k, c + 1, d, e + k⟩ [fm]⊢* ⟨0, b, c + k + 1, d + 2 * k, e⟩ := by
  intro k; induction' k with k ih <;> intro b c d e
  · exists 0
  · rw [show b + 2 * (k + 1) = (b + 2 * k + 1) + 1 from by ring,
        show e + (k + 1) = (e + k) + 1 from by ring]
    step fm
    rw [show b + 2 * k + 1 = (b + 2 * k) + 1 from by ring]
    step fm; step fm
    apply stepStar_trans (ih b (c + 1) (d + 2) e)
    ring_nf; finish

theorem r3r2_drain : ∀ k, ∀ a d, ⟨a + 1, 0, k, d, 0⟩ [fm]⊢* ⟨a + k + 1, 0, 0, d + k, 0⟩ := by
  intro k; induction' k with k ih <;> intro a d
  · exists 0
  · rw [show (k + 1) = k + 1 from rfl]
    step fm; step fm
    apply stepStar_trans (ih (a + 1) (d + 1))
    ring_nf; finish

theorem r2_r3r2 : ∀ k, ∀ a c d, ⟨a + 1, 0, c + k, d, k⟩ [fm]⊢* ⟨a + c + 2 * k + 1, 0, 0, d + c, 0⟩ := by
  intro k; induction' k with k ih <;> intro a c d
  · exact r3r2_drain c a d
  · rw [show c + (k + 1) = (c + k) + 1 from by ring,
        show (k + 1) = k + 1 from rfl]
    step fm
    apply stepStar_trans (ih (a + 2) c d)
    ring_nf; finish

theorem main_n4m (m : ℕ) :
    ⟨4 * m + 2, 0, 0, 8 * m + 2, 0⟩ [fm]⊢⁺ ⟨4 * m + 3, 0, 0, 8 * m + 4, 0⟩ := by
  rw [show 4 * m + 2 = (4 * m + 1) + 1 from by ring]
  apply step_stepStar_stepPlus
  · show fm ⟨(4 * m + 1) + 1, 0, 0, 8 * m + 2, 0⟩ = some ⟨4 * m + 1, 0, 0, 8 * m + 3, 1⟩
    simp [fm]
  rw [show (4 * m + 1 : ℕ) = 0 + (4 * m + 1) from by ring]
  apply stepStar_trans (r3_chain (4 * m + 1) 0 (8 * m + 3) 1)
  rw [show 8 * m + 3 + (4 * m + 1) = 0 + 2 * (6 * m + 2) from by ring,
      show 1 + (4 * m + 1) = 4 * m + 2 from by ring]
  apply stepStar_trans (r4_chain (6 * m + 2) 0 0 (4 * m + 2))
  rw [show 0 + (6 * m + 2) = (6 * m + 1) + 1 from by ring,
      show 4 * m + 2 = (4 * m + 1) + 1 from by ring]
  step fm
  rw [show 6 * m + 1 = (6 * m) + 1 from by ring]
  step fm
  rw [show 6 * m + 1 = 1 + 2 * (3 * m) from by ring,
      show 4 * m + 1 = (m + 1) + 3 * m from by ring]
  apply stepStar_trans (r2r1r1_cycle (3 * m) 1 1 1 (m + 1))
  rw [show 1 + 3 * m + 1 = (3 * m + 1) + 1 from by ring,
      show 1 + 2 * (3 * m) = 6 * m + 1 from by ring,
      show (m + 1 : ℕ) = m + 1 from rfl]
  step fm; step fm
  rw [show 3 * m + 1 + 1 = (2 * m + 2) + m from by ring,
      show 6 * m + 1 + 1 = 6 * m + 2 from by ring]
  apply stepStar_trans (r2_r3r2 m 0 (2 * m + 2) (6 * m + 2))
  ring_nf; finish

theorem main_n4m1 (m : ℕ) :
    ⟨4 * m + 3, 0, 0, 8 * m + 4, 0⟩ [fm]⊢⁺ ⟨4 * m + 4, 0, 0, 8 * m + 6, 0⟩ := by
  rw [show 4 * m + 3 = (4 * m + 2) + 1 from by ring]
  apply step_stepStar_stepPlus
  · show fm ⟨(4 * m + 2) + 1, 0, 0, 8 * m + 4, 0⟩ = some ⟨4 * m + 2, 0, 0, 8 * m + 5, 1⟩
    simp [fm]
  rw [show (4 * m + 2 : ℕ) = 0 + (4 * m + 2) from by ring]
  apply stepStar_trans (r3_chain (4 * m + 2) 0 (8 * m + 5) 1)
  rw [show 8 * m + 5 + (4 * m + 2) = 1 + 2 * (6 * m + 3) from by ring,
      show 1 + (4 * m + 2) = 4 * m + 3 from by ring]
  apply stepStar_trans (r4_chain (6 * m + 3) 0 1 (4 * m + 3))
  rw [show 0 + (6 * m + 3) = (6 * m + 2) + 1 from by ring,
      show 4 * m + 3 = (4 * m + 2) + 1 from by ring]
  step fm
  rw [show 6 * m + 2 = (6 * m) + 1 + 1 from by ring]
  step fm
  rw [show 6 * m + 2 = 0 + 2 * (3 * m + 1) from by ring,
      show 4 * m + 2 = (m + 1) + (3 * m + 1) from by ring]
  apply stepStar_trans (r2r1r1_cycle (3 * m + 1) 0 1 2 (m + 1))
  rw [show 1 + (3 * m + 1) + 1 = (3 * m + 2) + 1 from by ring,
      show 2 + 2 * (3 * m + 1) = 6 * m + 4 from by ring,
      show (m + 1 : ℕ) = (m + 1) from rfl]
  step fm
  rw [show (2 : ℕ) = 1 + 1 from by ring,
      show 3 * m + 2 = (2 * m + 2) + m from by ring]
  apply stepStar_trans (r2_r3r2 m 1 (2 * m + 2) (6 * m + 4))
  ring_nf; finish

theorem main_n4m2 (m : ℕ) :
    ⟨4 * m + 4, 0, 0, 8 * m + 6, 0⟩ [fm]⊢⁺ ⟨4 * m + 5, 0, 0, 8 * m + 8, 0⟩ := by
  rw [show 4 * m + 4 = (4 * m + 3) + 1 from by ring]
  apply step_stepStar_stepPlus
  · show fm ⟨(4 * m + 3) + 1, 0, 0, 8 * m + 6, 0⟩ = some ⟨4 * m + 3, 0, 0, 8 * m + 7, 1⟩
    simp [fm]
  rw [show (4 * m + 3 : ℕ) = 0 + (4 * m + 3) from by ring]
  apply stepStar_trans (r3_chain (4 * m + 3) 0 (8 * m + 7) 1)
  rw [show 8 * m + 7 + (4 * m + 3) = 0 + 2 * (6 * m + 5) from by ring,
      show 1 + (4 * m + 3) = 4 * m + 4 from by ring]
  apply stepStar_trans (r4_chain (6 * m + 5) 0 0 (4 * m + 4))
  rw [show 0 + (6 * m + 5) = (6 * m + 4) + 1 from by ring,
      show 4 * m + 4 = (4 * m + 3) + 1 from by ring]
  step fm
  rw [show 6 * m + 4 = (6 * m + 2) + 1 + 1 from by ring]
  step fm
  rw [show 6 * m + 4 = 0 + 2 * (3 * m + 2) from by ring,
      show 4 * m + 3 = (m + 1) + (3 * m + 2) from by ring]
  apply stepStar_trans (r2r1r1_cycle (3 * m + 2) 0 1 1 (m + 1))
  rw [show 1 + (3 * m + 2) + 1 = (3 * m + 3) + 1 from by ring,
      show 1 + 2 * (3 * m + 2) = 6 * m + 5 from by ring,
      show (m + 1 : ℕ) = (m + 1) from rfl]
  step fm
  rw [show (2 : ℕ) = 1 + 1 from by ring,
      show 3 * m + 3 = (2 * m + 3) + m from by ring]
  apply stepStar_trans (r2_r3r2 m 1 (2 * m + 3) (6 * m + 5))
  ring_nf; finish

theorem main_n4m3 (m : ℕ) :
    ⟨4 * m + 5, 0, 0, 8 * m + 8, 0⟩ [fm]⊢⁺ ⟨4 * m + 6, 0, 0, 8 * m + 10, 0⟩ := by
  rw [show 4 * m + 5 = (4 * m + 4) + 1 from by ring]
  apply step_stepStar_stepPlus
  · show fm ⟨(4 * m + 4) + 1, 0, 0, 8 * m + 8, 0⟩ = some ⟨4 * m + 4, 0, 0, 8 * m + 9, 1⟩
    simp [fm]
  rw [show (4 * m + 4 : ℕ) = 0 + (4 * m + 4) from by ring]
  apply stepStar_trans (r3_chain (4 * m + 4) 0 (8 * m + 9) 1)
  rw [show 8 * m + 9 + (4 * m + 4) = 1 + 2 * (6 * m + 6) from by ring,
      show 1 + (4 * m + 4) = 4 * m + 5 from by ring]
  apply stepStar_trans (r4_chain (6 * m + 6) 0 1 (4 * m + 5))
  rw [show 0 + (6 * m + 6) = (6 * m + 5) + 1 from by ring,
      show 4 * m + 5 = (4 * m + 4) + 1 from by ring]
  step fm
  rw [show 6 * m + 5 = (6 * m + 4) + 1 from by ring]
  step fm
  rw [show 6 * m + 5 = 1 + 2 * (3 * m + 2) from by ring,
      show 4 * m + 4 = (m + 2) + (3 * m + 2) from by ring]
  apply stepStar_trans (r2r1r1_cycle (3 * m + 2) 1 1 2 (m + 2))
  rw [show 1 + (3 * m + 2) + 1 = (3 * m + 3) + 1 from by ring,
      show 2 + 2 * (3 * m + 2) = 6 * m + 6 from by ring,
      show (m + 2 : ℕ) = m + 2 from rfl]
  step fm; step fm
  rw [show 3 * m + 3 + 1 = (2 * m + 3) + (m + 1) from by ring,
      show 6 * m + 6 + 1 = 6 * m + 7 from by ring]
  apply stepStar_trans (r2_r3r2 (m + 1) 0 (2 * m + 3) (6 * m + 7))
  ring_nf; finish

theorem main_trans (n : ℕ) :
    ⟨n + 2, 0, 0, 2 * n + 2, 0⟩ [fm]⊢⁺ ⟨n + 3, 0, 0, 2 * n + 4, 0⟩ := by
  rcases Nat.even_or_odd n with ⟨k, hk⟩ | ⟨k, hk⟩
  · rw [show k + k = 2 * k from by ring] at hk
    rcases Nat.even_or_odd k with ⟨m, hm⟩ | ⟨m, hm⟩
    · rw [show m + m = 2 * m from by ring] at hm; subst hm; subst hk
      rw [show 2 * (2 * m) + 2 = 4 * m + 2 from by ring,
          show 2 * (2 * (2 * m)) + 2 = 8 * m + 2 from by ring,
          show 2 * (2 * m) + 3 = 4 * m + 3 from by ring,
          show 2 * (2 * (2 * m)) + 4 = 8 * m + 4 from by ring]
      exact main_n4m m
    · rw [show 2 * m + 1 = 2 * m + 1 from rfl] at hm; subst hm; subst hk
      rw [show 2 * (2 * m + 1) + 2 = 4 * m + 4 from by ring,
          show 2 * (2 * (2 * m + 1)) + 2 = 8 * m + 6 from by ring,
          show 2 * (2 * m + 1) + 3 = 4 * m + 5 from by ring,
          show 2 * (2 * (2 * m + 1)) + 4 = 8 * m + 8 from by ring]
      exact main_n4m2 m
  · subst hk
    rcases Nat.even_or_odd k with ⟨m, hm⟩ | ⟨m, hm⟩
    · rw [show m + m = 2 * m from by ring] at hm; subst hm
      rw [show 2 * (2 * m) + 1 + 2 = 4 * m + 3 from by ring,
          show 2 * (2 * (2 * m) + 1) + 2 = 8 * m + 4 from by ring,
          show 2 * (2 * m) + 1 + 3 = 4 * m + 4 from by ring,
          show 2 * (2 * (2 * m) + 1) + 4 = 8 * m + 6 from by ring]
      exact main_n4m1 m
    · rw [show 2 * m + 1 = 2 * m + 1 from rfl] at hm; subst hm
      rw [show 2 * (2 * m + 1) + 1 + 2 = 4 * m + 5 from by ring,
          show 2 * (2 * (2 * m + 1) + 1) + 2 = 8 * m + 8 from by ring,
          show 2 * (2 * m + 1) + 1 + 3 = 4 * m + 6 from by ring,
          show 2 * (2 * (2 * m + 1) + 1) + 4 = 8 * m + 10 from by ring]
      exact main_n4m3 m

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨2, 0, 0, 2, 0⟩)
  · execute fm 4
  apply progress_nonhalt_simple (fm := fm) (A := ℕ)
    (fun n ↦ ⟨n + 2, 0, 0, 2 * n + 2, 0⟩) 0
  intro n; exact ⟨n + 1, main_trans n⟩

end Sz22_2003_unofficial_750
