import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #708: [35/6, 4/55, 121/2, 3/7, 6/11]

Vector representation:
```
-1 -1  1  1  0
 2  0 -1  0 -1
-1  0  0  0  2
 0  1  0 -1  0
 1  1  0  0 -1
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_708

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a+1, b+1, c, d, e⟩ => some ⟨a, b, c+1, d+1, e⟩
  | ⟨a, b, c+1, d, e+1⟩ => some ⟨a+2, b, c, d, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b, c, d, e+2⟩
  | ⟨a, b, c, d+1, e⟩ => some ⟨a, b+1, c, d, e⟩
  | ⟨a, b, c, d, e+1⟩ => some ⟨a+1, b+1, c, d, e⟩
  | _ => none

theorem r3_chain : ∀ k, ∀ a d e, ⟨a + k, 0, 0, d, e⟩ [fm]⊢* ⟨a, 0, 0, d, e + 2 * k⟩ := by
  intro k; induction' k with k ih <;> intro a d e
  · exists 0
  · rw [show a + (k + 1) = (a + k) + 1 from by ring]
    step fm
    apply stepStar_trans (ih a d (e + 2))
    ring_nf; finish

theorem r4_chain : ∀ k, ∀ b d e, ⟨0, b, 0, d + k, e⟩ [fm]⊢* ⟨0, b + k, 0, d, e⟩ := by
  intro k; induction' k with k ih <;> intro b d e
  · exists 0
  · rw [show d + (k + 1) = (d + k) + 1 from by ring]
    step fm
    apply stepStar_trans (ih (b + 1) d e)
    ring_nf; finish

theorem r2_drain : ∀ k, ∀ a c d e, ⟨a, 0, c + k, d, e + k⟩ [fm]⊢* ⟨a + 2 * k, 0, c, d, e⟩ := by
  intro k; induction' k with k ih <;> intro a c d e
  · exists 0
  · rw [show c + (k + 1) = (c + k) + 1 from by ring,
        show e + (k + 1) = (e + k) + 1 from by ring]
    step fm
    apply stepStar_trans (ih (a + 2) c d e)
    ring_nf; finish

theorem r2r1r1_round : ∀ k, ∀ b c d e,
    ⟨0, b + 2 * k, c + 1, d, e + k⟩ [fm]⊢* ⟨0, b, c + k + 1, d + 2 * k, e⟩ := by
  intro k; induction' k with k ih <;> intro b c d e
  · exists 0
  · rw [show b + 2 * (k + 1) = (b + 2 * k) + 1 + 1 from by ring,
        show e + (k + 1) = (e + k) + 1 from by ring]
    step fm; step fm; step fm
    apply stepStar_trans (ih b (c + 1) (d + 2) e)
    ring_nf; finish

theorem r2_r1_pair : ∀ c d e,
    ⟨0, 1, c + 1, d, e + 1⟩ [fm]⊢* ⟨1, 0, c + 1, d + 1, e⟩ := by
  intro c d e
  step fm; step fm; finish

theorem main_even (m e : ℕ) :
    ⟨2 * m + 1, 0, 0, 2 * m, e⟩ [fm]⊢⁺ ⟨2 * m + 2, 0, 0, 2 * m + 1, e + 2 * m⟩ := by
  rw [show 2 * m + 1 = 0 + (2 * m + 1) from by ring]
  apply step_stepStar_stepPlus
  · show fm ⟨0 + (2 * m + 1), 0, 0, 2 * m, e⟩ = some ⟨0 + (2 * m), 0, 0, 2 * m, e + 2⟩
    simp [fm]
  apply stepStar_trans (r3_chain (2 * m) 0 (2 * m) (e + 2))
  rw [show e + 2 + 2 * (2 * m) = (e + 4 * m + 1) + 1 from by ring,
      show (2 * m : ℕ) = 0 + (2 * m) from by omega]
  apply stepStar_trans (r4_chain (2 * m) 0 0 ((e + 4 * m + 1) + 1))
  rw [show (0 : ℕ) + (2 * m) = 2 * m from by omega]
  step fm
  rw [show 2 * m + 1 = (2 * m) + 1 from by ring]
  step fm
  rw [show 2 * m = 0 + 2 * m from by ring,
      show e + 4 * m + 1 = (e + 3 * m + 1) + m from by ring]
  apply stepStar_trans (r2r1r1_round m 0 0 1 (e + 3 * m + 1))
  rw [show 0 + m + 1 = 0 + (m + 1) from by ring,
      show 1 + 2 * m = 2 * m + 1 from by ring,
      show e + 3 * m + 1 = (e + 2 * m) + (m + 1) from by ring]
  apply stepStar_trans (r2_drain (m + 1) 0 0 (2 * m + 1) (e + 2 * m))
  ring_nf; finish

theorem main_odd (m e : ℕ) :
    ⟨2 * m + 2, 0, 0, 2 * m + 1, e⟩ [fm]⊢⁺ ⟨2 * m + 3, 0, 0, 2 * m + 2, e + 2 * m + 1⟩ := by
  rw [show 2 * m + 2 = 0 + (2 * m + 2) from by ring]
  apply step_stepStar_stepPlus
  · show fm ⟨0 + (2 * m + 2), 0, 0, 2 * m + 1, e⟩ =
         some ⟨0 + (2 * m + 1), 0, 0, 2 * m + 1, e + 2⟩
    simp [fm]
  apply stepStar_trans (r3_chain (2 * m + 1) 0 (2 * m + 1) (e + 2))
  rw [show e + 2 + 2 * (2 * m + 1) = (e + 4 * m + 3) + 1 from by ring,
      show (2 * m + 1 : ℕ) = 0 + (2 * m + 1) from by omega]
  apply stepStar_trans (r4_chain (2 * m + 1) 0 0 ((e + 4 * m + 3) + 1))
  rw [show (0 : ℕ) + (2 * m + 1) = 2 * m + 1 from by omega]
  step fm
  rw [show 2 * m + 1 + 1 = (2 * m + 1) + 1 from by ring]
  step fm
  rw [show 2 * m + 1 = 1 + 2 * m from by ring,
      show e + 4 * m + 3 = (e + 3 * m + 3) + m from by ring]
  apply stepStar_trans (r2r1r1_round m 1 0 1 (e + 3 * m + 3))
  rw [show 0 + m + 1 = m + 1 from by ring,
      show 1 + 2 * m = 2 * m + 1 from by ring,
      show e + 3 * m + 3 = (e + 3 * m + 2) + 1 from by ring]
  apply stepStar_trans (r2_r1_pair m (2 * m + 1) (e + 3 * m + 2))
  rw [show m + 1 = 0 + (m + 1) from by ring,
      show 2 * m + 1 + 1 = 2 * m + 2 from by ring,
      show e + 3 * m + 2 = (e + 2 * m + 1) + (m + 1) from by ring]
  apply stepStar_trans (r2_drain (m + 1) 1 0 (2 * m + 2) (e + 2 * m + 1))
  ring_nf; finish

theorem main_trans (n e : ℕ) :
    ⟨n + 1, 0, 0, n, e⟩ [fm]⊢⁺ ⟨n + 2, 0, 0, n + 1, e + n⟩ := by
  rcases Nat.even_or_odd n with ⟨m, hm⟩ | ⟨m, hm⟩
  · rw [show m + m = 2 * m from by ring] at hm; subst hm
    exact main_even m e
  · subst hm
    rw [show 2 * m + 1 + 1 = 2 * m + 2 from by ring,
        show 2 * m + 1 + 2 = 2 * m + 3 from by ring,
        show e + (2 * m + 1) = e + 2 * m + 1 from by ring]
    exact main_odd m e

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨2, 0, 0, 1, 0⟩) (by execute fm 4)
  apply progress_nonhalt_simple (fm := fm) (A := ℕ × ℕ)
    (fun ⟨n, e⟩ ↦ ⟨n + 1, 0, 0, n, e⟩) ⟨1, 0⟩
  intro ⟨n, e⟩; exact ⟨⟨n + 1, e + n⟩, main_trans n e⟩

end Sz22_2003_unofficial_708
