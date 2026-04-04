import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #1738: [8/15, 33/14, 55/2, 7/11, 9/7]

Vector representation:
```
 3 -1 -1  0  0
-1  1  0 -1  1
-1  0  1  0  1
 0  0  0  1 -1
 0  2  0 -1  0
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_1738

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a, b+1, c+1, d, e⟩ => some ⟨a+3, b, c, d, e⟩
  | ⟨a+1, b, c, d+1, e⟩ => some ⟨a, b+1, c, d, e+1⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b, c+1, d, e+1⟩
  | ⟨a, b, c, d, e+1⟩ => some ⟨a, b, c, d+1, e⟩
  | ⟨a, b, c, d+1, e⟩ => some ⟨a, b+2, c, d, e⟩
  | _ => none

-- R3 chain: (a+k, 0, c, 0, e) ->* (a, 0, c+k, 0, e+k)
theorem r3_chain : ∀ k a c e, ⟨a + k, 0, c, 0, e⟩ [fm]⊢* ⟨a, 0, c + k, 0, e + k⟩ := by
  intro k; induction' k with k ih <;> intro a c e
  · exists 0
  · rw [show a + (k + 1) = a + k + 1 from by ring]
    step fm
    apply stepStar_trans (ih a (c + 1) (e + 1))
    ring_nf; finish

-- R4 chain: (0, 0, c, d, e+k) ->* (0, 0, c, d+k, e)
theorem r4_chain : ∀ k c d e, ⟨0, 0, c, d, e + k⟩ [fm]⊢* ⟨0, 0, c, d + k, e⟩ := by
  intro k; induction' k with k ih <;> intro c d e
  · exists 0
  · rw [show e + (k + 1) = (e + k) + 1 from by ring]
    step fm
    apply stepStar_trans (ih c (d + 1) e)
    ring_nf; finish

-- R2+R1 chain: (a+1, 0, k+1, d+k+1, e) ->* (a+2k+1, 0, 1, d+1, e+k)
theorem r2r1_chain : ∀ k a d e,
    ⟨a + 1, 0, k + 1, d + k + 1, e⟩ [fm]⊢* ⟨a + 2 * k + 1, 0, 1, d + 1, e + k⟩ := by
  intro k; induction' k with k ih <;> intro a d e
  · exists 0
  · rw [show (k + 1) + 1 = k + 1 + 1 from rfl,
        show d + (k + 1) + 1 = d + k + 1 + 1 from by ring]
    step fm
    step fm
    apply stepStar_trans (ih (a + 2) d (e + 1))
    ring_nf; finish

-- R2 drain: (a+k, b, 0, k, e) ->* (a, b+k, 0, 0, e+k)
theorem r2_full_drain : ∀ k a b e,
    ⟨a + k, b, 0, k, e⟩ [fm]⊢* ⟨a, b + k, 0, 0, e + k⟩ := by
  intro k; induction' k with k ih <;> intro a b e
  · exists 0
  · rw [show a + (k + 1) = a + k + 1 from by ring]
    step fm
    apply stepStar_trans (ih a (b + 1) (e + 1))
    ring_nf; finish

-- R3+R1 chain: (a+1, b+k, 0, 0, e) ->* (a+2k+1, b, 0, 0, e+k)
theorem r3r1_chain : ∀ k a b e,
    ⟨a + 1, b + k, 0, 0, e⟩ [fm]⊢* ⟨a + 2 * k + 1, b, 0, 0, e + k⟩ := by
  intro k; induction' k with k ih <;> intro a b e
  · exists 0
  · rw [show b + (k + 1) = b + k + 1 from by ring]
    step fm
    step fm
    apply stepStar_trans (ih (a + 2) b (e + 1))
    ring_nf; finish

-- Canonical: (e+F+3, 0, 0, 0, e) ->+ (3e+2F+9, 0, 0, 0, 3e+F+3)
theorem main_trans (F e : ℕ) : (⟨e + F + 3, 0, 0, 0, e⟩ : Q) [fm]⊢⁺
    ⟨3 * e + 2 * F + 9, 0, 0, 0, 3 * e + F + 3⟩ := by
  rw [show e + F + 3 = 0 + (e + F + 3) from by ring]
  apply stepStar_stepPlus_stepPlus (r3_chain (e + F + 3) 0 0 e)
  rw [show e + (e + F + 3) = 0 + (2 * e + F + 3) from by ring,
      show (0 : ℕ) + (e + F + 3) = e + F + 3 from by ring]
  apply stepStar_stepPlus_stepPlus (r4_chain (2 * e + F + 3) (e + F + 3) 0 0)
  rw [show (0 : ℕ) + (2 * e + F + 3) = 2 * e + F + 3 from by ring,
      show 2 * e + F + 3 = (2 * e + F + 2) + 1 from by ring]
  apply step_stepStar_stepPlus
  · show (0, 0, e + F + 3, (2 * e + F + 2) + 1, 0) [fm]⊢
      (0, 0 + 2, e + F + 3, 2 * e + F + 2, 0); rfl
  rw [show e + F + 3 = (e + F + 2) + 1 from by ring,
      show (0 : ℕ) + 2 = 2 from by ring]
  apply stepStar_trans
  · apply step_stepStar
    show (0, (1 : ℕ) + 1, (e + F + 2) + 1, 2 * e + F + 2, 0) [fm]⊢
      (0 + 3, 1, e + F + 2, 2 * e + F + 2, 0); rfl
  rw [show (0 + 3 : ℕ) = 3 from by ring, show e + F + 2 = (e + F + 1) + 1 from by ring]
  apply stepStar_trans
  · apply step_stepStar
    show (3, (0 : ℕ) + 1, (e + F + 1) + 1, 2 * e + F + 2, 0) [fm]⊢
      (3 + 3, 0, e + F + 1, 2 * e + F + 2, 0); rfl
  rw [show (3 + 3 : ℕ) = 5 + 1 from by ring,
      show e + F + 1 = (e + F) + 1 from by ring,
      show 2 * e + F + 2 = (e + 1) + (e + F) + 1 from by ring]
  apply stepStar_trans (r2r1_chain (e + F) 5 (e + 1) 0)
  rw [show 5 + 2 * (e + F) + 1 = (2 * e + 2 * F + 5) + 1 from by ring,
      show (e + 1) + 1 = (e + 1) + 1 from rfl,
      show (0 : ℕ) + (e + F) = e + F from by ring]
  apply stepStar_trans
  · apply step_stepStar
    show ((2 * e + 2 * F + 5) + 1, 0, 1, (e + 1) + 1, e + F) [fm]⊢
      (2 * e + 2 * F + 5, 0 + 1, 1, e + 1, (e + F) + 1); rfl
  apply stepStar_trans
  · apply step_stepStar
    show (2 * e + 2 * F + 5, (0 : ℕ) + 1, (0 : ℕ) + 1, e + 1, (e + F) + 1) [fm]⊢
      (2 * e + 2 * F + 5 + 3, 0, 0, e + 1, (e + F) + 1); rfl
  rw [show 2 * e + 2 * F + 5 + 3 = (e + 2 * F + 7) + (e + 1) from by ring,
      show (e + F) + 1 = e + F + 1 from by ring]
  apply stepStar_trans (r2_full_drain (e + 1) (e + 2 * F + 7) 0 (e + F + 1))
  rw [show e + 2 * F + 7 = (e + 2 * F + 6) + 1 from by ring,
      show e + F + 1 + (e + 1) = 2 * e + F + 2 from by ring]
  apply stepStar_trans (r3r1_chain (e + 1) (e + 2 * F + 6) 0 (2 * e + F + 2))
  ring_nf; finish

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨5, 0, 0, 0, 1⟩) (by execute fm 6)
  apply progress_nonhalt_simple (fm := fm) (A := ℕ × ℕ)
    (fun ⟨F, e⟩ ↦ ⟨e + F + 3, 0, 0, 0, e⟩) ⟨1, 1⟩
  intro ⟨F, e⟩
  refine ⟨⟨F + 3, 3 * e + F + 3⟩, ?_⟩
  show (⟨e + F + 3, 0, 0, 0, e⟩ : Q) [fm]⊢⁺ ⟨(3 * e + F + 3) + (F + 3) + 3, 0, 0, 0, 3 * e + F + 3⟩
  rw [show (3 * e + F + 3) + (F + 3) + 3 = 3 * e + 2 * F + 9 from by ring]
  exact main_trans F e

end Sz22_2003_unofficial_1738
