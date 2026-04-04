import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #1981: [99/35, 275/6, 2/5, 7/11, 15/2]

Vector representation:
```
 0  2 -1 -1  1
-1 -1  2  0  1
 1  0 -1  0  0
 0  0  0  1 -1
-1  1  1  0  0
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_1981

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a, b, c+1, d+1, e⟩ => some ⟨a, b+2, c, d, e+1⟩
  | ⟨a+1, b+1, c, d, e⟩ => some ⟨a, b, c+2, d, e+1⟩
  | ⟨a, b, c+1, d, e⟩ => some ⟨a+1, b, c, d, e⟩
  | ⟨a, b, c, d, e+1⟩ => some ⟨a, b, c, d+1, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b+1, c+1, d, e⟩
  | _ => none

theorem r3_chain : ∀ k a c e, ⟨a, 0, c + k, 0, e⟩ [fm]⊢* ⟨a + k, 0, c, 0, e⟩ := by
  intro k; induction' k with k ih <;> intro a c e
  · exists 0
  · rw [show c + (k + 1) = (c + k) + 1 from by ring]
    step fm; apply stepStar_trans (ih (a + 1) c e); ring_nf; finish

theorem r4_chain : ∀ k a d e, ⟨a, 0, 0, d, e + k⟩ [fm]⊢* ⟨a, 0, 0, d + k, e⟩ := by
  intro k; induction' k with k ih <;> intro a d e
  · exists 0
  · rw [show e + (k + 1) = (e + k) + 1 from by ring]
    step fm; apply stepStar_trans (ih a (d + 1) e); ring_nf; finish

theorem r2r1x2_loop : ∀ k a b d e, ⟨a + k, b + 1, 0, d + 2 * k, e⟩ [fm]⊢*
    ⟨a, b + 1 + 3 * k, 0, d, e + 3 * k⟩ := by
  intro k; induction' k with k ih <;> intro a b d e
  · exists 0
  · rw [show a + (k + 1) = (a + k) + 1 from by ring,
        show d + 2 * (k + 1) = (d + 2 * k) + 2 from by ring]
    step fm; step fm; step fm
    apply stepStar_trans (ih a (b + 3) d (e + 3)); ring_nf; finish

theorem r2_drain : ∀ k a b c e, ⟨a + k, b + k, c, 0, e⟩ [fm]⊢*
    ⟨a, b, c + 2 * k, 0, e + k⟩ := by
  intro k; induction' k with k ih <;> intro a b c e
  · exists 0
  · rw [show a + (k + 1) = (a + k) + 1 from by ring,
        show b + (k + 1) = (b + k) + 1 from by ring]
    step fm; apply stepStar_trans (ih a b (c + 2) (e + 1)); ring_nf; finish

theorem r32_alt : ∀ k b c e, ⟨0, b + k, c + 1, 0, e⟩ [fm]⊢*
    ⟨0, b, c + 1 + k, 0, e + k⟩ := by
  intro k; induction' k with k ih <;> intro b c e
  · exists 0
  · rw [show b + (k + 1) = (b + k) + 1 from by ring]
    step fm; step fm
    apply stepStar_trans (ih b (c + 1) (e + 1)); ring_nf; finish

theorem trans_odd (j A : ℕ) (hA1 : j ≤ A) (hA2 : A ≤ 4 * j) :
    ⟨A + 2, 0, 0, 2 * j + 1, 0⟩ [fm]⊢⁺ ⟨A + 2 * j + 4, 0, 0, 6 * j + 4, 0⟩ := by
  step fm; step fm
  show ⟨A + 1, 3, 0, 2 * j, 1⟩ [fm]⊢* _
  rw [show A + 1 = (A + 1 - j) + j from by omega,
      show (3 : ℕ) = 2 + 1 from by ring,
      show 2 * j = 0 + 2 * j from by ring]
  apply stepStar_trans (r2r1x2_loop j (A + 1 - j) 2 0 1)
  rw [show 2 + 1 + 3 * j = 2 + 1 + 3 * j from rfl]
  show ⟨A + 1 - j, 3 + 3 * j, 0, 0, 1 + 3 * j⟩ [fm]⊢* _
  rw [show A + 1 - j = 0 + (A + 1 - j) from by omega,
      show 3 + 3 * j = (4 * j + 2 - A) + (A + 1 - j) from by omega]
  apply stepStar_trans (r2_drain (A + 1 - j) 0 (4 * j + 2 - A) 0 (1 + 3 * j))
  rw [show 0 + 2 * (A + 1 - j) = (2 * A - 2 * j + 1) + 1 from by omega,
      show (4 * j + 2 - A : ℕ) = 0 + (4 * j + 2 - A) from by omega]
  apply stepStar_trans (r32_alt (4 * j + 2 - A) 0 (2 * A - 2 * j + 1)
    (1 + 3 * j + (A + 1 - j)))
  rw [show (2 * A - 2 * j + 1) + 1 + (4 * j + 2 - A) = A + 2 * j + 4 from by omega,
      show 1 + 3 * j + (A + 1 - j) + (4 * j + 2 - A) = 6 * j + 4 from by omega]
  rw [show (A + 2 * j + 4 : ℕ) = 0 + (A + 2 * j + 4) from by omega]
  apply stepStar_trans (r3_chain (A + 2 * j + 4) 0 0 (6 * j + 4))
  rw [show 0 + (A + 2 * j + 4) = A + 2 * j + 4 from by ring,
      show (6 * j + 4 : ℕ) = 0 + (6 * j + 4) from by ring]
  apply stepStar_trans (r4_chain (6 * j + 4) (A + 2 * j + 4) 0 0)
  ring_nf; finish

theorem trans_even (j A : ℕ) (hA1 : j ≤ A) (hA2 : A ≤ 4 * j + 2) :
    ⟨A + 2, 0, 0, 2 * j + 2, 0⟩ [fm]⊢⁺ ⟨A + 2 * j + 5, 0, 0, 6 * j + 7, 0⟩ := by
  step fm; step fm
  show ⟨A + 1, 3, 0, 2 * j + 1, 1⟩ [fm]⊢* _
  rw [show A + 1 = (A + 1 - j) + j from by omega,
      show (3 : ℕ) = 2 + 1 from by ring,
      show 2 * j + 1 = 1 + 2 * j from by ring]
  apply stepStar_trans (r2r1x2_loop j (A + 1 - j) 2 1 1)
  show ⟨A + 1 - j, 3 + 3 * j, 0, 1, 1 + 3 * j⟩ [fm]⊢* _
  rw [show A + 1 - j = (A - j) + 1 from by omega,
      show 3 + 3 * j = (2 + 3 * j) + 1 from by ring]
  step fm; step fm
  rw [show 2 + 3 * j + 2 = 4 + 3 * j from by ring,
      show 1 + 3 * j + 1 + 1 = 3 + 3 * j from by ring]
  show ⟨A - j, 4 + 3 * j, 1, 0, 3 + 3 * j⟩ [fm]⊢* _
  rw [show A - j = 0 + (A - j) from by omega,
      show 4 + 3 * j = (4 + 4 * j - A) + (A - j) from by omega]
  apply stepStar_trans (r2_drain (A - j) 0 (4 + 4 * j - A) 1 (3 + 3 * j))
  rw [show 1 + 2 * (A - j) = (2 * A - 2 * j) + 1 from by omega,
      show (4 + 4 * j - A : ℕ) = 0 + (4 + 4 * j - A) from by omega]
  apply stepStar_trans (r32_alt (4 + 4 * j - A) 0 (2 * A - 2 * j)
    (3 + 3 * j + (A - j)))
  rw [show (2 * A - 2 * j) + 1 + (4 + 4 * j - A) = A + 2 * j + 5 from by omega,
      show 3 + 3 * j + (A - j) + (4 + 4 * j - A) = 6 * j + 7 from by omega]
  rw [show (A + 2 * j + 5 : ℕ) = 0 + (A + 2 * j + 5) from by omega]
  apply stepStar_trans (r3_chain (A + 2 * j + 5) 0 0 (6 * j + 7))
  rw [show 0 + (A + 2 * j + 5) = A + 2 * j + 5 from by ring,
      show (6 * j + 7 : ℕ) = 0 + (6 * j + 7) from by ring]
  apply stepStar_trans (r4_chain (6 * j + 7) (A + 2 * j + 5) 0 0)
  ring_nf; finish

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨2, 0, 0, 1, 0⟩) (by execute fm 6)
  apply progress_nonhalt (fm := fm)
    (P := fun q ↦ ∃ a d, q = ⟨a, 0, 0, d, 0⟩ ∧ d ≥ 1 ∧ a ≥ 2 ∧ d + 2 ≤ 2 * a ∧ a ≤ 2 * d)
  · intro c ⟨a, d, hq, hd, ha, had1, had2⟩; subst hq
    refine ⟨⟨a + d + 1, 0, 0, 3 * d + 1, 0⟩,
            ⟨a + d + 1, 3 * d + 1, rfl, by omega, by omega, by omega, by omega⟩, ?_⟩
    obtain ⟨A, rfl⟩ : ∃ A, a = A + 2 := ⟨a - 2, by omega⟩
    rcases Nat.even_or_odd d with ⟨j, hj⟩ | ⟨j, hj⟩
    · -- d even: d = 2j
      rw [show j + j = 2 * j from by ring] at hj; subst hj
      -- d = 2j, need d >= 1 so j >= 1
      obtain ⟨j, rfl⟩ : ∃ j', j = j' + 1 := ⟨j - 1, by omega⟩
      rw [show 2 * (j + 1) = 2 * j + 2 from by ring]
      rw [show A + 2 + (2 * j + 2) + 1 = A + 2 * j + 5 from by ring,
          show 3 * (2 * j + 2) + 1 = 6 * j + 7 from by ring]
      exact trans_even j A (by omega) (by omega)
    · -- d odd: d = 2j+1
      subst hj
      show ⟨A + 2, 0, 0, 2 * j + 1, 0⟩ [fm]⊢⁺ _
      rw [show A + 2 + (2 * j + 1) + 1 = A + 2 * j + 4 from by ring,
          show 3 * (2 * j + 1) + 1 = 6 * j + 4 from by ring]
      exact trans_odd j A (by omega) (by omega)
  · exact ⟨2, 1, rfl, by omega, by omega, by omega, by omega⟩
