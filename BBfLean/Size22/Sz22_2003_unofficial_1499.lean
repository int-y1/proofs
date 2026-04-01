import BBfLean.FM
import Mathlib.Tactic.Ring
import Mathlib.Tactic.IntervalCases

/-!
# sz22_2003_unofficial #1499: [7/15, 9/77, 242/3, 5/11, 539/2]

Vector representation:
```
 0 -1 -1  1  0
 0  2  0 -1 -1
 1 -1  0  0  2
 0  0  1  0 -1
-1  0  0  2  1
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_1499

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a, b+1, c+1, d, e⟩ => some ⟨a, b, c, d+1, e⟩
  | ⟨a, b, c, d+1, e+1⟩ => some ⟨a, b+2, c, d, e⟩
  | ⟨a, b+1, c, d, e⟩ => some ⟨a+1, b, c, d, e+2⟩
  | ⟨a, b, c, d, e+1⟩ => some ⟨a, b, c+1, d, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b, c, d+2, e+1⟩
  | _ => none

-- R4 chain: transfer e to c.
theorem e_to_c : ∀ k, ∀ a c, ⟨a, 0, c, 0, e + k⟩ [fm]⊢* ⟨a, 0, c + k, 0, e⟩ := by
  intro k; induction' k with k ih
  · intro a c; exists 0
  · intro a c; rw [Nat.add_succ]; step fm
    apply stepStar_trans (ih a (c + 1)); ring_nf; finish

-- R5, R2, R1, R1 chain: drain a and c, build d.
theorem drain_ac : ∀ k, ∀ a c D, ⟨a + k, 0, c + 2 * k, D, 0⟩ [fm]⊢* ⟨a, 0, c, D + 3 * k, 0⟩ := by
  intro k; induction' k with k ih <;> intro a c D
  · exists 0
  · rw [show a + (k + 1) = (a + k) + 1 from by ring,
        show c + 2 * (k + 1) = (c + 2 * k) + 1 + 1 from by ring]
    step fm; step fm; step fm; step fm
    apply stepStar_trans (ih a c (D + 3))
    ring_nf; finish

-- Odd c ending: (a+1, 0, 1, D, 0) -> (a+1, 4, 0, D, 0)
theorem odd_ending (a D : ℕ) :
    ⟨a + 1, 0, 1, D, 0⟩ [fm]⊢* ⟨a + 1, 4, 0, D, 0⟩ := by
  step fm; step fm; step fm; step fm; step fm; step fm; finish

-- Even c ending: (a+1, 0, 0, D+1, 0) -> (a+1, 5, 0, D, 0)
theorem even_ending (a D : ℕ) :
    ⟨a + 1, 0, 0, D + 1, 0⟩ [fm]⊢* ⟨a + 1, 5, 0, D, 0⟩ := by
  step fm; step fm; step fm; step fm; step fm; finish

-- R3, R2, R2 chain.
theorem r3r2r2_chain : ∀ k, ∀ A B D, ⟨A, B + 1, 0, D + 2 * k, 0⟩ [fm]⊢* ⟨A + k, B + 3 * k + 1, 0, D, 0⟩ := by
  intro k; induction' k with k ih <;> intro A B D
  · exists 0
  · rw [show D + 2 * (k + 1) = (D + 2 * k) + 2 from by ring]
    step fm; step fm; step fm
    apply stepStar_trans (ih (A + 1) (B + 3) D)
    ring_nf; finish

-- R3 drain.
theorem r3_drain : ∀ k, ∀ A B E, ⟨A, B + k, 0, 0, E⟩ [fm]⊢* ⟨A + k, B, 0, 0, E + 2 * k⟩ := by
  intro k; induction' k with k ih <;> intro A B E
  · exists 0
  · rw [show B + (k + 1) = (B + k) + 1 from by ring]
    step fm
    apply stepStar_trans (ih (A + 1) B (E + 2))
    ring_nf; finish

-- d=1 ending: (A, B+1, 0, 1, 0) -> (A+B+3, 0, 0, 0, 2*B+5)
theorem d1_ending (A B : ℕ) :
    ⟨A, B + 1, 0, 1, 0⟩ [fm]⊢* ⟨A + B + 3, 0, 0, 0, 2 * B + 5⟩ := by
  step fm; step fm; step fm
  rw [show B + 1 = 0 + (B + 1) from by ring,
      show (3 : ℕ) = 0 + 2 * 0 + 3 from by ring]
  apply stepStar_trans (r3_drain (B + 1) (A + 2) 0 3)
  ring_nf; finish

-- d=0 ending (R3 drain): (A, B+1, 0, 0, 0) -> (A+B+1, 0, 0, 0, 2*B+2)
theorem d0_ending (A B : ℕ) :
    ⟨A, B + 1, 0, 0, 0⟩ [fm]⊢* ⟨A + B + 1, 0, 0, 0, 2 * B + 2⟩ := by
  rw [show B + 1 = 0 + (B + 1) from by ring,
      show (0 : ℕ) = 0 + 2 * 0 from by ring]
  apply stepStar_trans (r3_drain (B + 1) A 0 0)
  ring_nf; finish

-- Full transition for e ≡ 1 mod 4.
theorem trans_e1 (F j : ℕ) :
    ⟨F + 2 * j + 1, 0, 0, 0, 4 * j + 1⟩ [fm]⊢⁺ ⟨F + 12 * j + 5, 0, 0, 0, 18 * j + 8⟩ := by
  step fm
  -- State: (F+2j+1, 0, 1, 0, 4j). Transfer remaining e to c via e_to_c.
  have h1 := e_to_c (4 * j) (F + 2 * j + 1) 1 (e := 0)
  rw [show (0 : ℕ) + (4 * j) = 4 * j from by ring] at h1
  apply stepStar_trans h1
  rw [show 1 + 4 * j = 1 + 2 * (2 * j) from by ring,
      show F + 2 * j + 1 = (F + 1) + 2 * j from by ring]
  apply stepStar_trans (drain_ac (2 * j) (F + 1) 1 0)
  rw [show 0 + 3 * (2 * j) = 6 * j from by ring]
  apply stepStar_trans (odd_ending F (6 * j))
  rw [show 6 * j = 0 + 2 * (3 * j) from by ring]
  apply stepStar_trans (r3r2r2_chain (3 * j) (F + 1) 3 0)
  rw [show F + 1 + 3 * j = F + 3 * j + 1 from by ring,
      show 3 + 3 * (3 * j) + 1 = (9 * j + 3) + 1 from by ring]
  apply stepStar_trans (d0_ending (F + 3 * j + 1) (9 * j + 3))
  ring_nf; finish

-- Full transition for e ≡ 3 mod 4.
theorem trans_e3 (F j : ℕ) :
    ⟨F + 2 * j + 2, 0, 0, 0, 4 * j + 3⟩ [fm]⊢⁺ ⟨F + 12 * j + 11, 0, 0, 0, 18 * j + 17⟩ := by
  step fm
  have h1 := e_to_c (4 * j + 2) (F + 2 * j + 2) 1 (e := 0)
  rw [show (0 : ℕ) + (4 * j + 2) = 4 * j + 2 from by ring] at h1
  apply stepStar_trans h1
  rw [show 1 + (4 * j + 2) = 1 + 2 * (2 * j + 1) from by ring,
      show F + 2 * j + 2 = (F + 1) + (2 * j + 1) from by ring]
  apply stepStar_trans (drain_ac (2 * j + 1) (F + 1) 1 0)
  rw [show 0 + 3 * (2 * j + 1) = 6 * j + 3 from by ring]
  apply stepStar_trans (odd_ending F (6 * j + 3))
  rw [show 6 * j + 3 = 1 + 2 * (3 * j + 1) from by ring]
  apply stepStar_trans (r3r2r2_chain (3 * j + 1) (F + 1) 3 1)
  rw [show F + 1 + (3 * j + 1) = F + 3 * j + 2 from by ring,
      show 3 + 3 * (3 * j + 1) + 1 = (9 * j + 6) + 1 from by ring]
  apply stepStar_trans (d1_ending (F + 3 * j + 2) (9 * j + 6))
  ring_nf; finish

-- Full transition for e ≡ 0 mod 4 (e = 4j+4).
theorem trans_e0 (F j : ℕ) :
    ⟨F + 2 * j + 3, 0, 0, 0, 4 * j + 4⟩ [fm]⊢⁺ ⟨F + 12 * j + 16, 0, 0, 0, 18 * j + 25⟩ := by
  step fm
  have h1 := e_to_c (4 * j + 3) (F + 2 * j + 3) 1 (e := 0)
  rw [show (0 : ℕ) + (4 * j + 3) = 4 * j + 3 from by ring] at h1
  apply stepStar_trans h1
  rw [show 1 + (4 * j + 3) = 0 + 2 * (2 * j + 2) from by ring,
      show F + 2 * j + 3 = (F + 1) + (2 * j + 2) from by ring]
  apply stepStar_trans (drain_ac (2 * j + 2) (F + 1) 0 0)
  rw [show 0 + 3 * (2 * j + 2) = (6 * j + 5) + 1 from by ring]
  apply stepStar_trans (even_ending F (6 * j + 5))
  rw [show 6 * j + 5 = 1 + 2 * (3 * j + 2) from by ring]
  apply stepStar_trans (r3r2r2_chain (3 * j + 2) (F + 1) 4 1)
  rw [show F + 1 + (3 * j + 2) = F + 3 * j + 3 from by ring,
      show 4 + 3 * (3 * j + 2) + 1 = (9 * j + 10) + 1 from by ring]
  apply stepStar_trans (d1_ending (F + 3 * j + 3) (9 * j + 10))
  ring_nf; finish

-- Full transition for e ≡ 2 mod 4 (e = 4j+2).
theorem trans_e2 (F j : ℕ) :
    ⟨F + 2 * j + 2, 0, 0, 0, 4 * j + 2⟩ [fm]⊢⁺ ⟨F + 12 * j + 10, 0, 0, 0, 18 * j + 16⟩ := by
  step fm
  have h1 := e_to_c (4 * j + 1) (F + 2 * j + 2) 1 (e := 0)
  rw [show (0 : ℕ) + (4 * j + 1) = 4 * j + 1 from by ring] at h1
  apply stepStar_trans h1
  rw [show 1 + (4 * j + 1) = 0 + 2 * (2 * j + 1) from by ring,
      show F + 2 * j + 2 = (F + 1) + (2 * j + 1) from by ring]
  apply stepStar_trans (drain_ac (2 * j + 1) (F + 1) 0 0)
  rw [show 0 + 3 * (2 * j + 1) = (6 * j + 2) + 1 from by ring]
  apply stepStar_trans (even_ending F (6 * j + 2))
  rw [show 6 * j + 2 = 0 + 2 * (3 * j + 1) from by ring]
  apply stepStar_trans (r3r2r2_chain (3 * j + 1) (F + 1) 4 0)
  rw [show F + 1 + (3 * j + 1) = F + 3 * j + 2 from by ring,
      show 4 + 3 * (3 * j + 1) + 1 = (9 * j + 7) + 1 from by ring]
  apply stepStar_trans (d0_ending (F + 3 * j + 2) (9 * j + 7))
  ring_nf; finish

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨4, 0, 0, 0, 7⟩)
  · execute fm 7
  apply progress_nonhalt (fm := fm)
    (P := fun q ↦ ∃ a e, q = ⟨a, 0, 0, 0, e⟩ ∧ e ≥ 1 ∧ 2 * a ≥ e + 1)
  · intro q ⟨a, e, hq, he1, hinv⟩; subst hq
    have h4 : e % 4 < 4 := Nat.mod_lt _ (by omega)
    obtain ⟨k, hk⟩ : ∃ k, e = 4 * k + e % 4 := ⟨e / 4, by omega⟩
    interval_cases (e % 4)
    · -- e ≡ 0 (mod 4): e = 4*k, k >= 1
      rw [Nat.add_zero] at hk; subst hk
      obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
      obtain ⟨F, rfl⟩ : ∃ F, a = F + 2 * k' + 3 := ⟨a - 2 * k' - 3, by omega⟩
      exact ⟨⟨F + 12 * k' + 16, 0, 0, 0, 18 * k' + 25⟩,
        ⟨F + 12 * k' + 16, 18 * k' + 25, by ring_nf, by omega, by omega⟩,
        trans_e0 F k'⟩
    · -- e ≡ 1 (mod 4): e = 4*k+1
      subst hk
      obtain ⟨F, rfl⟩ : ∃ F, a = F + 2 * k + 1 := ⟨a - 2 * k - 1, by omega⟩
      exact ⟨⟨F + 12 * k + 5, 0, 0, 0, 18 * k + 8⟩,
        ⟨F + 12 * k + 5, 18 * k + 8, by ring_nf, by omega, by omega⟩,
        trans_e1 F k⟩
    · -- e ≡ 2 (mod 4): e = 4*k+2
      subst hk
      obtain ⟨F, rfl⟩ : ∃ F, a = F + 2 * k + 2 := ⟨a - 2 * k - 2, by omega⟩
      exact ⟨⟨F + 12 * k + 10, 0, 0, 0, 18 * k + 16⟩,
        ⟨F + 12 * k + 10, 18 * k + 16, by ring_nf, by omega, by omega⟩,
        trans_e2 F k⟩
    · -- e ≡ 3 (mod 4): e = 4*k+3
      subst hk
      obtain ⟨F, rfl⟩ : ∃ F, a = F + 2 * k + 2 := ⟨a - 2 * k - 2, by omega⟩
      exact ⟨⟨F + 12 * k + 11, 0, 0, 0, 18 * k + 17⟩,
        ⟨F + 12 * k + 11, 18 * k + 17, by ring_nf, by omega, by omega⟩,
        trans_e3 F k⟩
  · exact ⟨4, 7, by ring_nf, by omega, by omega⟩

end Sz22_2003_unofficial_1499
