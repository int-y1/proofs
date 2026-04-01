import BBfLean.FM
import Mathlib.Tactic.Ring
import Mathlib.Tactic.IntervalCases

/-!
# sz22_2003_unofficial #1498: [7/15, 9/77, 242/3, 5/11, 363/2]

Vector representation:
```
 0 -1 -1  1  0
 0  2  0 -1 -1
 1 -1  0  0  2
 0  0  1  0 -1
-1  1  0  0  2
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_1498

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a, b+1, c+1, d, e⟩ => some ⟨a, b, c, d+1, e⟩
  | ⟨a, b, c, d+1, e+1⟩ => some ⟨a, b+2, c, d, e⟩
  | ⟨a, b+1, c, d, e⟩ => some ⟨a+1, b, c, d, e+2⟩
  | ⟨a, b, c, d, e+1⟩ => some ⟨a, b, c+1, d, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b+1, c, d, e+2⟩
  | _ => none

theorem e_to_c : ∀ k, ∀ a c, (⟨a, 0, c, 0, e + k⟩ : Q) [fm]⊢* ⟨a, 0, c + k, 0, e⟩ := by
  intro k; induction' k with k ih
  · intro a c; exists 0
  · intro a c; rw [Nat.add_succ]; step fm
    apply stepStar_trans (ih a (c + 1)); ring_nf; finish

theorem drain : ∀ k, ∀ a c D, (⟨a + k, 0, c + 5 * k, D, 0⟩ : Q) [fm]⊢* ⟨a, 0, c, D + 3 * k, 0⟩ := by
  intro k; induction' k with k ih <;> intro a c D
  · exists 0
  · rw [show a + (k + 1) = (a + k) + 1 from by ring,
        show c + 5 * (k + 1) = (c + 5 * k) + 5 from by ring]
    step fm; step fm; step fm; step fm; step fm; step fm; step fm; step fm
    apply stepStar_trans (ih a c (D + 3)); ring_nf; finish

theorem sdrain4 : ∀ a d, (⟨a + 1, 0, 4, d, 0⟩ : Q) [fm]⊢* ⟨a, 1, 0, d + 2, 0⟩ := by
  intro a d; step fm; step fm; step fm; step fm; step fm; step fm; step fm; finish

theorem sdrain3 : ∀ a d, (⟨a + 1, 0, 3, d, 0⟩ : Q) [fm]⊢* ⟨a, 2, 0, d + 1, 0⟩ := by
  intro a d; step fm; step fm; step fm; step fm; step fm; step fm; finish

theorem sdrain2 : ∀ a d, (⟨a + 1, 0, 2, d, 0⟩ : Q) [fm]⊢* ⟨a, 3, 0, d, 0⟩ := by
  intro a d; step fm; step fm; step fm; step fm; step fm; finish

theorem sdrain1 : ∀ a d, (⟨a + 1, 0, 1, d + 1, 0⟩ : Q) [fm]⊢* ⟨a, 4, 0, d, 0⟩ := by
  intro a d; step fm; step fm; step fm; step fm; finish

theorem sdrain0 : ∀ a d, (⟨a + 1, 0, 0, d + 2, 0⟩ : Q) [fm]⊢* ⟨a, 5, 0, d, 0⟩ := by
  intro a d; step fm; step fm; step fm; finish

theorem r3r2r2 : ∀ k, ∀ A B D, (⟨A, B + 1, 0, D + 2 * k, 0⟩ : Q) [fm]⊢* ⟨A + k, B + 3 * k + 1, 0, D, 0⟩ := by
  intro k; induction' k with k ih <;> intro A B D
  · exists 0
  · rw [show D + 2 * (k + 1) = (D + 2 * k) + 2 from by ring]
    step fm; step fm; step fm
    apply stepStar_trans (ih (A + 1) (B + 3) D); ring_nf; finish

theorem r3_drain : ∀ k, ∀ A E, (⟨A, k, 0, 0, E⟩ : Q) [fm]⊢* ⟨A + k, 0, 0, 0, E + 2 * k⟩ := by
  intro k; induction' k with k ih <;> intro A E
  · exists 0
  · rw [show k + 1 = k + 1 from rfl]; step fm
    apply stepStar_trans (ih (A + 1) (E + 2)); ring_nf; finish

theorem trans_e4 (F L : ℕ) :
    (⟨F + 2 * L + 1, 0, 0, 0, 10 * L + 4⟩ : Q) [fm]⊢⁺
    ⟨F + 12 * L + 5, 0, 0, 0, 18 * L + 8⟩ := by
  rw [show (10 * L + 4 : ℕ) = (10 * L + 3) + 1 from by ring]
  step fm
  rw [show (10 * L + 3 : ℕ) = 0 + (10 * L + 3) from by ring]
  apply stepStar_trans (e_to_c (10 * L + 3) (F + 2 * L + 1) 1 (e := 0))
  rw [show 1 + (10 * L + 3) = 10 * L + 4 from by ring,
      show F + 2 * L + 1 = (F + 1) + 2 * L from by ring,
      show 10 * L + 4 = 4 + 5 * (2 * L) from by ring]
  apply stepStar_trans (drain (2 * L) (F + 1) 4 0)
  rw [show 0 + 3 * (2 * L) = 6 * L from by ring]
  apply stepStar_trans (sdrain4 F (6 * L))
  rw [show 6 * L + 2 = 0 + 2 * (3 * L + 1) from by ring,
      show (1 : ℕ) = 0 + 1 from by ring]
  apply stepStar_trans (r3r2r2 (3 * L + 1) F 0 0)
  rw [show F + (3 * L + 1) = F + 3 * L + 1 from by ring,
      show 0 + 3 * (3 * L + 1) + 1 = 9 * L + 4 from by ring]
  apply stepStar_trans (r3_drain (9 * L + 4) (F + 3 * L + 1) 0)
  ring_nf; finish

theorem trans_e8 (F L : ℕ) :
    (⟨F + 2 * L + 2, 0, 0, 0, 10 * L + 8⟩ : Q) [fm]⊢⁺
    ⟨F + 12 * L + 10, 0, 0, 0, 18 * L + 16⟩ := by
  rw [show (10 * L + 8 : ℕ) = (10 * L + 7) + 1 from by ring]
  step fm
  rw [show (10 * L + 7 : ℕ) = 0 + (10 * L + 7) from by ring]
  apply stepStar_trans (e_to_c (10 * L + 7) (F + 2 * L + 2) 1 (e := 0))
  rw [show 1 + (10 * L + 7) = 10 * L + 8 from by ring,
      show F + 2 * L + 2 = (F + 1) + (2 * L + 1) from by ring,
      show 10 * L + 8 = 3 + 5 * (2 * L + 1) from by ring]
  apply stepStar_trans (drain (2 * L + 1) (F + 1) 3 0)
  rw [show 0 + 3 * (2 * L + 1) = 6 * L + 3 from by ring]
  apply stepStar_trans (sdrain3 F (6 * L + 3))
  rw [show 6 * L + 3 + 1 = 0 + 2 * (3 * L + 2) from by ring,
      show (2 : ℕ) = 1 + 1 from by ring]
  apply stepStar_trans (r3r2r2 (3 * L + 2) F 1 0)
  rw [show F + (3 * L + 2) = F + 3 * L + 2 from by ring,
      show 1 + 3 * (3 * L + 2) + 1 = 9 * L + 8 from by ring]
  apply stepStar_trans (r3_drain (9 * L + 8) (F + 3 * L + 2) 0)
  ring_nf; finish

theorem trans_e6 (F L : ℕ) :
    (⟨F + 2 * L + 2, 0, 0, 0, 10 * L + 6⟩ : Q) [fm]⊢⁺
    ⟨F + 12 * L + 8, 0, 0, 0, 18 * L + 14⟩ := by
  rw [show (10 * L + 6 : ℕ) = (10 * L + 5) + 1 from by ring]
  step fm
  rw [show (10 * L + 5 : ℕ) = 0 + (10 * L + 5) from by ring]
  apply stepStar_trans (e_to_c (10 * L + 5) (F + 2 * L + 2) 1 (e := 0))
  rw [show 1 + (10 * L + 5) = 10 * L + 6 from by ring,
      show F + 2 * L + 2 = (F + 1) + (2 * L + 1) from by ring,
      show 10 * L + 6 = 1 + 5 * (2 * L + 1) from by ring]
  apply stepStar_trans (drain (2 * L + 1) (F + 1) 1 0)
  rw [show 0 + 3 * (2 * L + 1) = 6 * L + 3 from by ring,
      show 6 * L + 3 = (6 * L + 2) + 1 from by ring]
  apply stepStar_trans (sdrain1 F (6 * L + 2))
  rw [show 6 * L + 2 = 0 + 2 * (3 * L + 1) from by ring,
      show (4 : ℕ) = 3 + 1 from by ring]
  apply stepStar_trans (r3r2r2 (3 * L + 1) F 3 0)
  rw [show F + (3 * L + 1) = F + 3 * L + 1 from by ring,
      show 3 + 3 * (3 * L + 1) + 1 = 9 * L + 7 from by ring]
  apply stepStar_trans (r3_drain (9 * L + 7) (F + 3 * L + 1) 0)
  ring_nf; finish

theorem trans_e2 (F L : ℕ) :
    (⟨F + 2 * L + 1, 0, 0, 0, 10 * L + 2⟩ : Q) [fm]⊢⁺
    ⟨F + 12 * L + 3, 0, 0, 0, 18 * L + 6⟩ := by
  rw [show (10 * L + 2 : ℕ) = (10 * L + 1) + 1 from by ring]
  step fm
  rw [show (10 * L + 1 : ℕ) = 0 + (10 * L + 1) from by ring]
  apply stepStar_trans (e_to_c (10 * L + 1) (F + 2 * L + 1) 1 (e := 0))
  rw [show 1 + (10 * L + 1) = 10 * L + 2 from by ring,
      show F + 2 * L + 1 = (F + 1) + 2 * L from by ring,
      show 10 * L + 2 = 2 + 5 * (2 * L) from by ring]
  apply stepStar_trans (drain (2 * L) (F + 1) 2 0)
  rw [show 0 + 3 * (2 * L) = 6 * L from by ring]
  apply stepStar_trans (sdrain2 F (6 * L))
  rw [show 6 * L = 0 + 2 * (3 * L) from by ring,
      show (3 : ℕ) = 2 + 1 from by ring]
  apply stepStar_trans (r3r2r2 (3 * L) F 2 0)
  rw [show F + 3 * L = F + 3 * L from rfl,
      show 2 + 3 * (3 * L) + 1 = 9 * L + 3 from by ring]
  apply stepStar_trans (r3_drain (9 * L + 3) (F + 3 * L) 0)
  ring_nf; finish

theorem trans_e0 (F L : ℕ) :
    (⟨F + 2 * L + 3, 0, 0, 0, 10 * L + 10⟩ : Q) [fm]⊢⁺
    ⟨F + 12 * L + 13, 0, 0, 0, 18 * L + 22⟩ := by
  rw [show (10 * L + 10 : ℕ) = (10 * L + 9) + 1 from by ring]
  step fm
  rw [show (10 * L + 9 : ℕ) = 0 + (10 * L + 9) from by ring]
  apply stepStar_trans (e_to_c (10 * L + 9) (F + 2 * L + 3) 1 (e := 0))
  rw [show 1 + (10 * L + 9) = 10 * L + 10 from by ring,
      show F + 2 * L + 3 = (F + 1) + (2 * L + 2) from by ring,
      show 10 * L + 10 = 0 + 5 * (2 * L + 2) from by ring]
  apply stepStar_trans (drain (2 * L + 2) (F + 1) 0 0)
  rw [show 0 + 3 * (2 * L + 2) = 6 * L + 6 from by ring,
      show 6 * L + 6 = (6 * L + 4) + 2 from by ring]
  apply stepStar_trans (sdrain0 F (6 * L + 4))
  rw [show 6 * L + 4 = 0 + 2 * (3 * L + 2) from by ring,
      show (5 : ℕ) = 4 + 1 from by ring]
  apply stepStar_trans (r3r2r2 (3 * L + 2) F 4 0)
  rw [show F + (3 * L + 2) = F + 3 * L + 2 from by ring,
      show 4 + 3 * (3 * L + 2) + 1 = 9 * L + 11 from by ring]
  apply stepStar_trans (r3_drain (9 * L + 11) (F + 3 * L + 2) 0)
  ring_nf; finish

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨5, 0, 0, 0, 8⟩) (by execute fm 20)
  apply progress_nonhalt (fm := fm)
    (P := fun q ↦ ∃ a k, q = ⟨a, 0, 0, 0, 2 * k + 2⟩ ∧ 2 * a ≥ 2 * k + 4)
  · intro q ⟨a, k, hq, hinv⟩; subst hq
    have h5 : k % 5 < 5 := Nat.mod_lt _ (by omega)
    obtain ⟨L, hL⟩ : ∃ L, k = 5 * L + k % 5 := ⟨k / 5, by omega⟩
    interval_cases (k % 5)
    · -- k ≡ 0: e = 10L+2
      obtain ⟨F, rfl⟩ : ∃ F, a = F + 2 * L + 1 := ⟨a - 2 * L - 1, by omega⟩
      exact ⟨⟨F + 12 * L + 3, 0, 0, 0, 18 * L + 6⟩,
        ⟨F + 12 * L + 3, 9 * L + 2, by ring_nf, by omega⟩,
        by rw [show 2 * k + 2 = 10 * L + 2 from by omega]; exact trans_e2 F L⟩
    · -- k ≡ 1: e = 10L+4
      obtain ⟨F, rfl⟩ : ∃ F, a = F + 2 * L + 1 := ⟨a - 2 * L - 1, by omega⟩
      exact ⟨⟨F + 12 * L + 5, 0, 0, 0, 18 * L + 8⟩,
        ⟨F + 12 * L + 5, 9 * L + 3, by ring_nf, by omega⟩,
        by rw [show 2 * k + 2 = 10 * L + 4 from by omega]; exact trans_e4 F L⟩
    · -- k ≡ 2: e = 10L+6
      obtain ⟨F, rfl⟩ : ∃ F, a = F + 2 * L + 2 := ⟨a - 2 * L - 2, by omega⟩
      exact ⟨⟨F + 12 * L + 8, 0, 0, 0, 18 * L + 14⟩,
        ⟨F + 12 * L + 8, 9 * L + 6, by ring_nf, by omega⟩,
        by rw [show 2 * k + 2 = 10 * L + 6 from by omega]; exact trans_e6 F L⟩
    · -- k ≡ 3: e = 10L+8
      obtain ⟨F, rfl⟩ : ∃ F, a = F + 2 * L + 2 := ⟨a - 2 * L - 2, by omega⟩
      exact ⟨⟨F + 12 * L + 10, 0, 0, 0, 18 * L + 16⟩,
        ⟨F + 12 * L + 10, 9 * L + 7, by ring_nf, by omega⟩,
        by rw [show 2 * k + 2 = 10 * L + 8 from by omega]; exact trans_e8 F L⟩
    · -- k ≡ 4: e = 10L+10
      obtain ⟨F, rfl⟩ : ∃ F, a = F + 2 * L + 3 := ⟨a - 2 * L - 3, by omega⟩
      exact ⟨⟨F + 12 * L + 13, 0, 0, 0, 18 * L + 22⟩,
        ⟨F + 12 * L + 13, 9 * L + 10, by ring_nf, by omega⟩,
        by rw [show 2 * k + 2 = 10 * L + 10 from by omega]; exact trans_e0 F L⟩
  · exact ⟨5, 3, by ring_nf, by omega⟩

end Sz22_2003_unofficial_1498
