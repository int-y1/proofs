import BBfLean.FM
import Mathlib.Tactic.Ring
import Mathlib.Tactic.IntervalCases

/-!
# sz22_2003_unofficial #1504: [7/15, 9/77, 242/3, 5/121, 33/2]

Vector representation:
```
 0 -1 -1  1  0
 0  2  0 -1 -1
 1 -1  0  0  2
 0  0  1  0 -2
-1  1  0  0  1
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_1504

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a, b+1, c+1, d, e⟩ => some ⟨a, b, c, d+1, e⟩
  | ⟨a, b, c, d+1, e+1⟩ => some ⟨a, b+2, c, d, e⟩
  | ⟨a, b+1, c, d, e⟩ => some ⟨a+1, b, c, d, e+2⟩
  | ⟨a, b, c, d, e+2⟩ => some ⟨a, b, c+1, d, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b+1, c, d, e+1⟩
  | _ => none

theorem e_to_c : ∀ k, ∀ a c, (⟨a, 0, c, 0, e + 2 * k⟩ : Q) [fm]⊢* ⟨a, 0, c + k, 0, e⟩ := by
  intro k; induction' k with k ih
  · intro a c; exists 0
  · intro a c; rw [show e + 2 * (k + 1) = e + 2 * k + 2 from by ring]
    step fm; apply stepStar_trans (ih a (c + 1)); ring_nf; finish

theorem drain3 : ∀ k, ∀ a c d, (⟨a + k, 0, c + 3 * k, d, 0⟩ : Q) [fm]⊢* ⟨a, 0, c, d + 2 * k, 0⟩ := by
  intro k; induction' k with k ih <;> intro a c d
  · exists 0
  · rw [show a + (k + 1) = (a + k) + 1 from by ring,
        show c + 3 * (k + 1) = (c + 3 * k) + 3 from by ring]
    step fm; step fm; step fm; step fm; step fm
    apply stepStar_trans (ih a c (d + 2)); ring_nf; finish

theorem r1_init : ∀ a c, (⟨a + 1, 0, c + 5, 0, 1⟩ : Q) [fm]⊢* ⟨a, 0, c, 3, 0⟩ := by
  intro a c; step fm; step fm; step fm; step fm; step fm; step fm; step fm; step fm; finish

theorem r3_chain : ∀ k, ∀ A E, (⟨A, k, 0, 0, E⟩ : Q) [fm]⊢* ⟨A + k, 0, 0, 0, E + 2 * k⟩ := by
  intro k; induction' k with k ih <;> intro A E
  · exists 0
  · rw [show k + 1 = k + 1 from rfl]; step fm
    apply stepStar_trans (ih (A + 1) (E + 2)); ring_nf; finish

theorem sdrain2 : ∀ a d, (⟨a + 1, 0, 2, d, 0⟩ : Q) [fm]⊢* ⟨a, 1, 0, d + 1, 0⟩ := by
  intro a d; step fm; step fm; step fm; step fm; finish

theorem chain : ∀ D, ∀ A B,
    (⟨A, B, 0, D, 2⟩ : Q) [fm]⊢* ⟨A + B + 2 * D, 0, 0, 0, 2 * B + 3 * D + 2⟩ := by
  intro D; induction' D using Nat.strongRecOn with D ih; intro A B
  rcases D with _ | _ | D
  · -- D = 0: R3 chain
    apply stepStar_trans (r3_chain B A 2)
    ring_nf; finish
  · -- D = 1: R2, then R3 chain
    step fm
    apply stepStar_trans (r3_chain (B + 2) A 1)
    ring_nf; finish
  · -- D + 2: R2, R2, R3, then IH
    step fm; step fm; step fm
    apply stepStar_trans (ih D (by omega) (A + 1) (B + 3))
    ring_nf; finish

theorem tail_c0 (A D : ℕ) :
    (⟨A + 1, 0, 0, D + 1, 0⟩ : Q) [fm]⊢⁺ ⟨A + 2 * D + 3, 0, 0, 0, 3 * D + 6⟩ := by
  step fm; step fm; step fm
  apply stepStar_trans (chain D (A + 1) 2)
  ring_nf; finish

theorem tail_c1 (A D : ℕ) :
    (⟨A + 1, 0, 1, D, 0⟩ : Q) [fm]⊢⁺ ⟨A + 2 * D + 2, 0, 0, 0, 3 * D + 4⟩ := by
  step fm; step fm; step fm; step fm
  apply stepStar_trans (chain D (A + 1) 1)
  ring_nf; finish

theorem tail_c2 (A D : ℕ) :
    (⟨A + 1, 0, 2, D, 0⟩ : Q) [fm]⊢⁺ ⟨A + 2 * D + 3, 0, 0, 0, 3 * D + 5⟩ := by
  -- sdrain2 + R3 + chain
  apply stepStar_stepPlus_stepPlus (sdrain2 A D)
  -- Now at (A, 1, 0, D+1, 0). R3 step.
  step fm
  -- Now at (A+1, 0, 0, D+1, 2).
  apply stepStar_trans (chain (D + 1) (A + 1) 0)
  ring_nf; finish

-- e ≡ 4 mod 6: e = 6n+10
theorem full_e4 (F n : ℕ) :
    (⟨F + n + 2, 0, 0, 0, 6 * n + 10⟩ : Q) [fm]⊢⁺ ⟨F + 4 * n + 7, 0, 0, 0, 6 * n + 11⟩ := by
  rw [show (6 * n + 10 : ℕ) = 0 + 2 * (3 * n + 5) from by ring]
  apply stepStar_stepPlus_stepPlus (e_to_c (3 * n + 5) (F + n + 2) 0 (e := 0))
  rw [show 0 + (3 * n + 5) = 3 * n + 5 from by ring,
      show F + n + 2 = (F + 1) + (n + 1) from by ring,
      show 3 * n + 5 = 2 + 3 * (n + 1) from by ring]
  apply stepStar_stepPlus_stepPlus (drain3 (n + 1) (F + 1) 2 0)
  rw [show 0 + 2 * (n + 1) = 2 * n + 2 from by ring]
  convert tail_c2 F (2 * n + 2) using 2 ; ring_nf

-- e ≡ 5 mod 6: e = 6n+11
theorem full_e5 (F n : ℕ) :
    (⟨F + n + 2, 0, 0, 0, 6 * n + 11⟩ : Q) [fm]⊢⁺ ⟨F + 4 * n + 7, 0, 0, 0, 6 * n + 12⟩ := by
  rw [show (6 * n + 11 : ℕ) = 1 + 2 * (3 * n + 5) from by ring]
  apply stepStar_stepPlus_stepPlus (e_to_c (3 * n + 5) (F + n + 2) 0 (e := 1))
  rw [show 0 + (3 * n + 5) = 3 * n + 5 from by ring,
      show F + n + 2 = (F + 1) + (n + 1) from by ring,
      show 3 * n + 5 = (3 * n) + 5 from by ring]
  apply stepStar_stepPlus_stepPlus (r1_init (F + 1 + n) (3 * n))
  rw [show F + 1 + n = (F + 1) + n from by ring,
      show 3 * n = 0 + 3 * n from by ring]
  apply stepStar_stepPlus_stepPlus (drain3 n (F + 1) 0 3)
  rw [show 3 + 2 * n = (2 * n + 2) + 1 from by ring]
  convert tail_c0 F (2 * n + 2) using 2 ; ring_nf

-- e ≡ 0 mod 6: e = 6n+12
theorem full_e0 (F n : ℕ) :
    (⟨F + n + 3, 0, 0, 0, 6 * n + 12⟩ : Q) [fm]⊢⁺ ⟨F + 4 * n + 9, 0, 0, 0, 6 * n + 15⟩ := by
  rw [show (6 * n + 12 : ℕ) = 0 + 2 * (3 * n + 6) from by ring]
  apply stepStar_stepPlus_stepPlus (e_to_c (3 * n + 6) (F + n + 3) 0 (e := 0))
  rw [show 0 + (3 * n + 6) = 3 * n + 6 from by ring,
      show F + n + 3 = (F + 1) + (n + 2) from by ring,
      show 3 * n + 6 = 0 + 3 * (n + 2) from by ring]
  apply stepStar_stepPlus_stepPlus (drain3 (n + 2) (F + 1) 0 0)
  rw [show 0 + 2 * (n + 2) = (2 * n + 3) + 1 from by ring]
  convert tail_c0 F (2 * n + 3) using 2 ; ring_nf

-- e ≡ 1 mod 6: e = 6n+13
theorem full_e1 (F n : ℕ) :
    (⟨F + n + 2, 0, 0, 0, 6 * n + 13⟩ : Q) [fm]⊢⁺ ⟨F + 4 * n + 8, 0, 0, 0, 6 * n + 13⟩ := by
  rw [show (6 * n + 13 : ℕ) = 1 + 2 * (3 * n + 6) from by ring]
  apply stepStar_stepPlus_stepPlus (e_to_c (3 * n + 6) (F + n + 2) 0 (e := 1))
  rw [show 0 + (3 * n + 6) = 3 * n + 6 from by ring,
      show F + n + 2 = (F + 1) + (n + 1) from by ring,
      show 3 * n + 6 = (3 * n + 1) + 5 from by ring]
  apply stepStar_stepPlus_stepPlus (r1_init (F + 1 + n) (3 * n + 1))
  rw [show F + 1 + n = (F + 1) + n from by ring,
      show 3 * n + 1 = 1 + 3 * n from by ring]
  apply stepStar_stepPlus_stepPlus (drain3 n (F + 1) 1 3)
  rw [show 3 + 2 * n = 2 * n + 3 from by ring]
  convert tail_c1 F (2 * n + 3) using 2 ; ring_nf

-- e ≡ 2 mod 6: e = 6n+14
theorem full_e2 (F n : ℕ) :
    (⟨F + n + 3, 0, 0, 0, 6 * n + 14⟩ : Q) [fm]⊢⁺ ⟨F + 4 * n + 10, 0, 0, 0, 6 * n + 16⟩ := by
  rw [show (6 * n + 14 : ℕ) = 0 + 2 * (3 * n + 7) from by ring]
  apply stepStar_stepPlus_stepPlus (e_to_c (3 * n + 7) (F + n + 3) 0 (e := 0))
  rw [show 0 + (3 * n + 7) = 3 * n + 7 from by ring,
      show F + n + 3 = (F + 1) + (n + 2) from by ring,
      show 3 * n + 7 = 1 + 3 * (n + 2) from by ring]
  apply stepStar_stepPlus_stepPlus (drain3 (n + 2) (F + 1) 1 0)
  rw [show 0 + 2 * (n + 2) = 2 * n + 4 from by ring]
  convert tail_c1 F (2 * n + 4) using 2 ; ring_nf

-- e ≡ 3 mod 6: e = 6n+15
theorem full_e3 (F n : ℕ) :
    (⟨F + n + 2, 0, 0, 0, 6 * n + 15⟩ : Q) [fm]⊢⁺ ⟨F + 4 * n + 9, 0, 0, 0, 6 * n + 14⟩ := by
  rw [show (6 * n + 15 : ℕ) = 1 + 2 * (3 * n + 7) from by ring]
  apply stepStar_stepPlus_stepPlus (e_to_c (3 * n + 7) (F + n + 2) 0 (e := 1))
  rw [show 0 + (3 * n + 7) = 3 * n + 7 from by ring,
      show F + n + 2 = (F + 1) + (n + 1) from by ring,
      show 3 * n + 7 = (3 * n + 2) + 5 from by ring]
  apply stepStar_stepPlus_stepPlus (r1_init (F + 1 + n) (3 * n + 2))
  rw [show F + 1 + n = (F + 1) + n from by ring,
      show 3 * n + 2 = 2 + 3 * n from by ring]
  apply stepStar_stepPlus_stepPlus (drain3 n (F + 1) 2 3)
  rw [show 3 + 2 * n = 2 * n + 3 from by ring]
  convert tail_c2 F (2 * n + 3) using 2 ; ring_nf

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨15, 0, 0, 0, 10⟩) (by execute fm 72)
  apply progress_nonhalt (fm := fm)
    (P := fun q ↦ ∃ a e, q = ⟨a, 0, 0, 0, e⟩ ∧ 2 * a ≥ e + 20 ∧ e ≥ 10)
  · intro q ⟨a, e, hq, hinv, he⟩; subst hq
    have h6 : e % 6 < 6 := Nat.mod_lt _ (by omega)
    obtain ⟨n, hn⟩ : ∃ n, e = 6 * n + e % 6 := ⟨e / 6, by omega⟩
    interval_cases (e % 6)
    · -- e ≡ 0 mod 6: e = 6n, n ≥ 2
      obtain ⟨m, rfl⟩ : ∃ m, n = m + 2 := ⟨n - 2, by omega⟩
      rw [show 6 * (m + 2) + 0 = 6 * m + 12 from by ring] at hn; subst hn
      obtain ⟨F, rfl⟩ : ∃ F, a = F + m + 3 := ⟨a - m - 3, by omega⟩
      exact ⟨⟨F + 4 * m + 9, 0, 0, 0, 6 * m + 15⟩,
        ⟨F + 4 * m + 9, 6 * m + 15, rfl, by omega, by omega⟩,
        full_e0 F m⟩
    · -- e ≡ 1 mod 6: e = 6n+1, n ≥ 2
      obtain ⟨m, rfl⟩ : ∃ m, n = m + 2 := ⟨n - 2, by omega⟩
      rw [show 6 * (m + 2) + 1 = 6 * m + 13 from by ring] at hn; subst hn
      obtain ⟨F, rfl⟩ : ∃ F, a = F + m + 2 := ⟨a - m - 2, by omega⟩
      exact ⟨⟨F + 4 * m + 8, 0, 0, 0, 6 * m + 13⟩,
        ⟨F + 4 * m + 8, 6 * m + 13, rfl, by omega, by omega⟩,
        full_e1 F m⟩
    · -- e ≡ 2 mod 6: e = 6n+2, n ≥ 2
      obtain ⟨m, rfl⟩ : ∃ m, n = m + 2 := ⟨n - 2, by omega⟩
      rw [show 6 * (m + 2) + 2 = 6 * m + 14 from by ring] at hn; subst hn
      obtain ⟨F, rfl⟩ : ∃ F, a = F + m + 3 := ⟨a - m - 3, by omega⟩
      exact ⟨⟨F + 4 * m + 10, 0, 0, 0, 6 * m + 16⟩,
        ⟨F + 4 * m + 10, 6 * m + 16, rfl, by omega, by omega⟩,
        full_e2 F m⟩
    · -- e ≡ 3 mod 6: e = 6n+3, n ≥ 2
      obtain ⟨m, rfl⟩ : ∃ m, n = m + 2 := ⟨n - 2, by omega⟩
      rw [show 6 * (m + 2) + 3 = 6 * m + 15 from by ring] at hn; subst hn
      obtain ⟨F, rfl⟩ : ∃ F, a = F + m + 2 := ⟨a - m - 2, by omega⟩
      exact ⟨⟨F + 4 * m + 9, 0, 0, 0, 6 * m + 14⟩,
        ⟨F + 4 * m + 9, 6 * m + 14, rfl, by omega, by omega⟩,
        full_e3 F m⟩
    · -- e ≡ 4 mod 6: e = 6n+4, n ≥ 1
      obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
      rw [show 6 * (m + 1) + 4 = 6 * m + 10 from by ring] at hn; subst hn
      obtain ⟨F, rfl⟩ : ∃ F, a = F + m + 2 := ⟨a - m - 2, by omega⟩
      exact ⟨⟨F + 4 * m + 7, 0, 0, 0, 6 * m + 11⟩,
        ⟨F + 4 * m + 7, 6 * m + 11, rfl, by omega, by omega⟩,
        full_e4 F m⟩
    · -- e ≡ 5 mod 6: e = 6n+5, n ≥ 1
      obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
      rw [show 6 * (m + 1) + 5 = 6 * m + 11 from by ring] at hn; subst hn
      obtain ⟨F, rfl⟩ : ∃ F, a = F + m + 2 := ⟨a - m - 2, by omega⟩
      exact ⟨⟨F + 4 * m + 7, 0, 0, 0, 6 * m + 12⟩,
        ⟨F + 4 * m + 7, 6 * m + 12, rfl, by omega, by omega⟩,
        full_e5 F m⟩
  · exact ⟨15, 10, rfl, by omega, by omega⟩

end Sz22_2003_unofficial_1504
