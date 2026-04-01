import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #1452: [7/15, 27/77, 242/3, 5/11, 33/2]

Vector representation:
```
 0 -1 -1  1  0
 0  3  0 -1 -1
 1 -1  0  0  2
 0  0  1  0 -1
-1  1  0  0  1
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_1452

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a, b+1, c+1, d, e⟩ => some ⟨a, b, c, d+1, e⟩
  | ⟨a, b, c, d+1, e+1⟩ => some ⟨a, b+3, c, d, e⟩
  | ⟨a, b+1, c, d, e⟩ => some ⟨a+1, b, c, d, e+2⟩
  | ⟨a, b, c, d, e+1⟩ => some ⟨a, b, c+1, d, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b+1, c, d, e+1⟩
  | _ => none

-- R4 chain: transfer e to c
theorem e_to_c : ∀ k, ∀ a c e, ⟨a, 0, c, 0, e + k⟩ [fm]⊢* ⟨a, 0, c + k, 0, e⟩ := by
  intro k; induction' k with k ih <;> intro a c e
  · simp; exists 0
  · rw [show e + (k + 1) = (e + k) + 1 from by ring]
    step fm
    apply stepStar_trans (ih a (c + 1) e)
    ring_nf; finish

-- R3 chain: transfer b to a,e
theorem b_to_ae : ∀ k, ∀ a b e, ⟨a, k + b, 0, 0, e⟩ [fm]⊢* ⟨a + k, b, 0, 0, e + 2 * k⟩ := by
  intro k; induction' k with k ih <;> intro a b e
  · simp; exists 0
  · rw [show (k + 1) + b = k + (b + 1) from by ring]
    step fm
    apply stepStar_trans (ih (a + 1) b (e + 2))
    ring_nf; finish

-- c to d phase: R5,R1,R2,R1,R1,R1 repeated
theorem c_to_d : ∀ k, ∀ a c d, ⟨a + k, 0, 4 * k + c, d, 0⟩ [fm]⊢* ⟨a, 0, c, d + 3 * k, 0⟩ := by
  intro k; induction' k with k ih <;> intro a c d
  · simp; exists 0
  · rw [show a + (k + 1) = (a + k) + 1 from by ring,
        show 4 * (k + 1) + c = (4 * k + c) + 4 from by ring]
    step fm; step fm; step fm; step fm; step fm; step fm
    apply stepStar_trans (ih a c (d + 3))
    ring_nf; finish

-- bd to ae: from (A, B, 0, D, 0) with B>=1
theorem bd_to_ae : ∀ D, ∀ A B, B ≥ 1 →
    ⟨A, B, 0, D, 0⟩ [fm]⊢⁺ ⟨A + B + 3 * D, 0, 0, 0, 2 * B + 5 * D⟩ := by
  intro D; induction' D using Nat.strongRecOn with D ih; intro A B hB
  rcases D with _ | _ | D
  · -- D = 0
    obtain ⟨B, rfl⟩ : ∃ B', B = B' + 1 := ⟨B - 1, by omega⟩
    step fm
    apply stepStar_trans (b_to_ae B (A + 1) 0 2)
    ring_nf; finish
  · -- D = 1
    obtain ⟨B, rfl⟩ : ∃ B', B = B' + 1 := ⟨B - 1, by omega⟩
    step fm; step fm; step fm
    apply stepStar_trans (b_to_ae (B + 2) (A + 2) 0 3)
    ring_nf; finish
  · -- D + 2
    obtain ⟨B, rfl⟩ : ∃ B', B = B' + 1 := ⟨B - 1, by omega⟩
    step fm; step fm; step fm
    -- After R3→R2→R2: goal state has B+2+1+3 for b and D+1+1 for d
    rw [show B + 2 + 1 + 3 = B + 1 + 5 from by ring,
        show D + 1 + 1 = D + 2 from by ring]
    have h := ih D (by omega) (A + 1) (B + 1 + 5) (by omega)
    rw [show A + 1 + (B + 1 + 5) + 3 * D = A + (B + 1) + 3 * (D + 2) from by ring,
        show 2 * (B + 1 + 5) + 5 * D = 2 * (B + 1) + 5 * (D + 2) from by ring] at h
    exact stepPlus_stepStar (stepPlus_stepStar_stepPlus h (by exists 0))

-- Residue 1: (a+1, 0, 1, d, 0) to (a, 3, 0, d, 0)
theorem res1 : ∀ a d, ⟨a + 1, 0, 1, d, 0⟩ [fm]⊢* ⟨a, 3, 0, d, 0⟩ := by
  intro a d; step fm; step fm; step fm; finish

-- Residue 2: (a+1, 0, 2, d, 0) to (a, 2, 0, d+1, 0)
theorem res2 : ∀ a d, ⟨a + 1, 0, 2, d, 0⟩ [fm]⊢* ⟨a, 2, 0, d + 1, 0⟩ := by
  intro a d; step fm; step fm; step fm; step fm; finish

-- Residue 3: (a+1, 0, 3, d, 0) to (a+1, 6, 0, d, 0)
theorem res3 : ∀ a d, ⟨a + 1, 0, 3, d, 0⟩ [fm]⊢* ⟨a + 1, 6, 0, d, 0⟩ := by
  intro a d; step fm; step fm; step fm; step fm; step fm; step fm; step fm; step fm; finish

-- R5,R2 opening: (a+1, 0, 0, d+1, 0) to (a, 4, 0, d, 0)
theorem r5r2 : ∀ a d, ⟨a + 1, 0, 0, d + 1, 0⟩ [fm]⊢* ⟨a, 4, 0, d, 0⟩ := by
  intro a d; step fm; step fm; finish

-- Cycle e=4k+3: (a+k+1, 0, 0, 0, 4k+3) to (a+9k+7, 0, 0, 0, 15k+12)
theorem cycle_e3 : ⟨a + k + 1, 0, 0, 0, 4 * k + 3⟩ [fm]⊢⁺
    ⟨a + 9 * k + 7, 0, 0, 0, 15 * k + 12⟩ := by
  have h1 : ⟨a + k + 1, 0, 0, 0, 4 * k + 3⟩ [fm]⊢* ⟨a + 1, 6, 0, 3 * k, 0⟩ := by
    apply stepStar_trans
    · rw [show (4 * k + 3 : ℕ) = 0 + (4 * k + 3) from by ring]
      exact e_to_c (4 * k + 3) (a + k + 1) 0 0
    apply stepStar_trans
    · rw [show a + k + 1 = (a + 1) + k from by ring,
          show (0 : ℕ) + (4 * k + 3) = 4 * k + 3 from by ring]
      have h := c_to_d k (a + 1) 3 0
      rwa [show (0 : ℕ) + 3 * k = 3 * k from by ring] at h
    exact res3 a (3 * k)
  have h2 : ⟨a + 1, 6, 0, 3 * k, 0⟩ [fm]⊢⁺ ⟨a + 9 * k + 7, 0, 0, 0, 15 * k + 12⟩ := by
    have h := bd_to_ae (3 * k) (a + 1) 6 (by omega)
    rwa [show (a + 1) + 6 + 3 * (3 * k) = a + 9 * k + 7 from by ring,
         show 2 * 6 + 5 * (3 * k) = 15 * k + 12 from by ring] at h
  exact stepStar_stepPlus_stepPlus h1 h2

-- Cycle e=4(k+1): (a+k+2, 0, 0, 0, 4k+4) to (a+9k+10, 0, 0, 0, 15k+18)
theorem cycle_e0 : ⟨a + k + 2, 0, 0, 0, 4 * k + 4⟩ [fm]⊢⁺
    ⟨a + 9 * k + 10, 0, 0, 0, 15 * k + 18⟩ := by
  have h1 : ⟨a + k + 2, 0, 0, 0, 4 * k + 4⟩ [fm]⊢* ⟨a, 4, 0, 3 * k + 2, 0⟩ := by
    apply stepStar_trans
    · rw [show (4 * k + 4 : ℕ) = 0 + (4 * k + 4) from by ring]
      exact e_to_c (4 * k + 4) (a + k + 2) 0 0
    apply stepStar_trans
    · rw [show a + k + 2 = (a + 1) + (k + 1) from by ring,
          show (0 : ℕ) + (4 * k + 4) = 4 * (k + 1) + 0 from by ring]
      have h := c_to_d (k + 1) (a + 1) 0 0
      rwa [show (0 : ℕ) + 3 * (k + 1) = 3 * (k + 1) from by ring] at h
    rw [show 3 * (k + 1) = (3 * k + 2) + 1 from by ring]
    exact r5r2 a (3 * k + 2)
  have h2 : ⟨a, 4, 0, 3 * k + 2, 0⟩ [fm]⊢⁺ ⟨a + 9 * k + 10, 0, 0, 0, 15 * k + 18⟩ := by
    have h := bd_to_ae (3 * k + 2) a 4 (by omega)
    rwa [show a + 4 + 3 * (3 * k + 2) = a + 9 * k + 10 from by ring,
         show 2 * 4 + 5 * (3 * k + 2) = 15 * k + 18 from by ring] at h
  exact stepStar_stepPlus_stepPlus h1 h2

-- Cycle e=4(k+1)+1=4k+5: (a+k+2, 0, 0, 0, 4k+5) to (a+9k+12, 0, 0, 0, 15k+21)
theorem cycle_e1 : ⟨a + k + 2, 0, 0, 0, 4 * k + 5⟩ [fm]⊢⁺
    ⟨a + 9 * k + 12, 0, 0, 0, 15 * k + 21⟩ := by
  have h1 : ⟨a + k + 2, 0, 0, 0, 4 * k + 5⟩ [fm]⊢* ⟨a, 3, 0, 3 * k + 3, 0⟩ := by
    apply stepStar_trans
    · rw [show (4 * k + 5 : ℕ) = 0 + (4 * k + 5) from by ring]
      exact e_to_c (4 * k + 5) (a + k + 2) 0 0
    apply stepStar_trans
    · rw [show a + k + 2 = (a + 1) + (k + 1) from by ring,
          show (0 : ℕ) + (4 * k + 5) = 4 * (k + 1) + 1 from by ring]
      have h := c_to_d (k + 1) (a + 1) 1 0
      rwa [show (0 : ℕ) + 3 * (k + 1) = 3 * k + 3 from by ring] at h
    exact res1 a (3 * k + 3)
  have h2 : ⟨a, 3, 0, 3 * k + 3, 0⟩ [fm]⊢⁺ ⟨a + 9 * k + 12, 0, 0, 0, 15 * k + 21⟩ := by
    have h := bd_to_ae (3 * k + 3) a 3 (by omega)
    rwa [show a + 3 + 3 * (3 * k + 3) = a + 9 * k + 12 from by ring,
         show 2 * 3 + 5 * (3 * k + 3) = 15 * k + 21 from by ring] at h
  exact stepStar_stepPlus_stepPlus h1 h2

-- Cycle e=4(k+1)+2=4k+6: (a+k+2, 0, 0, 0, 4k+6) to (a+9k+14, 0, 0, 0, 15k+24)
theorem cycle_e2 : ⟨a + k + 2, 0, 0, 0, 4 * k + 6⟩ [fm]⊢⁺
    ⟨a + 9 * k + 14, 0, 0, 0, 15 * k + 24⟩ := by
  have h1 : ⟨a + k + 2, 0, 0, 0, 4 * k + 6⟩ [fm]⊢* ⟨a, 2, 0, 3 * k + 4, 0⟩ := by
    apply stepStar_trans
    · rw [show (4 * k + 6 : ℕ) = 0 + (4 * k + 6) from by ring]
      exact e_to_c (4 * k + 6) (a + k + 2) 0 0
    apply stepStar_trans
    · rw [show a + k + 2 = (a + 1) + (k + 1) from by ring,
          show (0 : ℕ) + (4 * k + 6) = 4 * (k + 1) + 2 from by ring]
      have h := c_to_d (k + 1) (a + 1) 2 0
      rwa [show (0 : ℕ) + 3 * (k + 1) = 3 * k + 3 from by ring] at h
    have h := res2 a (3 * k + 3)
    rwa [show 3 * k + 3 + 1 = 3 * k + 4 from by ring] at h
  have h2 : ⟨a, 2, 0, 3 * k + 4, 0⟩ [fm]⊢⁺ ⟨a + 9 * k + 14, 0, 0, 0, 15 * k + 24⟩ := by
    have h := bd_to_ae (3 * k + 4) a 2 (by omega)
    rwa [show a + 2 + 3 * (3 * k + 4) = a + 9 * k + 14 from by ring,
         show 2 * 2 + 5 * (3 * k + 4) = 15 * k + 24 from by ring] at h
  exact stepStar_stepPlus_stepPlus h1 h2

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨7, 0, 0, 0, 12⟩) (by execute fm 19)
  apply progress_nonhalt (fm := fm)
    (P := fun q ↦ ∃ a e, q = ⟨a, 0, 0, 0, e⟩ ∧ 4 * a ≥ e + 4 ∧ e ≥ 3)
  · intro c ⟨a, e, hq, ha, he⟩; subst hq
    obtain ⟨k, rfl | rfl | rfl | rfl⟩ : ∃ k, e = 4 * k ∨ e = 4 * k + 1 ∨ e = 4 * k + 2 ∨ e = 4 * k + 3 :=
      ⟨e / 4, by omega⟩
    · -- e = 4k, k >= 1
      obtain ⟨k, rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
      obtain ⟨m, rfl⟩ : ∃ m, a = m + k + 2 := ⟨a - k - 2, by omega⟩
      exact ⟨⟨m + 9 * k + 10, 0, 0, 0, 15 * k + 18⟩,
        ⟨m + 9 * k + 10, 15 * k + 18, rfl, by omega, by omega⟩,
        cycle_e0⟩
    · -- e = 4k+1, k >= 1
      obtain ⟨k, rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
      obtain ⟨m, rfl⟩ : ∃ m, a = m + k + 2 := ⟨a - k - 2, by omega⟩
      exact ⟨⟨m + 9 * k + 12, 0, 0, 0, 15 * k + 21⟩,
        ⟨m + 9 * k + 12, 15 * k + 21, rfl, by omega, by omega⟩,
        cycle_e1⟩
    · -- e = 4k+2, k >= 1
      obtain ⟨k, rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
      obtain ⟨m, rfl⟩ : ∃ m, a = m + k + 2 := ⟨a - k - 2, by omega⟩
      exact ⟨⟨m + 9 * k + 14, 0, 0, 0, 15 * k + 24⟩,
        ⟨m + 9 * k + 14, 15 * k + 24, rfl, by omega, by omega⟩,
        cycle_e2⟩
    · -- e = 4k+3, k >= 0
      obtain ⟨m, rfl⟩ : ∃ m, a = m + k + 1 := ⟨a - k - 1, by omega⟩
      exact ⟨⟨m + 9 * k + 7, 0, 0, 0, 15 * k + 12⟩,
        ⟨m + 9 * k + 7, 15 * k + 12, rfl, by omega, by omega⟩,
        cycle_e3⟩
  · exact ⟨7, 12, rfl, by omega, by omega⟩

end Sz22_2003_unofficial_1452
