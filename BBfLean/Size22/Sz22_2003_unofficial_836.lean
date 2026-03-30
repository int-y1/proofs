import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #836: [36/35, 1/33, 25/3, 11/25, 21/2]

Vector representation:
```
 2  2 -1 -1  0
 0 -1  0  0 -1
 0 -1  2  0  0
 0  0 -2  0  1
-1  1  0  1  0
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_836

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a, b, c+1, d+1, e⟩ => some ⟨a+2, b+2, c, d, e⟩
  | ⟨a, b+1, c, d, e+1⟩ => some ⟨a, b, c, d, e⟩
  | ⟨a, b+1, c, d, e⟩ => some ⟨a, b, c+2, d, e⟩
  | ⟨a, b, c+2, d, e⟩ => some ⟨a, b, c, d, e+1⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b+1, c, d+1, e⟩
  | _ => none

theorem r1_chain : ∀ k, ∀ A B c d e,
    ⟨A, B, c + k, d + k, e⟩ [fm]⊢* ⟨A + 2 * k, B + 2 * k, c, d, e⟩ := by
  intro k; induction' k with k ih <;> intro A B c d e
  · exists 0
  · rw [show c + (k + 1) = (c + k) + 1 from by ring,
        show d + (k + 1) = (d + k) + 1 from by ring]
    step fm
    apply stepStar_trans (ih (A + 2) (B + 2) c d e)
    ring_nf; finish

theorem b_to_c : ∀ k, ∀ A c,
    ⟨A, k, c, (0 : ℕ), (0 : ℕ)⟩ [fm]⊢* ⟨A, 0, c + 2 * k, (0 : ℕ), (0 : ℕ)⟩ := by
  intro k; induction' k with k ih <;> intro A c
  · exists 0
  · step fm
    apply stepStar_trans (ih A (c + 2))
    ring_nf; finish

theorem c_to_e : ∀ k, ∀ A c e,
    ⟨A, 0, c + 2 * k, (0 : ℕ), e⟩ [fm]⊢* ⟨A, 0, c, (0 : ℕ), e + k⟩ := by
  intro k; induction' k with k ih <;> intro A c e
  · exists 0
  · rw [show c + 2 * (k + 1) = (c + 2 * k) + 2 from by ring]
    step fm
    apply stepStar_trans (ih A c (e + 1))
    ring_nf; finish

theorem e_drain : ∀ k, ∀ A d,
    ⟨A + k, 0, 0, d, k⟩ [fm]⊢* ⟨A, 0, 0, d + k, (0 : ℕ)⟩ := by
  intro k; induction' k with k ih <;> intro A d
  · exists 0
  · rw [show A + (k + 1) = (A + k) + 1 from by ring]
    step fm; step fm
    apply stepStar_trans (ih A (d + 1))
    ring_nf; finish

theorem r2_chain : ∀ k, ∀ A e,
    ⟨A, k, 0, (0 : ℕ), e + k⟩ [fm]⊢* ⟨A, 0, 0, (0 : ℕ), e⟩ := by
  intro k; induction' k with k ih <;> intro A e
  · exists 0
  · rw [show e + (k + 1) = (e + k) + 1 from by ring]
    step fm
    apply stepStar_trans (ih A e)
    finish

theorem spiral_inner : ∀ D, ∀ A B, B ≥ 1 →
    ⟨A, B, 0, D, (0 : ℕ)⟩ [fm]⊢* ⟨A + 2 * D, 0, 2 * B + 3 * D, (0 : ℕ), (0 : ℕ)⟩ := by
  intro D; induction' D using Nat.strongRecOn with D ih; intro A B hB
  rcases D with _ | _ | D
  · rw [show A + 2 * 0 = A from by ring, show 2 * B + 3 * 0 = 0 + 2 * B from by ring]
    exact b_to_c B A 0
  · obtain ⟨B', rfl⟩ : ∃ B', B = B' + 1 := ⟨B - 1, by omega⟩
    step fm
    rw [show (2 : ℕ) = 1 + 1 from by ring, show (1 : ℕ) = 0 + 1 from by ring]
    apply stepStar_trans (r1_chain 1 A B' 1 0 0)
    rw [show A + 2 * 1 = A + 2 from by ring, show B' + 2 * 1 = B' + 2 from by ring]
    apply stepStar_trans (b_to_c (B' + 2) (A + 2) 1)
    ring_nf; finish
  · obtain ⟨B', rfl⟩ : ∃ B', B = B' + 1 := ⟨B - 1, by omega⟩
    step fm
    rw [show (2 : ℕ) = 0 + 2 from by ring, show D + 2 = D + 2 from rfl]
    apply stepStar_trans (r1_chain 2 A B' 0 D 0)
    rw [show A + 2 * 2 = A + 4 from by ring, show B' + 2 * 2 = B' + 4 from by ring]
    apply stepStar_trans (ih D (by omega) (A + 4) (B' + 4) (by omega))
    ring_nf; finish

theorem phase12 : ∀ d, ∀ a,
    ⟨a + 1, 0, 0, d, (0 : ℕ)⟩ [fm]⊢⁺ ⟨a + 2 * d + 2, 0, 3 * d + 5, (0 : ℕ), (0 : ℕ)⟩ := by
  intro d a
  step fm
  rcases d with _ | d
  · apply stepStar_trans (spiral_inner 1 a 1 (by omega))
    ring_nf; finish
  · rw [show d + 1 + 1 = d + 2 from by ring]
    apply stepStar_trans (spiral_inner (d + 2) a 1 (by omega))
    ring_nf; finish

-- d=0: (a+1, 0, 0, 0, 0) ⊢⁺ (a+2, 0, 0, 1, 0)
theorem case_d0 : ∀ a, ⟨a + 1, 0, 0, 0, (0 : ℕ)⟩ [fm]⊢⁺ ⟨a + 2, 0, 0, 1, (0 : ℕ)⟩ := by
  intro a
  apply stepPlus_stepStar_stepPlus (phase12 0 a)
  -- normalize the phase12 output
  rw [show a + 2 * 0 + 2 = a + 2 from by ring, show 3 * 0 + 5 = 1 + 2 * 2 from by ring]
  apply stepStar_trans (c_to_e 2 (a + 2) 1 0)
  -- (a+2, 0, 1, 0, 0+2): need to normalize then step
  rw [show a + 2 = (a + 1) + 1 from by ring]
  step fm -- R5: (a+1, 1, 1, 1, 2)
  step fm -- R1: (a+3, 3, 0, 0, 2)
  step fm -- R2: (a+3, 2, 0, 0, 1)
  step fm -- R2: (a+3, 1, 0, 0, 0)
  step fm -- R3: (a+3, 0, 2, 0, 0)
  step fm -- R4: (a+3, 0, 0, 0, 1)
  rw [show a + 3 = (a + 2) + 1 from by ring]
  step fm -- R5: (a+2, 1, 0, 1, 1)
  step fm -- R2: (a+2, 0, 0, 1, 0)
  finish

-- d odd: d = 2k+1, (a+1, 0, 0, 2k+1, 0) ⊢⁺ (a+k, 0, 0, 3k+4, 0)
theorem case_odd : ∀ k, ∀ a,
    ⟨a + 1, 0, 0, 2 * k + 1, (0 : ℕ)⟩ [fm]⊢⁺ ⟨a + k, 0, 0, 3 * k + 4, (0 : ℕ)⟩ := by
  intro k a
  apply stepPlus_stepStar_stepPlus (phase12 (2 * k + 1) a)
  rw [show a + 2 * (2 * k + 1) + 2 = a + 4 * k + 4 from by ring,
      show 3 * (2 * k + 1) + 5 = 0 + 2 * (3 * k + 4) from by ring]
  apply stepStar_trans (c_to_e (3 * k + 4) (a + 4 * k + 4) 0 0)
  rw [show a + 4 * k + 4 = (a + k) + (3 * k + 4) from by ring,
      show (0 : ℕ) + (3 * k + 4) = 3 * k + 4 from by ring]
  have := e_drain (3 * k + 4) (a + k) 0
  convert this using 2; ring_nf

-- d even >= 2: d = 2*(m+1) = 2m+2
-- (a+1, 0, 0, 2m+2, 0) ⊢⁺ (a+m+5, 0, 0, 3m+2, 0)
theorem case_even : ∀ m, ∀ a,
    ⟨a + 1, 0, 0, 2 * m + 2, (0 : ℕ)⟩ [fm]⊢⁺ ⟨a + m + 5, 0, 0, 3 * m + 2, (0 : ℕ)⟩ := by
  intro m a
  apply stepPlus_stepStar_stepPlus (phase12 (2 * m + 2) a)
  rw [show a + 2 * (2 * m + 2) + 2 = a + 4 * m + 6 from by ring,
      show 3 * (2 * m + 2) + 5 = 1 + 2 * (3 * m + 5) from by ring]
  apply stepStar_trans (c_to_e (3 * m + 5) (a + 4 * m + 6) 1 0)
  -- (a+4m+6, 0, 1, 0, 0+(3m+5))
  rw [show a + 4 * m + 6 = (a + 4 * m + 5) + 1 from by ring,
      show (0 : ℕ) + (3 * m + 5) = 3 * m + 5 from by ring]
  step fm -- R5: (a+4m+5, 1, 1, 1, 3m+5)
  rw [show 3 * m + 5 = 3 * m + 5 from rfl]
  step fm -- R1: (a+4m+7, 3, 0, 0, 3m+5)
  rw [show 3 * m + 5 = (3 * m + 2) + 3 from by ring]
  apply stepStar_trans (r2_chain 3 (a + 4 * m + 7) (3 * m + 2))
  -- (a+4m+7, 0, 0, 0, 3m+2)
  rw [show a + 4 * m + 7 = (a + m + 5) + (3 * m + 2) from by ring]
  have := e_drain (3 * m + 2) (a + m + 5) 0
  convert this using 2; ring_nf

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨2, 0, 0, 1, 0⟩) (by execute fm 15)
  apply progress_nonhalt (fm := fm)
    (P := fun q ↦ ∃ A d, q = ⟨A, 0, 0, d, 0⟩ ∧ A ≥ 1 ∧ A + d ≥ 3)
  · intro c ⟨A, d, hq, hA, hAd⟩; subst hq
    obtain ⟨a, rfl⟩ : ∃ a, A = a + 1 := ⟨A - 1, by omega⟩
    rcases Nat.even_or_odd d with ⟨m, hm⟩ | ⟨m, hm⟩
    · rw [show m + m = 2 * m from by ring] at hm; subst hm
      rcases m with _ | m
      · exact ⟨⟨a + 2, 0, 0, 1, 0⟩,
          ⟨a + 2, 1, rfl, by omega, by omega⟩, case_d0 a⟩
      · rw [show 2 * (m + 1) = 2 * m + 2 from by ring]
        exact ⟨⟨a + m + 5, 0, 0, 3 * m + 2, 0⟩,
          ⟨a + m + 5, 3 * m + 2, rfl, by omega, by omega⟩, case_even m a⟩
    · subst hm
      exact ⟨⟨a + m, 0, 0, 3 * m + 4, 0⟩,
        ⟨a + m, 3 * m + 4, rfl, by omega, by omega⟩, case_odd m a⟩
  · exact ⟨2, 1, rfl, by omega, by omega⟩

end Sz22_2003_unofficial_836
