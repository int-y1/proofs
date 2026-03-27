import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #458: [28/15, 147/22, 25/2, 11/7, 3/5]

Vector representation:
```
 2 -1 -1  1  0
-1  1  0  2 -1
-1  0  2  0  0
 0  0  0 -1  1
 0  1 -1  0  0
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_458

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a, b+1, c+1, d, e⟩ => some ⟨a+2, b, c, d+1, e⟩
  | ⟨a+1, b, c, d, e+1⟩ => some ⟨a, b+1, c, d+2, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b, c+2, d, e⟩
  | ⟨a, b, c, d+1, e⟩ => some ⟨a, b, c, d, e+1⟩
  | ⟨a, b, c+1, d, e⟩ => some ⟨a, b+1, c, d, e⟩
  | _ => none

theorem drain_R4 : ∀ k c d e, ⟨0, 0, c, d + k, e⟩ [fm]⊢* ⟨0, 0, c, d, e + k⟩ := by
  intro k; induction' k with k ih <;> intro c d e
  · exists 0
  rw [show d + (k + 1) = d + k + 1 from by ring]; step fm
  refine stepStar_trans (ih c d (e + 1)) ?_; ring_nf; finish

theorem drain_R3 : ∀ k a c d, ⟨a + k, 0, c, d, 0⟩ [fm]⊢* ⟨a, 0, c + 2 * k, d, 0⟩ := by
  intro k; induction' k with k ih <;> intro a c d
  · exists 0
  rw [show a + (k + 1) = (a + k) + 1 from by ring]; step fm
  refine stepStar_trans (ih a _ d) ?_; ring_nf; finish

theorem chain_R1R2 : ∀ k a c d e,
    ⟨a, 1, c + k, d, e + k⟩ [fm]⊢* ⟨a + k, 1, c, d + 3 * k, e⟩ := by
  intro k; induction' k with k ih <;> intro a c d e
  · exists 0
  rw [show c + (k + 1) = (c + k) + 1 from by ring,
      show e + (k + 1) = (e + k) + 1 from by ring]
  step fm; step fm
  refine stepStar_trans (ih _ c _ e) ?_; ring_nf; finish

theorem chain_R2 : ∀ k a b d e,
    ⟨a + k, b, 0, d, e + k⟩ [fm]⊢* ⟨a, b + k, 0, d + 2 * k, e⟩ := by
  intro k; induction' k with k ih <;> intro a b d e
  · exists 0
  rw [show a + (k + 1) = (a + k) + 1 from by ring,
      show e + (k + 1) = (e + k) + 1 from by ring]
  step fm
  refine stepStar_trans (ih a _ _ e) ?_; ring_nf; finish

theorem cleanup_even : ∀ k a d,
    ⟨a + 1, 2 * k, 0, d, 0⟩ [fm]⊢* ⟨a + 3 * k + 1, 0, 0, d + 2 * k, 0⟩ := by
  intro k; induction' k with k ih <;> intro a d
  · exists 0
  rw [show 2 * (k + 1) = 2 * k + 1 + 1 from by ring]
  step fm; step fm; step fm
  refine stepStar_trans (ih _ _) ?_; ring_nf; finish

theorem cleanup_odd : ∀ k a d,
    ⟨a + 1, 2 * k + 1, 0, d, 0⟩ [fm]⊢* ⟨a + 3 * k + 2, 0, 1, d + 2 * k + 1, 0⟩ := by
  intro k; induction' k with k ih <;> intro a d
  · step fm; step fm; finish
  rw [show 2 * (k + 1) + 1 = (2 * k + 1) + 1 + 1 from by ring]
  step fm; step fm; step fm
  refine stepStar_trans (ih _ _) ?_; ring_nf; finish

-- Case A: c ≥ e + 2. c = e + r + 2.
theorem trans_A : ∀ e r,
    ⟨0, 0, e + r + 2, 0, e⟩ [fm]⊢⁺ ⟨0, 0, 2 * e + r + 4, 0, 3 * e + 1⟩ := by
  intro e r
  rw [show e + r + 2 = e + r + 1 + 1 from by ring]; step fm
  have h1 := chain_R1R2 e 0 (r + 1) 0 0
  simp only [Nat.zero_add] at h1
  rw [show (r + 1) + e = e + r + 1 from by ring] at h1
  refine stepStar_trans h1 ?_
  step fm
  have h2 := drain_R3 (e + 2) 0 r (3 * e + 1)
  simp only [Nat.zero_add] at h2
  refine stepStar_trans h2 ?_
  have h3 := drain_R4 (3 * e + 1) (r + 2 * (e + 2)) 0 0
  simp only [Nat.zero_add] at h3
  refine stepStar_trans h3 ?_; ring_nf; finish

-- Case B: c = e + 1.
theorem trans_B : ∀ e,
    ⟨0, 0, e + 2, 0, e + 1⟩ [fm]⊢⁺ ⟨0, 0, 2 * e + 5, 0, 3 * e + 4⟩ := by
  intro e
  rw [show e + 2 = e + 1 + 1 from by ring]; step fm
  have h1 := chain_R1R2 (e + 1) 0 0 0 0
  simp only [Nat.zero_add] at h1
  refine stepStar_trans h1 ?_
  step fm; step fm
  have h2 := drain_R3 (e + 2) 0 1 (3 * e + 4)
  simp only [Nat.zero_add] at h2
  refine stepStar_trans h2 ?_
  have h3 := drain_R4 (3 * e + 4) (1 + 2 * (e + 2)) 0 0
  simp only [Nat.zero_add] at h3
  refine stepStar_trans h3 ?_; ring_nf; finish

-- Case C, b even: c = c'+2, e = c'+2K+2, K ≥ 0, c' ≥ 2K+5.
theorem trans_C_even : ∀ c' K, c' ≥ 2 * K + 5 →
    ⟨0, 0, c' + 2, 0, c' + 2 * K + 2⟩ [fm]⊢⁺
    ⟨0, 0, 2 * c' + 2 * K + 6, 0, 3 * c' + 6 * K + 7⟩ := by
  intro c' K hc'
  rw [show c' + 2 = c' + 1 + 1 from by ring]; step fm
  -- chain_R1R2(c'+1)
  have h1 := chain_R1R2 (c' + 1) 0 0 0 (2 * K + 1)
  simp only [Nat.zero_add] at h1
  rw [show (2 * K + 1) + (c' + 1) = c' + 2 * K + 2 from by ring] at h1
  refine stepStar_trans h1 ?_
  have h2 := chain_R2 (2 * K + 1) (c' - 2 * K) 1 (3 * c' + 3) 0
  simp only [Nat.zero_add] at h2
  rw [show (c' - 2 * K) + (2 * K + 1) = c' + 1 from by omega,
      show 1 + (2 * K + 1) = 2 * K + 2 from by ring,
      show 3 * c' + 3 + 2 * (2 * K + 1) = 3 * c' + 4 * K + 5 from by ring] at h2
  refine stepStar_trans h2 ?_
  have h3 := cleanup_even (K + 1) (c' - 2 * K - 1) (3 * c' + 4 * K + 5)
  rw [show (c' - 2 * K - 1) + 1 = c' - 2 * K from by omega,
      show (c' - 2 * K - 1) + 3 * (K + 1) + 1 = c' + K + 3 from by omega,
      show 2 * (K + 1) = 2 * K + 2 from by ring,
      show 3 * c' + 4 * K + 5 + (2 * K + 2) = 3 * c' + 6 * K + 7 from by ring] at h3
  refine stepStar_trans h3 ?_
  -- drain_R3(c'+K+3)
  have h4 := drain_R3 (c' + K + 3) 0 0 (3 * c' + 6 * K + 7)
  simp only [Nat.zero_add] at h4
  refine stepStar_trans h4 ?_
  -- drain_R4
  have h5 := drain_R4 (3 * c' + 6 * K + 7) (0 + 2 * (c' + K + 3)) 0 0
  simp only [Nat.zero_add] at h5
  refine stepStar_trans h5 ?_; ring_nf; finish

-- Case C, b odd: c = c'+2, e = c'+2K+1, K ≥ 1, c' ≥ 2K+4.
theorem trans_C_odd : ∀ c' K, c' ≥ 2 * K + 4 →
    ⟨0, 0, c' + 2, 0, c' + 2 * K + 1⟩ [fm]⊢⁺
    ⟨0, 0, 2 * c' + 2 * K + 5, 0, 3 * c' + 6 * K + 4⟩ := by
  intro c' K hc'
  rw [show c' + 2 = c' + 1 + 1 from by ring]; step fm
  -- chain_R1R2(c'+1)
  have h1 := chain_R1R2 (c' + 1) 0 0 0 (2 * K)
  simp only [Nat.zero_add] at h1
  rw [show 2 * K + (c' + 1) = c' + 2 * K + 1 from by ring] at h1
  refine stepStar_trans h1 ?_
  -- chain_R2(2K)
  have h2 := chain_R2 (2 * K) (c' + 1 - 2 * K) 1 (3 * c' + 3) 0
  simp only [Nat.zero_add] at h2
  rw [show (c' + 1 - 2 * K) + 2 * K = c' + 1 from by omega,
      show 1 + 2 * K = 2 * K + 1 from by ring,
      show 3 * c' + 3 + 2 * (2 * K) = 3 * c' + 4 * K + 3 from by ring] at h2
  refine stepStar_trans h2 ?_
  -- cleanup_odd(K)
  have h3 := cleanup_odd K (c' - 2 * K) (3 * c' + 4 * K + 3)
  rw [show (c' - 2 * K) + 1 = c' + 1 - 2 * K from by omega,
      show (c' - 2 * K) + 3 * K + 2 = c' + K + 2 from by omega,
      show 3 * c' + 4 * K + 3 + 2 * K + 1 = 3 * c' + 6 * K + 4 from by ring] at h3
  refine stepStar_trans h3 ?_
  -- drain_R3(c'+K+2)
  have h4 := drain_R3 (c' + K + 2) 0 1 (3 * c' + 6 * K + 4)
  simp only [Nat.zero_add] at h4
  refine stepStar_trans h4 ?_
  -- drain_R4
  have h5 := drain_R4 (3 * c' + 6 * K + 4) (1 + 2 * (c' + K + 2)) 0 0
  simp only [Nat.zero_add] at h5
  refine stepStar_trans h5 ?_; ring_nf; finish

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨0, 0, 4, 0, 1⟩) (by execute fm 6)
  apply progress_nonhalt (fm := fm)
    (P := fun q ↦ ∃ c e, q = ⟨0, 0, c, 0, e⟩ ∧ 2 * c ≥ e + 7 ∧ e ≥ 1)
  · intro q ⟨c, e, hq, hc, he⟩; subst hq
    rcases (show c ≥ e + 2 ∨ c = e + 1 ∨ c ≤ e from by omega) with h | h | h
    · obtain ⟨r, rfl⟩ : ∃ r, c = e + r + 2 := ⟨c - e - 2, by omega⟩
      exact ⟨⟨0, 0, 2 * e + r + 4, 0, 3 * e + 1⟩,
        ⟨2 * e + r + 4, 3 * e + 1, rfl, by omega, by omega⟩, trans_A e r⟩
    · subst h
      obtain ⟨e', rfl⟩ : ∃ e', e = e' + 1 := ⟨e - 1, by omega⟩
      exact ⟨⟨0, 0, 2 * e' + 5, 0, 3 * e' + 4⟩,
        ⟨2 * e' + 5, 3 * e' + 4, rfl, by omega, by omega⟩, trans_B e'⟩
    · obtain ⟨c', rfl⟩ : ∃ c', c = c' + 2 := ⟨c - 2, by omega⟩
      rcases Nat.even_or_odd (e - c') with ⟨K, hK⟩ | ⟨K, hK⟩
      · have hK1 : K ≥ 1 := by omega
        obtain ⟨K', rfl⟩ : ∃ K', K = K' + 1 := ⟨K - 1, by omega⟩
        have he_eq : e = c' + 2 * K' + 2 := by omega
        rw [he_eq]
        exact ⟨⟨0, 0, 2 * c' + 2 * K' + 6, 0, 3 * c' + 6 * K' + 7⟩,
          ⟨2 * c' + 2 * K' + 6, 3 * c' + 6 * K' + 7, rfl, by omega, by omega⟩,
          trans_C_even c' K' (by omega)⟩
      · have hK1 : K ≥ 1 := by omega
        have he_eq : e = c' + 2 * K + 1 := by omega
        rw [he_eq]
        exact ⟨⟨0, 0, 2 * c' + 2 * K + 5, 0, 3 * c' + 6 * K + 4⟩,
          ⟨2 * c' + 2 * K + 5, 3 * c' + 6 * K + 4, rfl, by omega, by omega⟩,
          trans_C_odd c' K (by omega)⟩
  · exact ⟨4, 1, rfl, by omega, by omega⟩

end Sz22_2003_unofficial_458
