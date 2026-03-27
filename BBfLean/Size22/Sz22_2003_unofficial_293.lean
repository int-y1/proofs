import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #293: [14/15, 9/77, 25/7, 11/25, 21/2]

Vector representation:
```
 1 -1 -1  1  0
 0  2  0 -1 -1
 0  0  2 -1  0
 0  0 -2  0  1
-1  1  0  1  0
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_293

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a, b+1, c+1, d, e⟩ => some ⟨a+1, b, c, d+1, e⟩
  | ⟨a, b, c, d+1, e+1⟩ => some ⟨a, b+2, c, d, e⟩
  | ⟨a, b, c, d+1, e⟩ => some ⟨a, b, c+2, d, e⟩
  | ⟨a, b, c+2, d, e⟩ => some ⟨a, b, c, d, e+1⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b+1, c, d+1, e⟩
  | _ => none

theorem r4_chain (K : ℕ) : ⟨A, 0, C + 2*K, 0, E⟩ [fm]⊢* ⟨A, (0:ℕ), C, 0, E + K⟩ := by
  induction K generalizing C E with
  | zero => simp; exists 0
  | succ K ih =>
    rw [show C + 2 * (K + 1) = (C + 2) + 2 * K from by ring]
    apply stepStar_trans (ih (C := C + 2) (E := E))
    rw [show C + 2 = C + (1 + 1) from by ring]; step fm
    rw [show E + K + 1 = E + (K + 1) from by ring]; finish

theorem r3_chain (K : ℕ) : ⟨A, 0, C, D + K, 0⟩ [fm]⊢* ⟨A, (0:ℕ), C + 2*K, D, 0⟩ := by
  induction K generalizing C D with
  | zero => simp; exists 0
  | succ K ih =>
    rw [show D + (K + 1) = (D + K) + 1 from by ring]; step fm
    apply stepStar_trans (ih (C := C + 2) (D := D))
    rw [show C + 2 + 2 * K = C + 2 * (K + 1) from by ring]; finish

theorem r1_chain (K : ℕ) : ⟨A, B + K, C + K, D, E⟩ [fm]⊢* ⟨A + K, B, C, D + K, E⟩ := by
  induction K generalizing A B C D E with
  | zero => exists 0
  | succ K ih =>
    rw [show B + (K + 1) = (B + K) + 1 from by ring,
        show C + (K + 1) = (C + K) + 1 from by ring]; step fm
    apply stepStar_trans (ih (A := A + 1) (D := D + 1))
    rw [show A + 1 + K = A + (K + 1) from by ring,
        show D + 1 + K = D + (K + 1) from by ring]; finish

theorem r5_r2_drain (K : ℕ) : ⟨A + K, B, 0, 0, K⟩ [fm]⊢* ⟨A, B + 3*K, (0:ℕ), 0, 0⟩ := by
  induction K generalizing A B with
  | zero => simp; exists 0
  | succ K ih =>
    rw [show A + (K + 1) = (A + K) + 1 from by ring]; step fm; step fm
    apply stepStar_trans (ih (A := A) (B := B + 3))
    rw [show B + 3 + 3 * K = B + 3 * (K + 1) from by ring]; finish

theorem r5_sym : fm ⟨A + 1, B, 0, 0, 0⟩ = some ⟨A, B + 1, 0, 1, 0⟩ := by cases B <;> rfl
theorem r3_sym : fm ⟨A, B, 0, D + 1, 0⟩ = some ⟨A, B, 2, D, 0⟩ := by cases B <;> rfl

private theorem mk_eq {a₁ a₂ b₁ b₂ c₁ c₂ d₁ d₂ e₁ e₂ : ℕ}
    (ha : a₁ = a₂) (hb : b₁ = b₂) (hc : c₁ = c₂) (hd : d₁ = d₂) (he : e₁ = e₂) :
    (a₁, b₁, c₁, d₁, e₁) = (a₂, b₂, c₂, d₂, e₂) := by subst_vars; rfl

theorem expand_general : ⟨A, B + 1, 2, D, 0⟩ [fm]⊢* ⟨A + B + 1, (0:ℕ), 2*D + B + 3, 0, 0⟩ := by
  induction' B using Nat.strongRecOn with B ih generalizing A D
  match B with
  | 0 =>
    have h1 := r1_chain (A := A) (B := 0) (C := 1) (D := D) (E := 0) 1
    simp only [Nat.zero_add] at h1; apply stepStar_trans h1
    have h2 := r3_chain (A := A + 1) (C := 1) (D := 0) (K := D + 1)
    simp only [Nat.zero_add] at h2; apply stepStar_trans h2
    rw [show 1 + 2 * (D + 1) = 2 * D + 0 + 3 from by ring]; finish
  | 1 =>
    rw [show (1 : ℕ) + 1 = 2 from by ring]
    have h1 := r1_chain (A := A) (B := 0) (C := 0) (D := D) (E := 0) 2
    simp only [Nat.zero_add] at h1; apply stepStar_trans h1
    have h2 := r3_chain (A := A + 2) (C := 0) (D := 0) (K := D + 2)
    simp only [Nat.zero_add] at h2
    rw [show 2 * D + 1 + 3 = 2 * (D + 2) from by ring,
        show A + 1 + 1 = A + 2 from by ring]
    exact h2
  | B + 2 =>
    rw [show B + 2 + 1 = (B + 1) + 2 from by ring]
    have hs := r1_chain (A := A) (B := B + 1) (C := 0) (D := D) (E := 0) 2
    simp only [Nat.zero_add] at hs; apply stepStar_trans hs
    rw [show D + 2 = (D + 1) + 1 from by ring]; step fm
    have h := ih B (by omega) (A := A + 2) (D := D + 1)
    rw [show A + 2 + B + 1 = A + (B + 2) + 1 from by ring,
        show 2 * (D + 1) + B + 3 = 2 * D + (B + 2) + 3 from by ring] at h
    exact h

-- K=1 odd case: done by concrete execution
theorem main_odd_1 (hA : A ≥ 1) :
    ⟨A, 0, 3, 0, 0⟩ [fm]⊢⁺ ⟨A + 2, (0:ℕ), 4, 0, 0⟩ := by
  -- Manually step through: R4, R5, R1, R2, R3, expand(2)
  rw [show (3 : ℕ) = 1 + 2 * 1 from by ring]
  apply stepStar_stepPlus_stepPlus (r4_chain (A := A) (C := 1) (E := 0) 1)
  simp only [Nat.zero_add]
  rw [show A = (A - 1) + 1 from by omega]; step fm  -- R5
  rw [show (1 : ℕ) = 0 + 1 from by ring]; step fm  -- R1
  rw [show A - 1 + 1 = A from by omega,
      show (2 : ℕ) = (0 + 1) + 1 from by ring, show (1 : ℕ) = 0 + 1 from by ring]
  step fm  -- R2
  rw [show (1 : ℕ) = 0 + 1 from by ring]; step fm  -- R3
  -- Now at (A, 2, 2, 0, 0). Apply expand with B=1, D=0.
  rw [show (2 : ℕ) = 1 + 1 from by ring]
  apply stepStar_trans (expand_general (A := A) (B := 1) (D := 0))
  rw [show 2 * 0 + 1 + 3 = 4 from by ring,
      show A + 1 + 1 = A + 2 from by ring]; finish

-- K >= 2 odd case
theorem main_odd_ge2 (hK : K ≥ 2) (hA : A ≥ K) :
    ⟨A, 0, 2*K + 1, 0, 0⟩ [fm]⊢⁺ ⟨A + 2*K, (0:ℕ), 3*K + 1, 0, 0⟩ := by
  -- Phase 1: R4(K)
  rw [show 2 * K + 1 = 1 + 2 * K from by ring]
  apply stepStar_stepPlus_stepPlus (r4_chain (A := A) (C := 1) (E := 0) K)
  simp only [Nat.zero_add]
  -- Phase 2: R5, R1
  rw [show A = (A - 1) + 1 from by omega]; step fm
  rw [show (1 : ℕ) = 0 + 1 from by ring]; step fm
  rw [show A - 1 + 1 = A from by omega]
  -- Phase 3: 2 R2 steps
  rw [show (2 : ℕ) = (0 + 1) + 1 from by ring, show K = (K - 1) + 1 from by omega]
  step fm  -- R2: (A, 2, 0, 1, K-1)
  rw [show K - 1 = (K - 2) + 1 from by omega]; step fm  -- R2: (A, 4, 0, 0, K-2)
  -- Phase 4: drain
  rw [show A = (A - (K - 2)) + (K - 2) from by omega]
  apply stepStar_trans (r5_r2_drain (A := A - (K - 2)) (B := 4) (K - 2))
  -- Phase 5: R5 (symbolic b)
  rw [show A - (K - 2) = (A - (K - 2) - 1) + 1 from by omega]
  apply stepStar_trans (step_stepStar (r5_sym (A := A - (K - 2) - 1) (B := 4 + 3 * (K - 2))))
  -- Phase 6: R3 (symbolic b)
  apply stepStar_trans (step_stepStar (r3_sym (A := A - (K - 2) - 1) (B := 4 + 3 * (K - 2) + 1) (D := 0)))
  -- Phase 7: expand
  rw [show 4 + 3 * (K - 2) + 1 = (4 + 3 * (K - 2)) + 1 from by ring]
  apply stepStar_trans (expand_general (A := A - (K - 2) - 1) (B := 4 + 3 * (K - 2)) (D := 0))
  -- Simplify to target
  exists 0; show some _ = some _; congr 1
  exact mk_eq (by omega) rfl (by omega) rfl rfl

-- Even case
theorem main_even (hA : A ≥ K + 1) (_hK : K ≥ 2) :
    ⟨A, 0, 2*K, 0, 0⟩ [fm]⊢⁺ ⟨A + 2*K, (0:ℕ), 3*K + 3, 0, 0⟩ := by
  -- Phase 1: R4(K)
  rw [show 2 * K = 0 + 2 * K from by ring]
  apply stepStar_stepPlus_stepPlus (r4_chain (A := A) (C := 0) (E := 0) K)
  simp only [Nat.zero_add]
  -- Phase 2: drain
  rw [show A = (A - K) + K from by omega]
  apply stepStar_stepPlus_stepPlus (r5_r2_drain (A := A - K) (B := 0) K)
  rw [show 0 + 3 * K = 3 * K from by ring]
  -- Phase 3: R5 (symbolic b)
  rw [show A - K = (A - K - 1) + 1 from by omega]
  apply stepPlus_stepStar_stepPlus (step_stepPlus (r5_sym (A := A - K - 1) (B := 3 * K)))
  -- Phase 4: R3 (symbolic b)
  apply stepStar_trans (step_stepStar (r3_sym (A := A - K - 1) (B := 3 * K + 1) (D := 0)))
  -- Phase 5: expand
  rw [show 3 * K + 1 = (3 * K) + 1 from by ring]
  apply stepStar_trans (expand_general (A := A - K - 1) (B := 3 * K) (D := 0))
  exists 0; show some _ = some _; congr 1
  exact mk_eq (by omega) rfl (by ring) rfl rfl


theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨1, 0, 3, 0, 0⟩) (by execute fm 4)
  apply progress_nonhalt (fm := fm)
    (P := fun q ↦ ∃ A K,
      (q = ⟨A, 0, 2*K + 1, 0, 0⟩ ∧ A ≥ K ∧ K ≥ 1) ∨
      (q = ⟨A, 0, 2*K, 0, 0⟩ ∧ A ≥ K + 1 ∧ K ≥ 2))
  · intro q ⟨A, K, h⟩
    rcases h with ⟨hq, hA, hK⟩ | ⟨hq, hA, hK⟩
    · -- Odd case
      subst hq
      rcases Nat.eq_or_lt_of_le hK with rfl | hK2
      · exact ⟨_, ⟨A + 2, 2, Or.inr ⟨by ring_nf, by omega, by omega⟩⟩, main_odd_1 hA⟩
      · rcases Nat.even_or_odd K with ⟨M, hM⟩ | ⟨M, hM⟩
        · subst hM  -- K = M + M, even
          refine ⟨_, ⟨A + 2*(M+M), 3*M, Or.inl ⟨?_, by omega, by omega⟩⟩,
                 main_odd_ge2 (by omega) (by omega)⟩
          exact mk_eq rfl rfl (by ring) rfl rfl
        · subst hM  -- K = 2*M+1, odd
          refine ⟨_, ⟨A + 2*(2*M+1), 3*M+2, Or.inr ⟨?_, by omega, by omega⟩⟩,
                 main_odd_ge2 (by omega) (by omega)⟩
          exact mk_eq rfl rfl (by ring) rfl rfl
    · -- Even case
      subst hq
      rcases Nat.even_or_odd K with ⟨M, hM⟩ | ⟨M, hM⟩
      · subst hM  -- K = M+M, even
        refine ⟨_, ⟨A + 2*(M+M), 3*M+1, Or.inl ⟨?_, by omega, by omega⟩⟩,
               main_even hA hK⟩
        exact mk_eq rfl rfl (by ring) rfl rfl
      · subst hM  -- K = 2*M+1, odd
        refine ⟨_, ⟨A + 2*(2*M+1), 3*M+3, Or.inr ⟨?_, by omega, by omega⟩⟩,
               main_even hA hK⟩
        exact mk_eq rfl rfl (by ring) rfl rfl
  · exact ⟨1, 1, Or.inl ⟨rfl, by omega, by omega⟩⟩

end Sz22_2003_unofficial_293
