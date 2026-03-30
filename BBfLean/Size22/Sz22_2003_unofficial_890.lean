import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #890: [4/15, 147/22, 175/2, 11/7, 3/11]

Vector representation:
```
 2 -1 -1  0  0
-1  1  0  2 -1
-1  0  2  1  0
 0  0  0 -1  1
 0  1  0  0 -1
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_890

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a, b+1, c+1, d, e⟩ => some ⟨a+2, b, c, d, e⟩
  | ⟨a+1, b, c, d, e+1⟩ => some ⟨a, b+1, c, d+2, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b, c+2, d+1, e⟩
  | ⟨a, b, c, d+1, e⟩ => some ⟨a, b, c, d, e+1⟩
  | ⟨a, b, c, d, e+1⟩ => some ⟨a, b+1, c, d, e⟩
  | _ => none

theorem d_to_e : ∀ K E, ⟨(0 : ℕ), 0, C, K, E⟩ [fm]⊢* ⟨0, 0, C, 0, E + K⟩ := by
  intro K; induction K with
  | zero => intro E; exists 0
  | succ K ih =>
    intro E; step fm
    apply stepStar_trans (ih (E + 1))
    refine ⟨0, ?_⟩; simp only [stepNat, Nat.repeat]; ring_nf

theorem R3_drain : ∀ A C D, ⟨A, (0 : ℕ), C, D, 0⟩ [fm]⊢* ⟨0, 0, C + 2 * A, D + A, 0⟩ := by
  intro A; induction A with
  | zero => intro C D; simp; exists 0
  | succ A ih =>
    intro C D; step fm
    apply stepStar_trans (ih (C + 2) (D + 1))
    refine ⟨0, ?_⟩; simp only [stepNat, Nat.repeat]; ring_nf

theorem spiral : ∀ K A C D E, ⟨A + 1, (0 : ℕ), C + K, D, E + K⟩ [fm]⊢* ⟨A + K + 1, 0, C, D + 2 * K, E⟩ := by
  intro K; induction K with
  | zero => intro A C D E; simp; exists 0
  | succ K ih =>
    intro A C D E
    rw [show C + (K + 1) = (C + K) + 1 from by ring,
        show E + (K + 1) = (E + K) + 1 from by ring]
    step fm; step fm
    apply stepStar_trans (ih (A + 1) C (D + 2) E)
    refine ⟨0, ?_⟩; simp only [stepNat, Nat.repeat]; ring_nf

theorem R2_chain : ∀ K A B D, ⟨A + K, B, (0 : ℕ), D, K⟩ [fm]⊢* ⟨A, B + K, 0, D + 2 * K, 0⟩ := by
  intro K; induction K with
  | zero => intro A B D; simp; exists 0
  | succ K ih =>
    intro A B D
    rw [show A + (K + 1) = (A + K) + 1 from by ring]
    step fm
    apply stepStar_trans (ih A (B + 1) (D + 2))
    refine ⟨0, ?_⟩; simp only [stepNat, Nat.repeat]; ring_nf

theorem cleanup : ∀ B A D, ⟨A + 1, B, (0 : ℕ), D, (0 : ℕ)⟩ [fm]⊢* ⟨0, 0, 2 * A + 3 * B + 2, D + A + 2 * B + 1, 0⟩ := by
  intro B; induction' B using Nat.strongRecOn with B ih
  intro A D
  rcases B with _ | _ | B
  · apply stepStar_trans (R3_drain (A + 1) 0 D)
    refine ⟨0, ?_⟩; simp only [stepNat, Nat.repeat]; ring_nf
  · step fm; step fm
    apply stepStar_trans (R3_drain (A + 2) 1 (D + 1))
    refine ⟨0, ?_⟩; simp only [stepNat, Nat.repeat]; ring_nf
  · step fm; step fm; step fm
    apply stepStar_trans (ih B (by omega) (A + 3) (D + 1))
    refine ⟨0, ?_⟩; simp only [stepNat, Nat.repeat]; ring_nf

theorem trans_ge_star : ⟨(0 : ℕ), 0, k + D + 1, D + 1, 0⟩ [fm]⊢* ⟨0, 0, k + 2 * D + 4, 3 * D + 2, 0⟩ := by
  apply stepStar_trans (d_to_e (D + 1) 0 (C := k + D + 1))
  simp only [Nat.zero_add]
  step fm; step fm
  apply stepStar_trans
  · show ⟨2, 0, k + D, 0, D⟩ [fm]⊢* ⟨D + 2, 0, k, 2 * D, 0⟩
    have h := spiral D 1 k 0 0
    simp only [Nat.zero_add] at h
    convert h using 2
    all_goals ring_nf
  apply stepStar_trans (R3_drain (D + 2) k (2 * D))
  refine ⟨0, ?_⟩; simp only [stepNat, Nat.repeat]; ring_nf

theorem trans_ge : ⟨(0 : ℕ), 0, k + D + 1, D + 1, 0⟩ [fm]⊢⁺ ⟨0, 0, k + 2 * D + 4, 3 * D + 2, 0⟩ :=
  stepStar_stepPlus trans_ge_star (by intro h; have := congr_arg (fun q : Q => q.2.2.2.1) h; simp at this; omega)

theorem trans_lt_star : ⟨(0 : ℕ), 0, j + m + 2, 2 * j + m + 3, 0⟩ [fm]⊢* ⟨0, 0, 3 * j + 2 * m + 7, 6 * j + 3 * m + 8, 0⟩ := by
  apply stepStar_trans (d_to_e (2 * j + m + 3) 0 (C := j + m + 2))
  simp only [Nat.zero_add]
  step fm; step fm
  apply stepStar_trans
  · show ⟨2, 0, j + m + 1, 0, 2 * j + m + 2⟩ [fm]⊢* ⟨j + m + 3, 0, 0, 2 * j + 2 * m + 2, j + 1⟩
    have h := spiral (j + m + 1) 1 0 0 (j + 1)
    simp only [Nat.zero_add] at h
    convert h using 2
    all_goals ring_nf
  apply stepStar_trans
  · show ⟨j + m + 3, 0, 0, 2 * j + 2 * m + 2, j + 1⟩ [fm]⊢*
        ⟨m + 2, j + 1, 0, 4 * j + 2 * m + 4, 0⟩
    have h := R2_chain (j + 1) (m + 2) 0 (2 * j + 2 * m + 2)
    convert h using 2
    all_goals ring_nf
  rw [show m + 2 = (m + 1) + 1 from by ring]
  apply stepStar_trans (cleanup (j + 1) (m + 1) (4 * j + 2 * m + 4))
  refine ⟨0, ?_⟩; simp only [stepNat, Nat.repeat]; ring_nf

theorem trans_lt : ⟨(0 : ℕ), 0, j + m + 2, 2 * j + m + 3, 0⟩ [fm]⊢⁺ ⟨0, 0, 3 * j + 2 * m + 7, 6 * j + 3 * m + 8, 0⟩ :=
  stepStar_stepPlus trans_lt_star (by intro h; have := congr_arg (fun q : Q => q.2.2.2.1) h; simp at this; omega)

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨0, 0, 2, 1, 0⟩) (by execute fm 1)
  apply progress_nonhalt (fm := fm)
    (P := fun q ↦ ∃ c d, q = ⟨0, 0, c + 1, d + 1, 0⟩ ∧ d + 2 ≤ 2 * c + 2)
  · intro q ⟨c, d, hq, hinv⟩; subst hq
    rcases (show d ≤ c ∨ c < d from by omega) with hle | hlt
    · obtain ⟨k, rfl⟩ : ∃ k, c = k + d := ⟨c - d, by omega⟩
      exact ⟨⟨0, 0, k + 2 * d + 4, 3 * d + 2, 0⟩,
        ⟨k + 2 * d + 3, 3 * d + 1, rfl, by omega⟩, trans_ge⟩
    · obtain ⟨j, rfl⟩ : ∃ j, d = c + 1 + j := ⟨d - c - 1, by omega⟩
      obtain ⟨m, rfl⟩ : ∃ m, c = j + 1 + m := ⟨c - j - 1, by omega⟩
      refine ⟨⟨0, 0, 3 * j + 2 * m + 7, 6 * j + 3 * m + 8, 0⟩,
        ⟨3 * j + 2 * m + 6, 6 * j + 3 * m + 7, rfl, by omega⟩, ?_⟩
      convert trans_lt (j := j) (m := m) using 2
      all_goals ring_nf
  · exact ⟨1, 0, rfl, by omega⟩
