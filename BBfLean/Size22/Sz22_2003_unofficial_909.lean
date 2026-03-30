import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #909: [4/15, 3/14, 275/2, 7/5, 75/11]

Vector representation:
```
 2 -1 -1  0  0
-1  1  0 -1  0
-1  0  2  0  1
 0  0 -1  1  0
 0  1  2  0 -1
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_909

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a, b+1, c+1, d, e⟩ => some ⟨a+2, b, c, d, e⟩
  | ⟨a+1, b, c, d+1, e⟩ => some ⟨a, b+1, c, d, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b, c+2, d, e+1⟩
  | ⟨a, b, c+1, d, e⟩ => some ⟨a, b, c, d+1, e⟩
  | ⟨a, b, c, d, e+1⟩ => some ⟨a, b+1, c+2, d, e⟩
  | _ => none

theorem R3_chain : ∀ A C E, ⟨A, (0 : ℕ), C, (0 : ℕ), E⟩ [fm]⊢* ⟨0, 0, C + 2 * A, 0, E + A⟩ := by
  intro A; induction A with
  | zero => intro C E; simp; exists 0
  | succ A ih =>
    intro C E; step fm
    apply stepStar_trans (ih (C + 2) (E + 1))
    ring_nf; finish

theorem R4_chain : ∀ K D E, ⟨(0 : ℕ), (0 : ℕ), K, D, E⟩ [fm]⊢* ⟨0, 0, 0, D + K, E⟩ := by
  intro K; induction K with
  | zero => intro D E; simp; exists 0
  | succ K ih =>
    intro D E; step fm
    apply stepStar_trans (ih (D + 1) E)
    ring_nf; finish

theorem tail : ∀ B A F, ⟨A + 1, B, (0 : ℕ), (0 : ℕ), F⟩ [fm]⊢*
    ⟨0, 0, 0, 2 * A + 3 * B + 2, F + A + 2 * B + 1⟩ := by
  intro B; induction' B using Nat.strongRecOn with B ih
  intro A F
  rcases B with _ | _ | B
  · apply stepStar_trans (R3_chain (A + 1) 0 F)
    simp only [Nat.zero_add]
    apply stepStar_trans (R4_chain (2 * (A + 1)) 0 (F + (A + 1)))
    ring_nf; finish
  · step fm; step fm
    apply stepStar_trans (R3_chain (A + 2) 1 (F + 1))
    apply stepStar_trans (R4_chain (1 + 2 * (A + 2)) 0 (F + 1 + (A + 2)))
    ring_nf; finish
  · step fm; step fm; step fm
    rw [show A + 4 = (A + 3) + 1 from by ring]
    apply stepStar_trans (ih B (by omega) (A + 3) (F + 1))
    ring_nf; finish

theorem inner_loop : ∀ K B D E, ⟨(0 : ℕ), B + 1, 0, D + 4 * K, E + K⟩ [fm]⊢*
    ⟨0, B + 1 + 3 * K, 0, D, E⟩ := by
  intro K; induction K with
  | zero => intro B D E; simp; exists 0
  | succ K ih =>
    intro B D E
    rw [show D + 4 * (K + 1) = D + 4 * K + 4 from by ring,
        show E + (K + 1) = E + K + 1 from by ring]
    step fm; step fm; step fm; step fm; step fm; step fm; step fm
    rw [show B + 4 = (B + 3) + 1 from by ring]
    apply stepStar_trans (ih (B + 3) D E)
    ring_nf; finish

theorem boundary_r0 : ∀ B E, ⟨(0 : ℕ), B + 1, 0, 0, E + 1⟩ [fm]⊢*
    ⟨0, 0, 0, 3 * B + 8, E + 2 * B + 4⟩ := by
  intro B E
  step fm; step fm; step fm
  rw [show (4 : ℕ) = 3 + 1 from by ring]
  apply stepStar_trans (tail B 3 E)
  ring_nf; finish

theorem boundary_r1 : ∀ B E, ⟨(0 : ℕ), B + 1, 0, 1, E + 1⟩ [fm]⊢*
    ⟨0, 0, 0, 3 * B + 9, E + 2 * B + 5⟩ := by
  intro B E
  step fm; step fm; step fm; step fm
  rw [show (3 : ℕ) = 2 + 1 from by ring]
  apply stepStar_trans (tail (B + 1) 2 E)
  ring_nf; finish

theorem boundary_r2 : ∀ B E, ⟨(0 : ℕ), B + 1, 0, 2, E + 1⟩ [fm]⊢*
    ⟨0, 0, 0, 3 * B + 10, E + 2 * B + 6⟩ := by
  intro B E
  step fm; step fm; step fm; step fm; step fm
  rw [show (2 : ℕ) = 1 + 1 from by ring]
  apply stepStar_trans (tail (B + 2) 1 E)
  ring_nf; finish

theorem boundary_r3 : ∀ B E, ⟨(0 : ℕ), B + 1, 0, 3, E + 1⟩ [fm]⊢*
    ⟨0, 0, 0, 3 * B + 11, E + 2 * B + 7⟩ := by
  intro B E
  step fm; step fm; step fm; step fm; step fm; step fm
  rw [show (1 : ℕ) = 0 + 1 from by ring]
  apply stepStar_trans (tail (B + 3) 0 E)
  ring_nf; finish

theorem trans_d1 : ∀ F, ⟨(0 : ℕ), 0, 0, 1, F + 1⟩ [fm]⊢⁺ ⟨0, 0, 0, 6, F + 3⟩ := by
  intro F
  step fm; step fm; step fm; step fm
  apply stepStar_trans (R3_chain 3 0 F)
  simp only [Nat.zero_add]
  apply stepStar_trans (R4_chain 6 0 (F + 3))
  ring_nf; finish

theorem trans_d2 : ∀ F, ⟨(0 : ℕ), 0, 0, 2, F + 1⟩ [fm]⊢⁺ ⟨0, 0, 0, 7, F + 4⟩ := by
  intro F
  step fm; step fm; step fm; step fm
  step fm
  rw [show (2 : ℕ) = 1 + 1 from by ring]
  apply stepStar_trans (tail 1 1 F)
  ring_nf; finish

theorem trans_d3 : ∀ F, ⟨(0 : ℕ), 0, 0, 3, F + 2⟩ [fm]⊢⁺ ⟨0, 0, 0, 8, F + 6⟩ := by
  intro F
  step fm; step fm; step fm; step fm
  step fm; step fm
  show ⟨0 + 1, 2, 0, 0, F + 1⟩ [fm]⊢* ⟨0, 0, 0, 8, F + 6⟩
  apply stepStar_trans (tail 2 0 (F + 1))
  ring_nf; finish

theorem trans_r0 : ∀ N F, ⟨(0 : ℕ), 0, 0, 4 * N + 4, N + F + 2⟩ [fm]⊢⁺
    ⟨0, 0, 0, 9 * N + 14, F + 6 * N + 8⟩ := by
  intro N F
  step fm; step fm; step fm; step fm
  step fm; step fm; step fm
  rw [show (3 : ℕ) = 2 + 1 from by ring,
      show 4 * N = 0 + 4 * N from by ring,
      show N + F + 1 = (F + 1) + N from by ring]
  apply stepStar_trans (inner_loop N 2 0 (F + 1))
  rw [show 2 + 1 + 3 * N = (2 + 3 * N) + 1 from by ring]
  apply stepStar_trans (boundary_r0 (2 + 3 * N) F)
  ring_nf; finish

theorem trans_r1 : ∀ N F, ⟨(0 : ℕ), 0, 0, 4 * N + 5, N + F + 2⟩ [fm]⊢⁺
    ⟨0, 0, 0, 9 * N + 15, F + 6 * N + 9⟩ := by
  intro N F
  step fm; step fm; step fm; step fm
  step fm; step fm; step fm
  rw [show (3 : ℕ) = 2 + 1 from by ring,
      show 4 * N + 1 = 1 + 4 * N from by ring,
      show N + F + 1 = (F + 1) + N from by ring]
  apply stepStar_trans (inner_loop N 2 1 (F + 1))
  rw [show 2 + 1 + 3 * N = (2 + 3 * N) + 1 from by ring]
  apply stepStar_trans (boundary_r1 (2 + 3 * N) F)
  ring_nf; finish

theorem trans_r2 : ∀ N F, ⟨(0 : ℕ), 0, 0, 4 * N + 6, N + F + 2⟩ [fm]⊢⁺
    ⟨0, 0, 0, 9 * N + 16, F + 6 * N + 10⟩ := by
  intro N F
  step fm; step fm; step fm; step fm
  step fm; step fm; step fm
  rw [show (3 : ℕ) = 2 + 1 from by ring,
      show 4 * N + 2 = 2 + 4 * N from by ring,
      show N + F + 1 = (F + 1) + N from by ring]
  apply stepStar_trans (inner_loop N 2 2 (F + 1))
  rw [show 2 + 1 + 3 * N = (2 + 3 * N) + 1 from by ring]
  apply stepStar_trans (boundary_r2 (2 + 3 * N) F)
  ring_nf; finish

theorem trans_r3 : ∀ N F, ⟨(0 : ℕ), 0, 0, 4 * N + 7, N + F + 2⟩ [fm]⊢⁺
    ⟨0, 0, 0, 9 * N + 17, F + 6 * N + 11⟩ := by
  intro N F
  step fm; step fm; step fm; step fm
  step fm; step fm; step fm
  rw [show (3 : ℕ) = 2 + 1 from by ring,
      show 4 * N + 3 = 3 + 4 * N from by ring,
      show N + F + 1 = (F + 1) + N from by ring]
  apply stepStar_trans (inner_loop N 2 3 (F + 1))
  rw [show 2 + 1 + 3 * N = (2 + 3 * N) + 1 from by ring]
  apply stepStar_trans (boundary_r3 (2 + 3 * N) F)
  ring_nf; finish

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨0, 0, 0, 2, 1⟩) (by execute fm 3)
  apply progress_nonhalt (fm := fm)
    (P := fun q ↦ ∃ d e, q = ⟨0, 0, 0, d, e⟩ ∧ d ≥ 1 ∧ e ≥ 1 ∧ 2 * e ≥ d)
  · intro q ⟨d, e, hq, hd, he, hinv⟩; subst hq
    obtain ⟨d, rfl⟩ : ∃ d', d = d' + 1 := ⟨d - 1, by omega⟩
    obtain ⟨e, rfl⟩ : ∃ e', e = e' + 1 := ⟨e - 1, by omega⟩
    rcases (show d = 0 ∨ d = 1 ∨ d = 2 ∨ d ≥ 3 from by omega) with
      rfl | rfl | rfl | hd3
    · exact ⟨_, ⟨6, e + 3, rfl, by omega, by omega, by omega⟩, trans_d1 e⟩
    · exact ⟨_, ⟨7, e + 4, rfl, by omega, by omega, by omega⟩, trans_d2 e⟩
    · obtain ⟨F, rfl⟩ : ∃ F, e = F + 1 := ⟨e - 1, by omega⟩
      refine ⟨_, ⟨8, F + 6, rfl, by omega, by omega, by omega⟩, ?_⟩
      exact trans_d3 F
    · obtain ⟨d', rfl⟩ : ∃ d', d = 3 + d' := ⟨d - 3, by omega⟩
      obtain ⟨N, r, hr, rfl⟩ : ∃ N r, r < 4 ∧ d' = 4 * N + r :=
        ⟨d' / 4, d' % 4, Nat.mod_lt _ (by omega), (Nat.div_add_mod d' 4).symm⟩
      obtain ⟨F, rfl⟩ : ∃ F, e = N + F + 1 := ⟨e - N - 1, by omega⟩
      rcases (show r = 0 ∨ r = 1 ∨ r = 2 ∨ r = 3 from by omega) with
        rfl | rfl | rfl | rfl
      · refine ⟨_, ⟨9 * N + 14, F + 6 * N + 8, rfl, by omega, by omega, by omega⟩, ?_⟩
        rw [show 3 + (4 * N + 0) + 1 = 4 * N + 4 from by ring,
            show (N + F + 1) + 1 = N + F + 2 from by ring]
        exact trans_r0 N F
      · refine ⟨_, ⟨9 * N + 15, F + 6 * N + 9, rfl, by omega, by omega, by omega⟩, ?_⟩
        rw [show 3 + (4 * N + 1) + 1 = 4 * N + 5 from by ring,
            show (N + F + 1) + 1 = N + F + 2 from by ring]
        exact trans_r1 N F
      · refine ⟨_, ⟨9 * N + 16, F + 6 * N + 10, rfl, by omega, by omega, by omega⟩, ?_⟩
        rw [show 3 + (4 * N + 2) + 1 = 4 * N + 6 from by ring,
            show (N + F + 1) + 1 = N + F + 2 from by ring]
        exact trans_r2 N F
      · refine ⟨_, ⟨9 * N + 17, F + 6 * N + 11, rfl, by omega, by omega, by omega⟩, ?_⟩
        rw [show 3 + (4 * N + 3) + 1 = 4 * N + 7 from by ring,
            show (N + F + 1) + 1 = N + F + 2 from by ring]
        exact trans_r3 N F
  · exact ⟨2, 1, rfl, by omega, by omega, by omega⟩

end Sz22_2003_unofficial_909
