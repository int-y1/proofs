import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #1889: [9/35, 5/33, 98/3, 11/7, 245/2]

Vector representation:
```
 0  2 -1 -1  0
 0 -1  1  0 -1
 1 -1  0  2  0
 0  0  0 -1  1
-1  0  1  2  0
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_1889

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a, b, c+1, d+1, e⟩ => some ⟨a, b+2, c, d, e⟩
  | ⟨a, b+1, c, d, e+1⟩ => some ⟨a, b, c+1, d, e⟩
  | ⟨a, b+1, c, d, e⟩ => some ⟨a+1, b, c, d+2, e⟩
  | ⟨a, b, c, d+1, e⟩ => some ⟨a, b, c, d, e+1⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b, c+1, d+2, e⟩
  | _ => none

theorem d_to_e : ∀ k d, ⟨a, 0, 0, d + k, 0⟩ [fm]⊢* ⟨a, 0, 0, d, k⟩ := by
  intro k; induction k with
  | zero => intro d; exists 0
  | succ k ih =>
    intro d; rw [show d + (k + 1) = (d + 1) + k from by ring]
    apply stepStar_trans (ih (d + 1)); step fm; finish

theorem r3_chain : ∀ b, ∀ a d, ⟨a, b, 0, d, 0⟩ [fm]⊢* ⟨a + b, 0, 0, d + 2 * b, 0⟩ := by
  intro b; induction b with
  | zero => intro a d; exists 0
  | succ b ih =>
    intro a d; step fm
    apply stepStar_trans (ih (a + 1) (d + 2))
    ring_nf; finish

theorem r1_chain : ∀ k b c d, ⟨a, b, c + k, d + k, 0⟩ [fm]⊢* ⟨a, b + 2 * k, c, d, 0⟩ := by
  intro k; induction k with
  | zero => intro b c d; exists 0
  | succ k ih =>
    intro b c d
    rw [show c + (k + 1) = (c + k) + 1 from by ring,
        show d + (k + 1) = (d + k) + 1 from by ring]
    step fm; apply stepStar_trans (ih (b + 2) c d); ring_nf; finish

theorem r3r1_drain : ∀ c a b, ⟨a, b + 1, c, 0, 0⟩ [fm]⊢* ⟨a + b + 2 * c + 1, 0, 0, 2 * b + 3 * c + 2, 0⟩ := by
  intro c; induction c using Nat.strongRecOn with
  | ind c ih =>
    intro a b; rcases c with _ | _ | c
    · show ⟨a, b + 1, 0, 0, 0⟩ [fm]⊢* ⟨a + b + 1, 0, 0, 2 * b + 2, 0⟩
      rw [show a + b + 1 = a + (b + 1) from by ring,
          show 2 * b + 2 = 0 + 2 * (b + 1) from by ring]
      exact r3_chain (b + 1) a 0
    · step fm
      apply stepStar_trans (r1_chain 1 b 0 1 (a := a + 1))
      rw [show b + 2 * 1 = b + 2 from by ring]
      apply stepStar_trans (r3_chain (b + 2) 1 (a := a + 1))
      ring_nf; finish
    · step fm
      apply stepStar_trans (r1_chain 2 b c 0 (a := a + 1))
      rw [show b + 2 * 2 = (b + 3) + 1 from by ring]
      apply stepStar_trans (ih c (by omega) (a + 1) (b + 3))
      ring_nf; finish

theorem spiral_round_0 : ⟨a + 1, 0, 0, 0, e + 4⟩ [fm]⊢* ⟨a, 0, 3, 0, e⟩ := by
  execute fm 7

theorem spiral_round : ⟨a + 1, 0, c + 3, 0, e + 4⟩ [fm]⊢* ⟨a, 0, c + 6, 0, e⟩ := by
  step fm; rw [show c + 4 = (c + 3) + 1 from by ring]
  step fm; step fm; step fm; step fm; step fm; step fm; finish

theorem spiral_chain : ∀ k, ∀ a r, ⟨a + k, 0, 0, 0, 4 * k + r⟩ [fm]⊢* ⟨a, 0, 3 * k, 0, r⟩ := by
  intro k; induction k with
  | zero => intro a r; ring_nf; exists 0
  | succ k ih =>
    intro a r
    rw [show a + (k + 1) = (a + 1) + k from by ring,
        show 4 * (k + 1) + r = 4 * k + (r + 4) from by ring]
    apply stepStar_trans (ih (a + 1) (r + 4))
    show ⟨a + 1, 0, 3 * k, 0, r + 4⟩ [fm]⊢* ⟨a, 0, 3 * (k + 1), 0, r⟩
    rw [show 3 * (k + 1) = 3 * k + 3 from by ring]
    rcases k with _ | k
    · show ⟨a + 1, 0, 0, 0, r + 4⟩ [fm]⊢* ⟨a, 0, 3, 0, r⟩
      exact spiral_round_0
    · rw [show 3 * (k + 1) = 3 * k + 3 from by ring]
      exact spiral_round (a := a) (c := 3 * k) (e := r)

theorem end_game_r0_k0 : ⟨a + 1, 0, 0, 0, 0⟩ [fm]⊢⁺ ⟨a + 2, 0, 0, 5, 0⟩ := by
  execute fm 4

theorem end_game_r1_k0 : ⟨a + 1, 0, 0, 0, 1⟩ [fm]⊢⁺ ⟨a + 3, 0, 0, 6, 0⟩ := by
  execute fm 7

theorem end_game_r2_k0 : ⟨a + 1, 0, 0, 0, 2⟩ [fm]⊢⁺ ⟨a + 4, 0, 0, 7, 0⟩ := by
  step fm; step fm; step fm; step fm; step fm
  show ⟨a, 2, 1, 0, 0⟩ [fm]⊢* ⟨a + 4, 0, 0, 7, 0⟩
  rw [show (2 : ℕ) = 1 + 1 from by ring]
  apply stepStar_trans (r3r1_drain 1 a 1); ring_nf; finish

theorem end_game_r3_k0 : ⟨a + 1, 0, 0, 0, 3⟩ [fm]⊢⁺ ⟨a + 5, 0, 0, 8, 0⟩ := by
  step fm; step fm; step fm; step fm; step fm; step fm
  show ⟨a, 1, 2, 0, 0⟩ [fm]⊢* ⟨a + 5, 0, 0, 8, 0⟩
  rw [show (1 : ℕ) = 0 + 1 from by ring]
  apply stepStar_trans (r3r1_drain 2 a 0); ring_nf; finish

theorem end_game_r0 : ⟨a + 1, 0, 3 * (k + 1), 0, 0⟩ [fm]⊢⁺ ⟨a + 6 * k + 8, 0, 0, 9 * k + 14, 0⟩ := by
  rw [show 3 * (k + 1) = (3 * k + 2) + 1 from by ring]
  step fm; rw [show 3 * k + 2 + 1 + 1 = (3 * k + 2) + 1 + 1 from by ring]
  step fm; step fm
  show ⟨a, 3 + 1, 3 * k + 2, 0, 0⟩ [fm]⊢* ⟨a + 6 * k + 8, 0, 0, 9 * k + 14, 0⟩
  apply stepStar_trans (r3r1_drain (3 * k + 2) a 3); ring_nf; finish

theorem end_game_r1 : ⟨a + 1, 0, 3 * (k + 1), 0, 1⟩ [fm]⊢⁺ ⟨a + 6 * k + 9, 0, 0, 9 * k + 15, 0⟩ := by
  rw [show 3 * (k + 1) = (3 * k + 2) + 1 from by ring]
  step fm; rw [show 3 * k + 2 + 1 + 1 = (3 * k + 2) + 1 + 1 from by ring]
  step fm; step fm; step fm
  rw [show 3 * k + 2 + 1 = 3 * (k + 1) from by ring]
  show ⟨a, 2 + 1, 3 * (k + 1), 0, 0⟩ [fm]⊢* ⟨a + 6 * k + 9, 0, 0, 9 * k + 15, 0⟩
  apply stepStar_trans (r3r1_drain (3 * (k + 1)) a 2); ring_nf; finish

theorem end_game_r2 : ⟨a + 1, 0, 3 * (k + 1), 0, 2⟩ [fm]⊢⁺ ⟨a + 6 * k + 10, 0, 0, 9 * k + 16, 0⟩ := by
  rw [show 3 * (k + 1) = (3 * k + 2) + 1 from by ring]
  step fm; rw [show 3 * k + 2 + 1 + 1 = (3 * k + 2) + 1 + 1 from by ring]
  step fm; step fm; step fm; step fm
  rw [show 3 * k + 2 + 1 + 1 = 3 * k + 4 from by ring]
  show ⟨a, 1 + 1, 3 * k + 4, 0, 0⟩ [fm]⊢* ⟨a + 6 * k + 10, 0, 0, 9 * k + 16, 0⟩
  apply stepStar_trans (r3r1_drain (3 * k + 4) a 1); ring_nf; finish

theorem end_game_r3 : ⟨a + 1, 0, 3 * (k + 1), 0, 3⟩ [fm]⊢⁺ ⟨a + 6 * k + 11, 0, 0, 9 * k + 17, 0⟩ := by
  rw [show 3 * (k + 1) = (3 * k + 2) + 1 from by ring]
  step fm; rw [show 3 * k + 2 + 1 + 1 = (3 * k + 2) + 1 + 1 from by ring]
  step fm; step fm; step fm; step fm; step fm
  rw [show 3 * k + 2 + 1 + 1 + 1 = 3 * k + 5 from by ring]
  show ⟨a, 0 + 1, 3 * k + 5, 0, 0⟩ [fm]⊢* ⟨a + 6 * k + 11, 0, 0, 9 * k + 17, 0⟩
  apply stepStar_trans (r3r1_drain (3 * k + 5) a 0); ring_nf; finish

theorem main_trans_r0 :
    ⟨a + k + 2, 0, 0, 4 * k + 4, 0⟩ [fm]⊢⁺ ⟨a + 6 * k + 8, 0, 0, 9 * k + 14, 0⟩ := by
  rw [show 4 * k + 4 = 0 + (4 * (k + 1) + 0) from by ring]
  apply stepStar_stepPlus_stepPlus (d_to_e (4 * (k + 1) + 0) 0 (a := a + k + 2))
  rw [show a + k + 2 = (a + 1) + (k + 1) from by ring]
  apply stepStar_stepPlus_stepPlus (spiral_chain (k + 1) (a + 1) 0)
  exact end_game_r0

theorem main_trans_r1 :
    ⟨a + k + 2, 0, 0, 4 * k + 5, 0⟩ [fm]⊢⁺ ⟨a + 6 * k + 9, 0, 0, 9 * k + 15, 0⟩ := by
  rw [show 4 * k + 5 = 0 + (4 * (k + 1) + 1) from by ring]
  apply stepStar_stepPlus_stepPlus (d_to_e (4 * (k + 1) + 1) 0 (a := a + k + 2))
  rw [show a + k + 2 = (a + 1) + (k + 1) from by ring]
  apply stepStar_stepPlus_stepPlus (spiral_chain (k + 1) (a + 1) 1)
  exact end_game_r1

theorem main_trans_r2 :
    ⟨a + k + 2, 0, 0, 4 * k + 6, 0⟩ [fm]⊢⁺ ⟨a + 6 * k + 10, 0, 0, 9 * k + 16, 0⟩ := by
  rw [show 4 * k + 6 = 0 + (4 * (k + 1) + 2) from by ring]
  apply stepStar_stepPlus_stepPlus (d_to_e (4 * (k + 1) + 2) 0 (a := a + k + 2))
  rw [show a + k + 2 = (a + 1) + (k + 1) from by ring]
  apply stepStar_stepPlus_stepPlus (spiral_chain (k + 1) (a + 1) 2)
  exact end_game_r2

theorem main_trans_r3 :
    ⟨a + k + 2, 0, 0, 4 * k + 7, 0⟩ [fm]⊢⁺ ⟨a + 6 * k + 11, 0, 0, 9 * k + 17, 0⟩ := by
  rw [show 4 * k + 7 = 0 + (4 * (k + 1) + 3) from by ring]
  apply stepStar_stepPlus_stepPlus (d_to_e (4 * (k + 1) + 3) 0 (a := a + k + 2))
  rw [show a + k + 2 = (a + 1) + (k + 1) from by ring]
  apply stepStar_stepPlus_stepPlus (spiral_chain (k + 1) (a + 1) 3)
  exact end_game_r3

theorem main_trans_d0 :
    ⟨a + 1, 0, 0, 0, 0⟩ [fm]⊢⁺ ⟨a + 2, 0, 0, 5, 0⟩ := end_game_r0_k0

theorem main_trans_d1 :
    ⟨a + 1, 0, 0, 1, 0⟩ [fm]⊢⁺ ⟨a + 3, 0, 0, 6, 0⟩ := by
  step fm
  show ⟨a + 1, 0, 0, 0, 1⟩ [fm]⊢* ⟨a + 3, 0, 0, 6, 0⟩
  exact stepPlus_stepStar end_game_r1_k0

theorem main_trans_d2 :
    ⟨a + 1, 0, 0, 2, 0⟩ [fm]⊢⁺ ⟨a + 4, 0, 0, 7, 0⟩ := by
  rw [show (2 : ℕ) = 0 + 2 from by ring]
  apply stepStar_stepPlus_stepPlus (d_to_e 2 0 (a := a + 1))
  exact end_game_r2_k0

theorem main_trans_d3 :
    ⟨a + 1, 0, 0, 3, 0⟩ [fm]⊢⁺ ⟨a + 5, 0, 0, 8, 0⟩ := by
  rw [show (3 : ℕ) = 0 + 3 from by ring]
  apply stepStar_stepPlus_stepPlus (d_to_e 3 0 (a := a + 1))
  exact end_game_r3_k0

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨2, 0, 0, 5, 0⟩) (by execute fm 4)
  apply progress_nonhalt (fm := fm)
    (P := fun q ↦ ∃ a d, q = ⟨a, 0, 0, d, 0⟩ ∧ a ≥ 2 ∧ d < 4 * a)
  · intro c ⟨a, d, hq, ha, hd⟩; subst hq
    rcases d with _ | _ | _ | _ | d
    · obtain ⟨m, rfl⟩ : ∃ m, a = m + 1 := ⟨a - 1, by omega⟩
      exact ⟨_, ⟨m + 2, 5, rfl, by omega, by omega⟩, main_trans_d0⟩
    · obtain ⟨m, rfl⟩ : ∃ m, a = m + 1 := ⟨a - 1, by omega⟩
      exact ⟨_, ⟨m + 3, 6, rfl, by omega, by omega⟩, main_trans_d1⟩
    · obtain ⟨m, rfl⟩ : ∃ m, a = m + 1 := ⟨a - 1, by omega⟩
      exact ⟨_, ⟨m + 4, 7, rfl, by omega, by omega⟩, main_trans_d2⟩
    · obtain ⟨m, rfl⟩ : ∃ m, a = m + 1 := ⟨a - 1, by omega⟩
      exact ⟨_, ⟨m + 5, 8, rfl, by omega, by omega⟩, main_trans_d3⟩
    · obtain ⟨k, rfl | rfl | rfl | rfl⟩ : ∃ k, d = 4 * k ∨ d = 4 * k + 1 ∨ d = 4 * k + 2 ∨ d = 4 * k + 3 :=
        ⟨d / 4, by omega⟩
      · obtain ⟨m, rfl⟩ : ∃ m, a = m + k + 2 := ⟨a - k - 2, by omega⟩
        exact ⟨_, ⟨m + 6 * k + 8, 9 * k + 14, rfl, by omega, by omega⟩, main_trans_r0⟩
      · obtain ⟨m, rfl⟩ : ∃ m, a = m + k + 2 := ⟨a - k - 2, by omega⟩
        exact ⟨_, ⟨m + 6 * k + 9, 9 * k + 15, rfl, by omega, by omega⟩, main_trans_r1⟩
      · obtain ⟨m, rfl⟩ : ∃ m, a = m + k + 2 := ⟨a - k - 2, by omega⟩
        exact ⟨_, ⟨m + 6 * k + 10, 9 * k + 16, rfl, by omega, by omega⟩, main_trans_r2⟩
      · obtain ⟨m, rfl⟩ : ∃ m, a = m + k + 2 := ⟨a - k - 2, by omega⟩
        exact ⟨_, ⟨m + 6 * k + 11, 9 * k + 17, rfl, by omega, by omega⟩, main_trans_r3⟩
  · exact ⟨2, 5, rfl, by omega, by omega⟩
