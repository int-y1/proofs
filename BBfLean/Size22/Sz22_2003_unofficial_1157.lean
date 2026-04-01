import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #1157: [5/6, 44/35, 77/2, 3/11, 20/3]

Vector representation:
```
-1 -1  1  0  0
 2  0 -1 -1  1
-1  0  0  1  1
 0  1  0  0 -1
 2 -1  1  0  0
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_1157

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a+1, b+1, c, d, e⟩ => some ⟨a, b, c+1, d, e⟩
  | ⟨a, b, c+1, d+1, e⟩ => some ⟨a+2, b, c, d, e+1⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b, c, d+1, e+1⟩
  | ⟨a, b, c, d, e+1⟩ => some ⟨a, b+1, c, d, e⟩
  | ⟨a, b+1, c, d, e⟩ => some ⟨a+2, b, c+1, d, e⟩
  | _ => none

theorem e_to_b : ∀ k, ∀ b d, ⟨0, b, 0, d, k⟩ [fm]⊢* ⟨0, b + k, 0, d, 0⟩ := by
  intro k; induction k with
  | zero => intros; exists 0
  | succ k ih =>
    intro b d
    step fm
    apply stepStar_trans (ih (b + 1) d)
    ring_nf; finish

theorem e_to_b_c : ∀ k, ∀ b c, ⟨0, b, c + 1, 0, k⟩ [fm]⊢* ⟨0, b + k, c + 1, 0, 0⟩ := by
  intro k; induction k with
  | zero => intros; exists 0
  | succ k ih =>
    intro b c
    step fm
    apply stepStar_trans (ih (b + 1) c)
    ring_nf; finish

theorem r3_drain : ∀ k, ∀ d e, ⟨k, 0, 0, d, e⟩ [fm]⊢* ⟨0, 0, 0, d + k, e + k⟩ := by
  intro k; induction k with
  | zero => intros; exists 0
  | succ k ih =>
    intro d e
    step fm
    apply stepStar_trans (ih (d + 1) (e + 1))
    ring_nf; finish

theorem r1r1r2_chain : ∀ k, ∀ B C D E,
    ⟨2, B + 2 * k, C, D + k, E⟩ [fm]⊢* ⟨2, B, C + k, D, E + k⟩ := by
  intro k; induction k with
  | zero => intros; simp; exists 0
  | succ k ih =>
    intro B C D E
    rw [show B + 2 * (k + 1) = (B + 2) + 2 * k from by ring,
        show D + (k + 1) = (D + 1) + k from by ring]
    apply stepStar_trans (ih (B + 2) C (D + 1) E)
    step fm; step fm; step fm
    ring_nf; finish

theorem r1r1r5_chain : ∀ k, ∀ C,
    ⟨2, 3 * k, C, 0, 0⟩ [fm]⊢* ⟨2, 0, C + 3 * k, 0, 0⟩ := by
  intro k; induction k with
  | zero => intro C; simp; exists 0
  | succ k ih =>
    intro C
    rw [show 3 * (k + 1) = 3 * k + 3 from by ring]
    rw [show (2 : ℕ) = 1 + 1 from rfl,
        show 3 * k + 3 = (3 * k + 2) + 1 from by ring]
    step fm
    rw [show 3 * k + 2 = (3 * k + 1) + 1 from by ring]
    step fm
    rw [show 3 * k + 1 = (3 * k) + 1 from by ring]
    step fm
    apply stepStar_trans (ih (C + 3))
    ring_nf; finish

theorem r3r2_chain : ∀ C, ∀ A E,
    ⟨A + 1, 0, C + 1, 0, E⟩ [fm]⊢* ⟨A + C + 2, 0, 0, 0, E + 2 * (C + 1)⟩ := by
  intro C; induction C with
  | zero =>
    intro A E
    step fm; step fm
    ring_nf; finish
  | succ C ih =>
    intro A E
    step fm
    step fm
    apply stepStar_trans (ih (A + 1) (E + 2))
    ring_nf; finish

theorem main_trans : ∀ n,
    ⟨0, 0, 0, 3 * n + 7, 9 * n + 17⟩ [fm]⊢⁺
    ⟨0, 0, 0, 9 * n + 19, 27 * n + 53⟩ := by
  intro n
  -- Phase 1: R4 transfer e→b: (0,0,0,3n+7,9n+17) →* (0,9n+17,0,3n+7,0)
  apply stepStar_stepPlus_stepPlus
  · exact e_to_b (9 * n + 17) 0 (3 * n + 7)
  -- Phase 2: R5 opening: (0,9n+17,0,3n+7,0) → (2,9n+16,1,3n+7,0)
  apply step_stepStar_stepPlus
  · rw [show 0 + (9 * n + 17) = (9 * n + 16) + 1 from by ring]
    show fm ⟨0, (9 * n + 16) + 1, 0, 3 * n + 7, 0⟩ = some ⟨2, 9 * n + 16, 1, 3 * n + 7, 0⟩
    simp [fm]
  -- Phase 3: R1R1R2 chain for (3n+7) rounds
  apply stepStar_trans
  · show ⟨2, 9 * n + 16, 1, 3 * n + 7, 0⟩ [fm]⊢* ⟨2, 3 * n + 2, 3 * n + 8, 0, 3 * n + 7⟩
    have h := r1r1r2_chain (3 * n + 7) (3 * n + 2) 1 0 0
    simp only [show (3 * n + 2) + 2 * (3 * n + 7) = 9 * n + 16 from by ring,
               show 0 + (3 * n + 7) = 3 * n + 7 from by ring,
               show 1 + (3 * n + 7) = 3 * n + 8 from by ring] at h
    exact h
  -- State: (2, 3n+2, 3n+8, 0, 3n+7)
  -- Phase 4: R1, R1
  rw [show (2 : ℕ) = 1 + 1 from rfl,
      show 3 * n + 2 = (3 * n + 1) + 1 from by ring]
  step fm
  rw [show 3 * n + 1 = (3 * n) + 1 from by ring]
  step fm
  -- State: (0, 3n, 3n+10, 0, 3n+7)
  -- Phase 5: R4 transfer e→b with nonzero c
  rw [show 3 * n + 10 = (3 * n + 9) + 1 from by ring]
  apply stepStar_trans
  · exact e_to_b_c (3 * n + 7) (3 * n) (3 * n + 9)
  -- State: (0, 6n+7, 3n+10, 0, 0)
  -- Phase 6: R5 opening
  rw [show 3 * n + (3 * n + 7) = (6 * n + 6) + 1 from by ring,
      show (3 * n + 9) + 1 = 3 * n + 10 from by ring]
  step fm
  -- State: (2, 6n+6, 3n+11, 0, 0)
  -- Phase 7: R1R1R5 chain for (2n+2) rounds
  rw [show 6 * n + 6 = 3 * (2 * n + 2) from by ring]
  apply stepStar_trans
  · exact r1r1r5_chain (2 * n + 2) (3 * n + 11)
  -- State: (2, 0, 9n+17, 0, 0)
  -- Phase 8: R3R2 chain
  rw [show 3 * n + 11 + 3 * (2 * n + 2) = 9 * n + 17 from by ring,
      show (2 : ℕ) = 1 + 1 from rfl,
      show 9 * n + 17 = (9 * n + 16) + 1 from by ring]
  apply stepStar_trans
  · exact r3r2_chain (9 * n + 16) 1 0
  -- State: (9n+19, 0, 0, 0, 18n+34)
  rw [show 1 + (9 * n + 16) + 2 = 9 * n + 19 from by ring,
      show 0 + 2 * ((9 * n + 16) + 1) = 18 * n + 34 from by ring]
  -- Phase 9: R3 drain
  have h9 := r3_drain (9 * n + 19) 0 (18 * n + 34)
  rw [show 0 + (9 * n + 19) = 9 * n + 19 from by ring,
      show 18 * n + 34 + (9 * n + 19) = 27 * n + 53 from by ring] at h9
  exact h9

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨0, 0, 0, 10, 29⟩)
  · show c₀ [fm]⊢* ⟨0, 0, 0, 10, 29⟩
    execute fm 86
  apply stepStar_not_halts_not_halts (c₂ := ⟨3, 0, 28, 0, 2⟩)
  · show ⟨0, 0, 0, 10, 29⟩ [fm]⊢* ⟨3, 0, 28, 0, 2⟩
    execute fm 90
  apply stepStar_not_halts_not_halts (c₂ := ⟨0, 0, 0, 31, 89⟩)
  · show ⟨3, 0, 28, 0, 2⟩ [fm]⊢* ⟨0, 0, 0, 31, 89⟩
    execute fm 87
  rw [show (0, 0, 0, 31, 89) = (0, 0, 0, 3 * 8 + 7, 9 * 8 + 17) from rfl]
  apply progress_nonhalt_simple (fm := fm) (A := ℕ)
    (fun n ↦ ⟨0, 0, 0, 3 * n + 7, 9 * n + 17⟩) 8
  intro n; exists 3 * n + 4
  rw [show 3 * (3 * n + 4) + 7 = 9 * n + 19 from by ring,
      show 9 * (3 * n + 4) + 17 = 27 * n + 53 from by ring]
  exact main_trans n

end Sz22_2003_unofficial_1157
