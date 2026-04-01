import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #1465: [7/15, 3/77, 50/7, 11/5, 3773/2]

Vector representation:
```
 0 -1 -1  1  0
 0  1  0 -1 -1
 1  0  2 -1  0
 0  0 -1  0  1
-1  0  0  3  1
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_1465

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a, b+1, c+1, d, e⟩ => some ⟨a, b, c, d+1, e⟩
  | ⟨a, b, c, d+1, e+1⟩ => some ⟨a, b+1, c, d, e⟩
  | ⟨a, b, c, d+1, e⟩ => some ⟨a+1, b, c+2, d, e⟩
  | ⟨a, b, c+1, d, e⟩ => some ⟨a, b, c, d, e+1⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b, c, d+3, e+1⟩
  | _ => none

theorem r5_step (a b e : ℕ) :
    (⟨a + 1, b, 0, 0, e⟩ : Q) [fm]⊢ ⟨a, b, 0, 3, e + 1⟩ := by
  show fm ⟨a + 1, b, 0, 0, e⟩ = some ⟨a, b, 0, 3, e + 1⟩; simp [fm]

theorem r2_step (a b d e : ℕ) :
    (⟨a, b, 0, d + 1, e + 1⟩ : Q) [fm]⊢ ⟨a, b + 1, 0, d, e⟩ := by
  show fm ⟨a, b, 0, d + 1, e + 1⟩ = some ⟨a, b + 1, 0, d, e⟩; simp [fm]

theorem r3_step_c0 (a b d : ℕ) :
    (⟨a, b, 0, d + 1, 0⟩ : Q) [fm]⊢ ⟨a + 1, b, 2, d, 0⟩ := by
  show fm ⟨a, b, 0, d + 1, 0⟩ = some ⟨a + 1, b, 2, d, 0⟩; simp [fm]

theorem r1_step (a b c d e : ℕ) :
    (⟨a, b + 1, c + 1, d, e⟩ : Q) [fm]⊢ ⟨a, b, c, d + 1, e⟩ := by
  show fm ⟨a, b + 1, c + 1, d, e⟩ = some ⟨a, b, c, d + 1, e⟩; simp [fm]

theorem r5r2x3_drain : ∀ k, ∀ a b e,
    (⟨a + k, b, 0, 0, e + 2 * k⟩ : Q) [fm]⊢* ⟨a, b + 3 * k, 0, 0, e⟩ := by
  intro k; induction k with
  | zero => intro a b e; ring_nf; finish
  | succ k ih =>
    intro a b e
    rw [show a + (k + 1) = (a + k) + 1 from by ring,
        show e + 2 * (k + 1) = (e + 2 * k) + 1 + 1 from by ring]
    apply stepStar_trans (step_stepStar (r5_step (a + k) b _))
    rw [show (e + 2 * k) + 1 + 1 + 1 = ((e + 2 * k) + 1 + 1) + 1 from by ring,
        show (3 : ℕ) = (1 + 1) + 1 from by ring]
    apply stepStar_trans (step_stepStar (r2_step (a + k) b (1 + 1) ((e + 2 * k) + 1 + 1)))
    apply stepStar_trans (step_stepStar (r2_step (a + k) (b + 1) 1 ((e + 2 * k) + 1)))
    rw [show (1 : ℕ) = 0 + 1 from by ring]
    apply stepStar_trans (step_stepStar (r2_step (a + k) (b + 2) 0 (e + 2 * k)))
    apply stepStar_trans (ih a (b + 3) e)
    ring_nf; finish

theorem r3_chain : ∀ k, ∀ a c d,
    (⟨a, 0, c, d + k, 0⟩ : Q) [fm]⊢* ⟨a + k, 0, c + 2 * k, d, 0⟩ := by
  intro k; induction k with
  | zero => intro a c d; ring_nf; finish
  | succ k ih =>
    intro a c d
    rw [show d + (k + 1) = (d + k) + 1 from by ring]
    step fm
    apply stepStar_trans (ih (a + 1) (c + 2) d)
    ring_nf; finish

theorem c_to_e : ∀ k, ∀ a c e,
    (⟨a, 0, c + k, 0, e⟩ : Q) [fm]⊢* ⟨a, 0, c, 0, e + k⟩ := by
  intro k; induction k with
  | zero => intro a c e; ring_nf; finish
  | succ k ih =>
    intro a c e
    rw [show c + (k + 1) = (c + k) + 1 from by ring]
    step fm
    apply stepStar_trans (ih a c (e + 1))
    ring_nf; finish

theorem drain_b : ∀ B, ∀ A D,
    (⟨A, B, 0, D + 1, 0⟩ : Q) [fm]⊢* ⟨A + B + D + 1, 0, 2 * D + B + 2, 0, 0⟩ := by
  intro B; induction B using Nat.strongRecOn with
  | _ B ih =>
  intro A D
  rcases B with _ | _ | B
  · -- B = 0: R3 chain
    rw [show D + 1 = 0 + (D + 1) from by ring]
    apply stepStar_trans (r3_chain (D + 1) A 0 0)
    ring_nf; finish
  · -- B = 1: R3 + R1 + R3 chain
    -- (A, 1, 0, D+1, 0) -> R3_c0 -> (A+1, 1, 2, D, 0) -> R1 -> (A+1, 0, 1, D+1, 0)
    -- -> R3 chain (D+1 steps from c=1) -> (A+1+D+1, 0, 1+2*(D+1), 0, 0)
    apply stepStar_trans (step_stepStar (r3_step_c0 A 1 D))
    rw [show (1 : ℕ) = 0 + 1 from by ring, show (2 : ℕ) = 1 + 1 from by ring]
    apply stepStar_trans (step_stepStar (r1_step (A + 1) 0 1 D 0))
    rw [show D + 1 = 0 + (D + 1) from by ring]
    apply stepStar_trans (r3_chain (D + 1) (A + 1) 1 0)
    ring_nf; finish
  · -- B + 2: R3 + R1 + R1 then recurse with B, D+1
    -- (A, B+2, 0, D+1, 0) -> R3_c0 -> (A+1, B+2, 2, D, 0) -> R1 -> (A+1, B+1, 1, D+1, 0)
    -- -> R1 -> (A+1, B, 0, D+2, 0). Recurse with B, A+1, D+1.
    apply stepStar_trans (step_stepStar (r3_step_c0 A (B + 2) D))
    rw [show B + 2 = (B + 1) + 1 from by ring, show (2 : ℕ) = 1 + 1 from by ring]
    apply stepStar_trans (step_stepStar (r1_step (A + 1) (B + 1) 1 D 0))
    rw [show B + 1 = B + 1 from rfl, show (1 : ℕ) = 0 + 1 from by ring]
    apply stepStar_trans (step_stepStar (r1_step (A + 1) B 0 (D + 1) 0))
    rw [show D + 1 + 1 = (D + 1) + 1 from by ring]
    apply stepStar_trans (ih B (by omega) (A + 1) (D + 1))
    ring_nf; finish

theorem main_even (a d : ℕ) (ha : a ≥ d) :
    (⟨a + 1, 0, 0, 0, 2 * d⟩ : Q) [fm]⊢⁺ ⟨a + 2 * d + 3, 0, 0, 0, 3 * d + 5⟩ := by
  rcases d with _ | d
  · -- d = 0: (a+1, 0, 0, 0, 0) -> (a+3, 0, 0, 0, 5) in 6 steps + c_to_e
    step fm; step fm; step fm; step fm; step fm; step fm
    rw [show a + 1 + 1 + 1 = a + 3 from by ring,
        show (5 : ℕ) = 0 + 5 from by ring]
    apply stepStar_trans (c_to_e 5 (a + 3) 0 0)
    ring_nf; finish
  · -- d = d' + 1 ≥ 1
    obtain ⟨A, rfl⟩ : ∃ A, a = A + d + 1 := ⟨a - d - 1, by omega⟩
    -- Phase 1: R5+R2×3 drain, d+1 rounds
    rw [show 2 * (d + 1) = 0 + 2 * (d + 1) from by ring,
        show A + d + 1 + 1 = (A + 1) + (d + 1) from by ring]
    apply step_stepStar_stepPlus
    · exact r5_step ((A + 1) + d) 0 (0 + 2 * (d + 1))
    rw [show 0 + 2 * (d + 1) + 1 = ((0 + 2 * d) + 1 + 1) + 1 from by ring,
        show (3 : ℕ) = (1 + 1) + 1 from by ring]
    apply stepStar_trans (step_stepStar (r2_step ((A + 1) + d) 0 (1 + 1) ((0 + 2 * d) + 1 + 1)))
    apply stepStar_trans (step_stepStar (r2_step ((A + 1) + d) 1 1 ((0 + 2 * d) + 1)))
    rw [show (1 : ℕ) = 0 + 1 from by ring]
    apply stepStar_trans (step_stepStar (r2_step ((A + 1) + d) 2 0 (0 + 2 * d)))
    apply stepStar_trans (r5r2x3_drain d (A + 1) 3 0)
    -- State: (A+1, 3d+3, 0, 0, 0)
    -- Phase 2: R5, R2, R3, R1, R1 (5 steps)
    rw [show 3 + 3 * d = 3 * d + 3 from by ring,
        show A + 1 = A + 1 from rfl]
    apply stepStar_trans (step_stepStar (r5_step A (3 * d + 3) 0))
    rw [show (0 + 1 : ℕ) = 1 from by ring,
        show (1 : ℕ) = 0 + 1 from by ring,
        show (3 : ℕ) = (1 + 1) + 1 from by ring]
    apply stepStar_trans (step_stepStar (r2_step A (3 * d + 3) (1 + 1) 0))
    rw [show 3 * d + 3 + 1 = (3 * d + 3) + 1 from by ring,
        show (1 + 1 : ℕ) = 1 + 1 from rfl]
    apply stepStar_trans (step_stepStar (r3_step_c0 A ((3 * d + 3) + 1) 1))
    -- State: (A+1, (3d+4), 2, 1, 0). R1 fires.
    rw [show (3 * d + 3) + 1 = (3 * d + 3) + 1 from rfl,
        show (2 : ℕ) = 1 + 1 from by ring]
    apply stepStar_trans (step_stepStar (r1_step (A + 1) (3 * d + 3) 1 1 0))
    -- State: (A+1, 3d+3, 1, 2, 0). R1 fires.
    rw [show 3 * d + 3 = (3 * d + 2) + 1 from by ring,
        show (1 : ℕ) = 0 + 1 from by ring]
    apply stepStar_trans (step_stepStar (r1_step (A + 1) (3 * d + 2) 0 2 0))
    -- State: (A+1, 3d+2, 0, 3, 0) = (A+1, 3d+2, 0, 2+1, 0)
    -- Phase 3: drain_b with B=3d+2, A=A+1, D=2
    rw [show 2 + 1 = 2 + 1 from rfl]
    apply stepStar_trans (drain_b (3 * d + 2) (A + 1) 2)
    -- Phase 4: c_to_e
    rw [show 2 * 2 + (3 * d + 2) + 2 = 0 + (3 * d + 8) from by ring]
    apply stepStar_trans (c_to_e (3 * d + 8) (A + 1 + (3 * d + 2) + 2 + 1) 0 0)
    ring_nf; finish

theorem main_odd (a d : ℕ) (ha : a ≥ d) :
    (⟨a + 1, 0, 0, 0, 2 * d + 1⟩ : Q) [fm]⊢⁺ ⟨a + 2 * d + 3, 0, 0, 0, 3 * d + 4⟩ := by
  rcases d with _ | d
  · -- d = 0: (a+1, 0, 0, 0, 1) -> (a+3, 0, 0, 0, 4) in 8 steps + c_to_e
    step fm; step fm; step fm; step fm; step fm; step fm; step fm; step fm
    rw [show a + 1 + 1 + 1 = a + 3 from by ring,
        show (4 : ℕ) = 0 + 4 from by ring]
    apply stepStar_trans (c_to_e 4 (a + 3) 0 0)
    ring_nf; finish
  · -- d = d' + 1 ≥ 1
    obtain ⟨A, rfl⟩ : ∃ A, a = A + d + 1 := ⟨a - d - 1, by omega⟩
    -- Phase 1: R5+R2×3 drain, d+1 rounds
    rw [show 2 * (d + 1) + 1 = 1 + 2 * (d + 1) from by ring,
        show A + d + 1 + 1 = (A + 1) + (d + 1) from by ring]
    apply step_stepStar_stepPlus
    · exact r5_step ((A + 1) + d) 0 (1 + 2 * (d + 1))
    rw [show 1 + 2 * (d + 1) + 1 = ((1 + 2 * d) + 1 + 1) + 1 from by ring,
        show (3 : ℕ) = (1 + 1) + 1 from by ring]
    apply stepStar_trans (step_stepStar (r2_step ((A + 1) + d) 0 (1 + 1) ((1 + 2 * d) + 1 + 1)))
    apply stepStar_trans (step_stepStar (r2_step ((A + 1) + d) 1 1 ((1 + 2 * d) + 1)))
    rw [show (1 : ℕ) = 0 + 1 from by ring]
    apply stepStar_trans (step_stepStar (r2_step ((A + 1) + d) 2 0 (1 + 2 * d)))
    apply stepStar_trans (r5r2x3_drain d (A + 1) 3 1)
    -- State: (A+1, 3d+3, 0, 0, 1)
    -- Phase 2: R5, R2×2, R3, R1×2 (6 steps)
    rw [show 3 + 3 * d = 3 * d + 3 from by ring,
        show A + 1 = A + 1 from rfl]
    apply stepStar_trans (step_stepStar (r5_step A (3 * d + 3) 1))
    rw [show (1 + 1 : ℕ) = 0 + 1 + 1 from by ring,
        show (3 : ℕ) = (0 + 1 + 1) + 1 from by ring]
    apply stepStar_trans (step_stepStar (r2_step A (3 * d + 3) (0 + 1 + 1) (0 + 1)))
    apply stepStar_trans (step_stepStar (r2_step A (3 * d + 3 + 1) (0 + 1) 0))
    -- State: (A, 3d+5, 0, 0+1, 0). R3 fires.
    rw [show 0 + 1 = 0 + 1 from rfl]
    apply stepStar_trans (step_stepStar (r3_step_c0 A (3 * d + 3 + 1 + 1) 0))
    -- State: (A+1, 3d+5, 2, 0, 0). R1 fires.
    rw [show 3 * d + 3 + 1 + 1 = (3 * d + 4) + 1 from by ring,
        show (2 : ℕ) = 1 + 1 from by ring]
    apply stepStar_trans (step_stepStar (r1_step (A + 1) (3 * d + 4) 1 0 0))
    -- State: (A+1, 3d+4, 1, 1, 0). R1 fires.
    rw [show 3 * d + 4 = (3 * d + 3) + 1 from by ring,
        show (1 : ℕ) = 0 + 1 from by ring]
    apply stepStar_trans (step_stepStar (r1_step (A + 1) (3 * d + 3) 0 1 0))
    -- State: (A+1, 3d+3, 0, 2, 0) = (A+1, 3d+3, 0, 1+1, 0)
    -- Phase 3: drain_b with B=3d+3, A=A+1, D=1
    rw [show 1 + 1 = 1 + 1 from rfl]
    apply stepStar_trans (drain_b (3 * d + 3) (A + 1) 1)
    -- Phase 4: c_to_e
    rw [show 2 * 1 + (3 * d + 3) + 2 = 0 + (3 * d + 7) from by ring]
    apply stepStar_trans (c_to_e (3 * d + 7) (A + 1 + (3 * d + 3) + 1 + 1) 0 0)
    ring_nf; finish

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨3, 0, 0, 0, 5⟩) (by execute fm 11)
  apply progress_nonhalt (fm := fm)
    (P := fun q ↦ ∃ a e, q = ⟨a + 1, 0, 0, 0, e⟩ ∧ 2 * (a + 1) > e)
  · intro q ⟨a, e, hq, hinv⟩; subst hq
    rcases Nat.even_or_odd e with ⟨d, hd⟩ | ⟨d, hd⟩
    · rw [show d + d = 2 * d from by ring] at hd; subst hd
      exact ⟨⟨a + 2 * d + 3, 0, 0, 0, 3 * d + 5⟩,
        ⟨a + 2 * d + 2, 3 * d + 5, rfl, by omega⟩,
        main_even a d (by omega)⟩
    · subst hd
      exact ⟨⟨a + 2 * d + 3, 0, 0, 0, 3 * d + 4⟩,
        ⟨a + 2 * d + 2, 3 * d + 4, rfl, by omega⟩,
        main_odd a d (by omega)⟩
  · exact ⟨2, 5, rfl, by omega⟩

end Sz22_2003_unofficial_1465
