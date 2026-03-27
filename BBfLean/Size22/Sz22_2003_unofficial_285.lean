import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #285: [14/15, 9/22, 125/2, 11/7, 3/5]

Vector representation:
```
 1 -1 -1  1  0
-1  2  0  0 -1
-1  0  3  0  0
 0  0  0 -1  1
 0  1 -1  0  0
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_285

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a, b+1, c+1, d, e⟩ => some ⟨a+1, b, c, d+1, e⟩
  | ⟨a+1, b, c, d, e+1⟩ => some ⟨a, b+2, c, d, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b, c+3, d, e⟩
  | ⟨a, b, c, d+1, e⟩ => some ⟨a, b, c, d, e+1⟩
  | ⟨a, b, c+1, d, e⟩ => some ⟨a, b+1, c, d, e⟩
  | _ => none

private lemma step_r4 (C d E : ℕ) : ⟨0, 0, C, d+1, E⟩ [fm]⊢ ⟨0, 0, C, d, E+1⟩ := by
  cases C <;> cases E <;> rfl
private lemma step_r3 (a C D : ℕ) : ⟨a+1, 0, C, D, 0⟩ [fm]⊢ ⟨a, 0, C+3, D, 0⟩ := by
  cases C <;> rfl
private lemma step_r2_b0 (a C D e : ℕ) : ⟨a+1, 0, C, D, e+1⟩ [fm]⊢ ⟨a, 2, C, D, e⟩ := by
  cases C <;> rfl
private lemma step_r2_c0 (a B D e : ℕ) : ⟨a+1, B, 0, D, e+1⟩ [fm]⊢ ⟨a, B+2, 0, D, e⟩ := by
  cases B <;> rfl
private lemma step_r1 (a b C d E : ℕ) : ⟨a, b+1, C+1, d, E⟩ [fm]⊢ ⟨a+1, b, C, d+1, E⟩ := rfl
private lemma step_r3_gen (a B D : ℕ) : ⟨a+1, B, 0, D, 0⟩ [fm]⊢ ⟨a, B, 3, D, 0⟩ := by
  cases B <;> rfl
private lemma step_r5_gen (C E : ℕ) : ⟨0, 0, C+1, 0, E⟩ [fm]⊢ ⟨0, 1, C, 0, E⟩ := by
  cases C <;> cases E <;> rfl

theorem r3_chain (k C D : ℕ) :
    ⟨k, 0, C, D, 0⟩ [fm]⊢* ⟨(0 : ℕ), 0, C + 3 * k, D, 0⟩ := by
  induction k generalizing C with
  | zero => simp; finish
  | succ k ih =>
    refine stepStar_trans (step_stepStar (step_r3 k C D)) ?_
    rw [show C + 3 * (k + 1) = (C + 3) + 3 * k from by ring]
    exact ih (C + 3)

theorem r4_chain (k C E : ℕ) :
    ⟨0, 0, C, k, E⟩ [fm]⊢* ⟨(0 : ℕ), 0, C, 0, E + k⟩ := by
  induction k generalizing E with
  | zero => simp; finish
  | succ k ih =>
    refine stepStar_trans (step_stepStar (step_r4 C k E)) ?_
    rw [show E + (k + 1) = (E + 1) + k from by ring]
    exact ih (E + 1)

theorem r2_drain (k A B D : ℕ) :
    ⟨A + k, B, 0, D, k⟩ [fm]⊢* ⟨A, B + 2 * k, (0 : ℕ), D, 0⟩ := by
  induction k generalizing A B with
  | zero => simp; finish
  | succ k ih =>
    rw [show A + (k + 1) = (A + k) + 1 from by ring]
    refine stepStar_trans (step_stepStar (step_r2_c0 (A + k) B D k)) ?_
    rw [show B + 2 * (k + 1) = (B + 2) + 2 * k from by ring]
    exact ih A (B + 2)

private lemma loop_round (A C D E : ℕ) :
    ⟨A+1, 0, C+2, D, E+1⟩ [fm]⊢* ⟨A+2, (0 : ℕ), C, D+2, E⟩ := by
  refine stepStar_trans (step_stepStar (step_r2_b0 A (C+2) D E)) ?_
  refine stepStar_trans (step_stepStar (step_r1 A 1 (C+1) D E)) ?_
  exact step_stepStar (step_r1 (A+1) 0 C (D+1) E)

theorem loop (n C D E : ℕ) :
    ⟨1, 0, C + 2 * n, D, E + n⟩ [fm]⊢* ⟨1 + n, (0 : ℕ), C, D + 2 * n, E⟩ := by
  induction n generalizing C D E with
  | zero => simp; finish
  | succ n ih =>
    rw [show C + 2 * (n + 1) = (C + 2) + 2 * n from by ring,
        show E + (n + 1) = (E + 1) + n from by ring]
    refine stepStar_trans (ih (C + 2) D (E + 1)) ?_
    convert loop_round n C (D + 2 * n) E using 2 <;> ring

private lemma r3r1_round (A B D : ℕ) :
    ⟨A+1, B+3, 0, D, 0⟩ [fm]⊢* ⟨A+3, B, (0 : ℕ), D+3, 0⟩ := by
  refine stepStar_trans (step_stepStar (step_r3_gen A (B+3) D)) ?_
  refine stepStar_trans (step_stepStar (step_r1 A (B+2) 2 D 0)) ?_
  refine stepStar_trans (step_stepStar (step_r1 (A+1) (B+1) 1 (D+1) 0)) ?_
  exact step_stepStar (step_r1 (A+2) B 0 (D+2) 0)

theorem round_chain_r0 (N A D : ℕ) :
    ⟨A+1, 3 * N, 0, D, 0⟩ [fm]⊢* ⟨A + 1 + 2 * N, (0 : ℕ), 0, D + 3 * N, 0⟩ := by
  induction N generalizing A D with
  | zero => simp; finish
  | succ N ih =>
    rw [show 3 * (N + 1) = 3 * N + 3 from by ring]
    refine stepStar_trans (r3r1_round A (3 * N) D) ?_
    convert ih (A + 2) (D + 3) using 2 <;> ring

theorem round_chain_r2 (N A D : ℕ) :
    ⟨A+1, 3 * N + 2, 0, D, 0⟩ [fm]⊢* ⟨A + 1 + 2 * N, (2 : ℕ), 0, D + 3 * N, 0⟩ := by
  induction N generalizing A D with
  | zero => simp; finish
  | succ N ih =>
    rw [show 3 * (N + 1) + 2 = (3 * N + 2) + 3 from by ring]
    refine stepStar_trans (r3r1_round A (3 * N + 2) D) ?_
    convert ih (A + 2) (D + 3) using 2 <;> ring

private lemma tail_steps (A D : ℕ) :
    ⟨A+1, 2, 0, D, 0⟩ [fm]⊢* ⟨A+2, (0 : ℕ), 1, D+2, 0⟩ := by
  refine stepStar_trans (step_stepStar (step_r3_gen A 2 D)) ?_
  refine stepStar_trans (step_stepStar (step_r1 A 1 2 D 0)) ?_
  exact step_stepStar (step_r1 (A+1) 0 1 (D+1) 0)

theorem middle_even (m : ℕ) :
    ⟨0, 0, 2 * m + 4, 0, 2 * m + 1⟩ [fm]⊢* ⟨(2 : ℕ), 2 * m, 0, 2 * m + 3, 0⟩ := by
  apply stepStar_trans
  show ⟨0, 0, 2 * m + 4, 0, 2 * m + 1⟩ [fm]⊢* ⟨0, 1, 2 * m + 3, 0, 2 * m + 1⟩
  · exact step_stepStar (step_r5_gen (2 * m + 3) (2 * m + 1))
  apply stepStar_trans
  show ⟨0, 1, 2 * m + 3, 0, 2 * m + 1⟩ [fm]⊢* ⟨1, 0, 2 * m + 2, 1, 2 * m + 1⟩
  · exact step_stepStar (step_r1 0 0 (2 * m + 2) 0 (2 * m + 1))
  apply stepStar_trans
  show ⟨1, 0, 2 * m + 2, 1, 2 * m + 1⟩ [fm]⊢* ⟨1 + m, (0 : ℕ), 2, 1 + 2 * m, m + 1⟩
  · convert loop m 2 1 (m + 1) using 2 <;> ring
  apply stepStar_trans
  show ⟨1 + m, 0, 2, 1 + 2 * m, m + 1⟩ [fm]⊢* ⟨m + 2, (0 : ℕ), 0, 1 + 2 * m + 2, m⟩
  · convert loop_round m 0 (1 + 2 * m) m using 2 <;> ring
  show ⟨m + 2, 0, 0, 1 + 2 * m + 2, m⟩ [fm]⊢* ⟨(2 : ℕ), 2 * m, 0, 2 * m + 3, 0⟩
  convert r2_drain m 2 0 (1 + 2 * m + 2) using 2 <;> ring

theorem middle_odd (m : ℕ) :
    ⟨0, 0, 2 * m + 5, 0, 2 * m + 2⟩ [fm]⊢* ⟨(2 : ℕ), 2 * m + 1, 0, 2 * m + 4, 0⟩ := by
  apply stepStar_trans
  show ⟨0, 0, 2 * m + 5, 0, 2 * m + 2⟩ [fm]⊢* ⟨0, 1, 2 * m + 4, 0, 2 * m + 2⟩
  · exact step_stepStar (step_r5_gen (2 * m + 4) (2 * m + 2))
  apply stepStar_trans
  show ⟨0, 1, 2 * m + 4, 0, 2 * m + 2⟩ [fm]⊢* ⟨1, 0, 2 * m + 3, 1, 2 * m + 2⟩
  · exact step_stepStar (step_r1 0 0 (2 * m + 3) 0 (2 * m + 2))
  apply stepStar_trans
  show ⟨1, 0, 2 * m + 3, 1, 2 * m + 2⟩ [fm]⊢* ⟨m + 2, (0 : ℕ), 1, 1 + 2 * (m + 1), m + 1⟩
  · convert loop (m + 1) 1 1 (m + 1) using 2 <;> ring
  apply stepStar_trans
  show ⟨m + 2, 0, 1, 1 + 2 * (m + 1), m + 1⟩ [fm]⊢* ⟨m + 1, 2, 1, 1 + 2 * (m + 1), m⟩
  · exact step_stepStar (step_r2_b0 (m + 1) 1 (1 + 2 * (m + 1)) m)
  apply stepStar_trans
  show ⟨m + 1, 2, 1, 1 + 2 * (m + 1), m⟩ [fm]⊢* ⟨m + 1 + 1, 1, 0, 1 + 2 * (m + 1) + 1, m⟩
  · exact step_stepStar (step_r1 (m + 1) 1 0 (1 + 2 * (m + 1)) m)
  show ⟨m + 1 + 1, 1, 0, 1 + 2 * (m + 1) + 1, m⟩ [fm]⊢* ⟨(2 : ℕ), 2 * m + 1, 0, 2 * m + 4, 0⟩
  convert r2_drain m 2 1 (2 + 2 * (m + 1)) using 2 <;> ring

theorem bootstrap : c₀ [fm]⊢* ⟨(2 : ℕ), 0, 0, 3, 0⟩ := by
  unfold c₀; execute fm 10

theorem main_trans (N : ℕ) :
    ⟨N + 2, 0, 0, 3 * (N + 1), 0⟩ [fm]⊢⁺ ⟨4 * N + 6, (0 : ℕ), 0, 12 * N + 15, 0⟩ := by
  -- Phase 1: R3 step + r3_chain
  apply step_stepStar_stepPlus (step_r3 (N + 1) 0 (3 * (N + 1)))
  apply stepStar_trans (r3_chain (N + 1) 3 (3 * (N + 1)))
  -- Phase 2: r4_chain
  apply stepStar_trans
  show ⟨0, 0, 3 + 3 * (N + 1), 3 * (N + 1), 0⟩ [fm]⊢*
       ⟨(0 : ℕ), 0, 3 + 3 * (N + 1), 0, 3 * (N + 1)⟩
  · convert r4_chain (3 * (N + 1)) (3 + 3 * (N + 1)) 0 using 2 <;> ring
  -- Phase 3+: middle section and second half. Split on parity of N.
  -- Helper: chain stepStar proofs with arithmetic conversion
  -- Helper to bridge between non-definitionally-equal tuples in stepStar chains
  have bridge : ∀ {a b c d e a' b' c' d' e' : ℕ} {X : Q},
      (⟨a, b, c, d, e⟩ [fm]⊢* X) → (a = a') → (b = b') → (c = c') → (d = d') → (e = e') →
      (⟨a', b', c', d', e'⟩ [fm]⊢* X) := by
    intro _ _ _ _ _ _ _ _ _ _ _ h h1 h2 h3 h4 h5
    subst h1; subst h2; subst h3; subst h4; subst h5; exact h
  rcases Nat.even_or_odd N with ⟨k, hk⟩ | ⟨k, hk⟩ <;> subst hk
  · -- N = 2k (even case).
    suffices h : ⟨0, 0, 2 * (3 * k + 1) + 4, 0, 2 * (3 * k + 1) + 1⟩ [fm]⊢*
        ⟨1 + 1 + 2 * (4 * k + 2), (0 : ℕ), 0, 12 * k + 9 + 3 * (4 * k + 2), 0⟩ by
      convert h using 2 <;> ring
    exact stepStar_trans (middle_even (3 * k + 1))
      (stepStar_trans (bridge (round_chain_r2 (2 * k) 1 (2 * (3 * k + 1) + 3))
          (by ring) (by ring) (by ring) (by ring) (by ring))
      (stepStar_trans (bridge (tail_steps (4 * k + 1) (12 * k + 5))
          (by ring) (by ring) (by ring) (by ring) (by ring))
      (stepStar_trans (bridge (r3_chain (4 * k + 3) 1 (12 * k + 7))
          (by ring) (by ring) (by ring) (by ring) (by ring))
      (stepStar_trans (bridge (r4_chain (12 * k + 7) (12 * k + 10) 0)
          (by ring) (by ring) (by ring) (by ring) (by ring))
      (stepStar_trans (bridge (middle_even (6 * k + 3))
          (by ring) (by ring) (by ring) (by ring) (by ring))
      (bridge (round_chain_r0 (4 * k + 2) 1 (12 * k + 9))
          (by ring) (by ring) (by ring) (by ring) (by ring)))))))
  · -- N = 2k+1 (odd case).
    suffices h : ⟨0, 0, 2 * (3 * k + 2) + 5, 0, 2 * (3 * k + 2) + 2⟩ [fm]⊢*
        ⟨1 + 1 + 2 * (4 * k + 4), (0 : ℕ), 0, 12 * k + 15 + 3 * (4 * k + 4), 0⟩ by
      convert h using 2 <;> ring
    exact stepStar_trans (middle_odd (3 * k + 2))
      (stepStar_trans (bridge (round_chain_r2 (2 * k + 1) 1 (2 * (3 * k + 2) + 4))
          (by ring) (by ring) (by ring) (by ring) (by ring))
      (stepStar_trans (bridge (tail_steps (4 * k + 3) (12 * k + 11))
          (by ring) (by ring) (by ring) (by ring) (by ring))
      (stepStar_trans (bridge (r3_chain (4 * k + 5) 1 (12 * k + 13))
          (by ring) (by ring) (by ring) (by ring) (by ring))
      (stepStar_trans (bridge (r4_chain (12 * k + 13) (12 * k + 16) 0)
          (by ring) (by ring) (by ring) (by ring) (by ring))
      (stepStar_trans (bridge (middle_even (6 * k + 6))
          (by ring) (by ring) (by ring) (by ring) (by ring))
      (bridge (round_chain_r0 (4 * k + 4) 1 (12 * k + 15))
          (by ring) (by ring) (by ring) (by ring) (by ring)))))))

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts bootstrap
  apply progress_nonhalt_simple (fm := fm) (fun n ↦ ⟨4 * n + 2, 0, 0, 12 * n + 3, 0⟩) 0
  intro n
  refine ⟨4 * n + 1, ?_⟩
  convert main_trans (4 * n) using 2; all_goals ring

end Sz22_2003_unofficial_285
