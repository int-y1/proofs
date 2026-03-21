import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz21_140_unofficial #138: [9/35, 25/33, 14/3, 11/7, 21/2]

Vector representation:
```
 0  2 -1 -1  0
 0 -1  2  0 -1
 1 -1  0  1  0
 0  0  0 -1  1
-1  1  0  1  0
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz21_140_unofficial_138

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a, b, c+1, d+1, e⟩ => some ⟨a, b+2, c, d, e⟩
  | ⟨a, b+1, c, d, e+1⟩ => some ⟨a, b, c+2, d, e⟩
  | ⟨a, b+1, c, d, e⟩ => some ⟨a+1, b, c, d+1, e⟩
  | ⟨a, b, c, d+1, e⟩ => some ⟨a, b, c, d, e+1⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b+1, c, d+1, e⟩
  | _ => none

-- R4 repeated: d → e
theorem d_to_e : ∀ k a d e, ⟨a, 0, 0, d+k, e⟩ [fm]⊢* ⟨a, 0, 0, d, e+k⟩ := by
  intro k; induction k with
  | zero => intro a d e; exists 0
  | succ k ih =>
    intro a d e
    rw [show d + (k + 1) = (d + k) + 1 from by ring]
    step fm
    have h := ih a d (e + 1)
    rw [show e + 1 + k = e + (k + 1) from by ring] at h
    exact h

theorem d_to_e_full (d a : ℕ) : ⟨a, 0, 0, d, 0⟩ [fm]⊢* ⟨a, 0, 0, 0, d⟩ := by
  have h := d_to_e d a 0 0; simp at h; exact h

-- R3 repeated: b → a, d
theorem b_to_ad : ∀ k a b d, ⟨a, b+k, 0, d, 0⟩ [fm]⊢* ⟨a+k, b, 0, d+k, 0⟩ := by
  intro k; induction k with
  | zero => intro a b d; exists 0
  | succ k ih =>
    intro a b d
    rw [show b + (k + 1) = (b + k) + 1 from by ring]
    step fm
    have h := ih (a+1) b (d+1)
    rw [show d + 1 + k = d + (k + 1) from by ring,
        show a + 1 + k = a + (k + 1) from by ring] at h
    exact h

theorem b_to_d (k a : ℕ) : ⟨a, k, 0, 0, 0⟩ [fm]⊢* ⟨a+k, 0, 0, k, 0⟩ := by
  have h := b_to_ad k a 0 0; simp at h; exact h

-- R3/R1 unwind: each round R3 then R1
theorem unwind : ∀ k A B, ⟨A, B+1, k, 0, 0⟩ [fm]⊢* ⟨A+k, B+1+k, 0, 0, 0⟩ := by
  intro k; induction k with
  | zero => intro A B; exists 0
  | succ k ih =>
    intro A B
    step fm; step fm
    have h := ih (A+1) (B+1)
    rw [show A + (k + 1) = A + 1 + k from by ring,
        show B + 1 + (k + 1) = B + 1 + 1 + k from by ring]
    exact h

theorem outer_c0 (a e : ℕ) : ⟨a+1, 0, 0, 0, e+3⟩ [fm]⊢* ⟨a, 0, 5, 0, e⟩ := by
  step fm; step fm; step fm; step fm; step fm; finish

theorem outer_c1 (a c e : ℕ) : ⟨a+1, 0, c+1, 0, e+3⟩ [fm]⊢* ⟨a, 0, c+6, 0, e⟩ := by
  step fm; step fm; step fm; step fm; step fm; ring_nf; finish

theorem outer_round (a c e : ℕ) : ⟨a+1, 0, c, 0, e+3⟩ [fm]⊢* ⟨a, 0, c+5, 0, e⟩ := by
  rcases c with _ | c
  · exact outer_c0 a e
  · have h := outer_c1 a c e; rw [show c + 6 = c + 1 + 5 from by ring] at h; exact h

-- k outer rounds
theorem outer_rounds : ∀ k a c r, ⟨a+k, 0, c, 0, 3*k+r⟩ [fm]⊢* ⟨a, 0, c+5*k, 0, r⟩ := by
  intro k; induction k with
  | zero => intro a c r; simp; exists 0
  | succ k ih =>
    intro a c r
    rw [show a + (k + 1) = (a + k) + 1 from by ring, show 3 * (k + 1) + r = (3 * k + r) + 3 from by ring]
    apply stepStar_trans (outer_round _ _ _)
    have h := ih a (c + 5) r
    rw [show c + 5 + 5 * k = c + 5 * (k + 1) from by ring] at h; exact h

theorem tail_mod0 (a c : ℕ) : ⟨a+1, 0, c+1, 0, 0⟩ [fm]⊢* ⟨a, 3, c, 0, 0⟩ := by
  step fm; step fm; finish

theorem tail_mod1_c0 (a : ℕ) : ⟨a+1, 0, 0, 0, 1⟩ [fm]⊢* ⟨a, 2, 1, 0, 0⟩ := by
  step fm; step fm; step fm; finish

theorem tail_mod1_c1 (a c : ℕ) : ⟨a+1, 0, c+1, 0, 1⟩ [fm]⊢* ⟨a, 2, c+2, 0, 0⟩ := by
  step fm; step fm; step fm; ring_nf; finish

theorem tail_mod1 (a c : ℕ) : ⟨a+1, 0, c, 0, 1⟩ [fm]⊢* ⟨a, 2, c+1, 0, 0⟩ := by
  rcases c with _ | c
  · exact tail_mod1_c0 a
  · have h := tail_mod1_c1 a c; rw [show c + 2 = c + 1 + 1 from by ring] at h; exact h

theorem tail_mod2_c0 (a : ℕ) : ⟨a+1, 0, 0, 0, 2⟩ [fm]⊢* ⟨a, 1, 3, 0, 0⟩ := by
  step fm; step fm; step fm; step fm; finish

theorem tail_mod2_c1 (a c : ℕ) : ⟨a+1, 0, c+1, 0, 2⟩ [fm]⊢* ⟨a, 1, c+4, 0, 0⟩ := by
  step fm; step fm; step fm; step fm; ring_nf; finish

theorem tail_mod2 (a c : ℕ) : ⟨a+1, 0, c, 0, 2⟩ [fm]⊢* ⟨a, 1, c+3, 0, 0⟩ := by
  rcases c with _ | c
  · exact tail_mod2_c0 a
  · have h := tail_mod2_c1 a c; rw [show c + 4 = c + 1 + 3 from by ring] at h; exact h

-- Transition for d = 3(K+1)
theorem trans_mod0 (K a : ℕ) : ⟨a+K+2, 0, 0, 3*K+3, 0⟩ [fm]⊢⁺ ⟨a+10*K+11, 0, 0, 5*K+7, 0⟩ := by
  rw [show 3 * K + 3 = (3 * K + 2) + 1 from by ring]
  apply step_stepStar_stepPlus (c₂ := ⟨a + K + 2, 0, 0, 3 * K + 2, 1⟩)
  · simp [fm]
  have hde := d_to_e (3*K+2) (a+K+2) 0 1; simp at hde
  apply stepStar_trans hde
  rw [show 1 + (3 * K + 2) = 3 * K + 3 from by ring]
  rw [show a + K + 2 = (a + 1) + (K + 1) from by ring,
      show 3 * K + 3 = 3 * (K + 1) + 0 from by ring]
  apply stepStar_trans (outer_rounds (K+1) (a+1) 0 0)
  rw [show 0 + 5 * (K + 1) = (5 * K + 4) + 1 from by ring]
  apply stepStar_trans (tail_mod0 a (5*K+4))
  rw [show (3 : ℕ) = 2 + 1 from by ring]
  apply stepStar_trans (unwind (5*K+4) a 2)
  rw [show 2 + 1 + (5 * K + 4) = 5 * K + 7 from by ring,
      show a + (5 * K + 4) = a + 5 * K + 4 from by ring]
  apply stepStar_trans (b_to_d (5*K+7) (a+5*K+4))
  ring_nf; finish

-- Transition for d = 3K+1
theorem trans_mod1 (K a : ℕ) : ⟨a+K+1, 0, 0, 3*K+1, 0⟩ [fm]⊢⁺ ⟨a+10*K+4, 0, 0, 5*K+3, 0⟩ := by
  rw [show 3 * K + 1 = (3 * K) + 1 from by ring]
  apply step_stepStar_stepPlus (c₂ := ⟨a + K + 1, 0, 0, 3 * K, 1⟩)
  · simp [fm]
  have hde := d_to_e (3*K) (a+K+1) 0 1; simp at hde
  apply stepStar_trans hde
  rw [show 1 + (3 * K) = 3 * K + 1 from by ring]
  rw [show a + K + 1 = (a + 1) + K from by ring,
      show 3 * K + 1 = 3 * K + 1 from rfl]
  apply stepStar_trans (outer_rounds K (a+1) 0 1)
  rw [show 0 + 5 * K = 5 * K from by ring]
  apply stepStar_trans (tail_mod1 a (5*K))
  rw [show (2 : ℕ) = 1 + 1 from by ring]
  apply stepStar_trans (unwind (5*K+1) a 1)
  rw [show 1 + 1 + (5 * K + 1) = 5 * K + 3 from by ring,
      show a + (5 * K + 1) = a + 5 * K + 1 from by ring]
  apply stepStar_trans (b_to_d (5*K+3) (a+5*K+1))
  ring_nf; finish

-- Transition for d = 3K+2
theorem trans_mod2 (K a : ℕ) : ⟨a+K+1, 0, 0, 3*K+2, 0⟩ [fm]⊢⁺ ⟨a+10*K+7, 0, 0, 5*K+4, 0⟩ := by
  rw [show 3 * K + 2 = (3 * K + 1) + 1 from by ring]
  apply step_stepStar_stepPlus (c₂ := ⟨a + K + 1, 0, 0, 3 * K + 1, 1⟩)
  · simp [fm]
  have hde := d_to_e (3*K+1) (a+K+1) 0 1; simp at hde
  apply stepStar_trans hde
  rw [show 1 + (3 * K + 1) = 3 * K + 2 from by ring]
  rw [show a + K + 1 = (a + 1) + K from by ring,
      show 3 * K + 2 = 3 * K + 2 from rfl]
  apply stepStar_trans (outer_rounds K (a+1) 0 2)
  rw [show 0 + 5 * K = 5 * K from by ring]
  apply stepStar_trans (tail_mod2 a (5*K))
  rw [show (1 : ℕ) = 0 + 1 from by ring]
  apply stepStar_trans (unwind (5*K+3) a 0)
  rw [show 0 + 1 + (5 * K + 3) = 5 * K + 4 from by ring,
      show a + (5 * K + 3) = a + 5 * K + 3 from by ring]
  apply stepStar_trans (b_to_d (5*K+4) (a+5*K+3))
  ring_nf; finish

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨7, 0, 0, 4, 0⟩) (by execute fm 18)
  apply progress_nonhalt (fm := fm)
    (P := fun q ↦ ∃ a d, q = ⟨a, 0, 0, d, 0⟩ ∧ d ≥ 1 ∧ a ≥ d + 3)
  · intro c ⟨a, d, hq, hd, ha⟩; subst hq
    obtain ⟨K, r, hdr, hr⟩ : ∃ K r, d = 3 * K + r ∧ r < 3 :=
      ⟨d / 3, d % 3, by omega, Nat.mod_lt _ (by omega)⟩
    rcases r with _ | _ | _ | r
    · -- r = 0: d = 3K, K ≥ 1
      simp at hdr
      obtain ⟨K', rfl⟩ : ∃ K', K = K' + 1 := ⟨K - 1, by omega⟩
      subst hdr
      refine ⟨⟨a + 9 * K' + 9, 0, 0, 5 * K' + 7, 0⟩,
              ⟨a + 9 * K' + 9, 5 * K' + 7, rfl, by omega, by omega⟩, ?_⟩
      have h := trans_mod0 K' (a - K' - 2)
      rw [show a - K' - 2 + K' + 2 = a from by omega,
          show a - K' - 2 + 10 * K' + 11 = a + 9 * K' + 9 from by omega] at h
      exact h
    · -- r = 1: d = 3K + 1
      subst hdr
      refine ⟨⟨a + 9 * K + 3, 0, 0, 5 * K + 3, 0⟩,
              ⟨a + 9 * K + 3, 5 * K + 3, rfl, by omega, by omega⟩, ?_⟩
      have h := trans_mod1 K (a - K - 1)
      rw [show a - K - 1 + K + 1 = a from by omega,
          show a - K - 1 + 10 * K + 4 = a + 9 * K + 3 from by omega] at h
      exact h
    · -- r = 2: d = 3K + 2
      subst hdr
      refine ⟨⟨a + 9 * K + 6, 0, 0, 5 * K + 4, 0⟩,
              ⟨a + 9 * K + 6, 5 * K + 4, rfl, by omega, by omega⟩, ?_⟩
      have h := trans_mod2 K (a - K - 1)
      rw [show a - K - 1 + K + 1 = a from by omega,
          show a - K - 1 + 10 * K + 7 = a + 9 * K + 6 from by omega] at h
      exact h
    · omega
  · exact ⟨7, 4, rfl, by omega, by omega⟩
