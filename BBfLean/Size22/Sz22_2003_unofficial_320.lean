import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #320: [16/15, 3/14, 55/2, 7/5, 10/11]

Vector representation:
```
 4 -1 -1  0  0
-1  1  0 -1  0
-1  0  1  0  1
 0  0 -1  1  0
 1  0  1  0 -1
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_320

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a, b+1, c+1, d, e⟩ => some ⟨a+4, b, c, d, e⟩
  | ⟨a+1, b, c, d+1, e⟩ => some ⟨a, b+1, c, d, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b, c+1, d, e+1⟩
  | ⟨a, b, c+1, d, e⟩ => some ⟨a, b, c, d+1, e⟩
  | ⟨a, b, c, d, e+1⟩ => some ⟨a+1, b, c+1, d, e⟩
  | _ => none

theorem r3_loop : ∀ a c e, ⟨a, 0, c, 0, e⟩ [fm]⊢* ⟨0, 0, c + a, 0, e + a⟩ := by
  intro a; induction a with
  | zero => intro c e; simp; finish
  | succ a ih =>
    intro c e; step fm
    apply stepStar_trans (ih (c + 1) (e + 1))
    ring_nf; finish

theorem r4_loop : ∀ c d e, ⟨0, 0, c, d, e⟩ [fm]⊢* ⟨0, 0, 0, d + c, e⟩ := by
  intro c; induction c with
  | zero => intro d e; simp; finish
  | succ c ih =>
    intro d e; step fm
    apply stepStar_trans (ih (d + 1) e)
    ring_nf; finish

theorem pump : ⟨0, b, 0, d + 1, e + 1⟩ [fm]⊢* ⟨4, b, 0, d, e⟩ := by
  cases b with
  | zero => step fm; step fm; step fm; finish
  | succ b => step fm; step fm; step fm; finish

theorem r2_partial : ∀ k a b d e,
    ⟨a + k, b, 0, d + k, e⟩ [fm]⊢* ⟨a, b + k, 0, d, e⟩ := by
  intro k; induction k with
  | zero => intro a b d e; simp; finish
  | succ k ih =>
    intro a b d e
    rw [show a + (k + 1) = (a + k) + 1 from by ring,
        show d + (k + 1) = (d + k) + 1 from by ring]
    step fm
    apply stepStar_trans (ih a (b + 1) d e)
    ring_nf; finish

theorem drain_b : ∀ b a e, ⟨a + 1, b, 0, 0, e⟩ [fm]⊢* ⟨a + 1 + 3 * b, 0, 0, 0, e + b⟩ := by
  intro b; induction b with
  | zero => intro a e; simp; finish
  | succ b ih =>
    intro a e; step fm; step fm
    apply stepStar_trans (ih (a + 3) (e + 1))
    ring_nf; finish

theorem big_round : ⟨0, b, 0, d + 5, e + 1⟩ [fm]⊢* ⟨0, b + 4, 0, d, e⟩ := by
  rw [show d + 5 = (d + 4) + 1 from by ring]
  apply stepStar_trans (pump (b := b) (d := d + 4) (e := e))
  rw [show (4 : ℕ) = 0 + 4 from by ring]
  apply stepStar_trans (r2_partial 4 0 b d e)
  ring_nf; finish

theorem big_round_loop : ∀ k b d e,
    ⟨0, b, 0, d + 5 * k, e + k⟩ [fm]⊢* ⟨0, b + 4 * k, 0, d, e⟩ := by
  intro k; induction k with
  | zero => intro b d e; simp; finish
  | succ k ih =>
    intro b d e
    rw [show d + 5 * (k + 1) = (d + 5) + 5 * k from by ring,
        show e + (k + 1) = (e + 1) + k from by ring]
    apply stepStar_trans (ih b (d + 5) (e + 1))
    apply stepStar_trans (big_round (b := b + 4 * k) (d := d) (e := e))
    ring_nf; finish

theorem tail_r1 : ⟨0, b, 0, 1, e + 1⟩ [fm]⊢⁺ ⟨3 * b + 4, 0, 0, 0, e + b⟩ := by
  rw [show (1 : ℕ) = 0 + 1 from by ring]
  cases b with
  | zero => step fm; step fm; step fm; finish
  | succ b =>
    step fm; step fm; step fm; step fm; step fm
    rw [show (7 : ℕ) = 6 + 1 from by ring]
    apply stepStar_trans (drain_b b 6 (e + 1))
    ring_nf; finish

theorem tail_r2 : ⟨0, b, 0, 2, e + 1⟩ [fm]⊢⁺ ⟨3 * b + 6, 0, 0, 0, e + b + 1⟩ := by
  rw [show (2 : ℕ) = 0 + 1 + 1 from by ring]
  cases b with
  | zero => step fm; step fm; step fm; step fm; step fm; step fm; finish
  | succ b =>
    step fm; step fm; step fm; step fm; step fm; step fm
    rw [show (6 : ℕ) = 5 + 1 from by ring]
    apply stepStar_trans (drain_b (b + 1) 5 (e + 1))
    ring_nf; finish

theorem tail_r3 : ⟨0, b, 0, 3, e + 1⟩ [fm]⊢⁺ ⟨3 * b + 8, 0, 0, 0, e + b + 2⟩ := by
  rw [show (3 : ℕ) = 0 + 2 + 1 from by ring]
  cases b with
  | zero =>
    step fm; step fm; step fm; step fm; step fm; step fm; step fm; step fm
    step fm; finish
  | succ b =>
    step fm; step fm; step fm; step fm; step fm; step fm; step fm
    rw [show (5 : ℕ) = 4 + 1 from by ring]
    apply stepStar_trans (drain_b (b + 2) 4 (e + 1))
    ring_nf; finish

theorem tail_r4 : ⟨0, b, 0, 4, e + 1⟩ [fm]⊢⁺ ⟨3 * b + 10, 0, 0, 0, e + b + 3⟩ := by
  rw [show (4 : ℕ) = 0 + 3 + 1 from by ring]
  cases b with
  | zero =>
    step fm; step fm; step fm; step fm; step fm; step fm; step fm; step fm
    rw [show (4 : ℕ) = 3 + 1 from by ring]
    apply stepStar_trans (drain_b 2 3 (e + 1))
    ring_nf; finish
  | succ b =>
    step fm; step fm; step fm; step fm; step fm; step fm; step fm; step fm
    rw [show (4 : ℕ) = 3 + 1 from by ring]
    apply stepStar_trans (drain_b (b + 3) 3 (e + 1))
    ring_nf; finish

theorem middle_phase : ∀ d : ℕ, d ≥ 1 → ∀ b e, e ≥ d →
    ∃ A E', A ≥ 1 ∧ (⟨0, b, 0, d, e⟩ : Q) [fm]⊢⁺ ⟨A, 0, 0, 0, E'⟩ := by
  intro d; induction' d using Nat.strongRecOn with d ih
  intro hd b e he
  by_cases h5 : d ≥ 5
  · obtain ⟨d', rfl⟩ : ∃ d', d = d' + 5 := ⟨d - 5, by omega⟩
    rw [show e = (e - 1) + 1 from by omega]
    by_cases hd' : d' ≥ 1
    · obtain ⟨A, E', hA, hstep⟩ := ih d' (by omega) hd' (b + 4) (e - 1) (by omega)
      exact ⟨A, E', hA, stepStar_stepPlus_stepPlus big_round hstep⟩
    · have : d' = 0 := by omega
      subst this; simp only [Nat.zero_add]
      refine ⟨3 * (b + 3) + 5, e - 2 + (b + 3), by omega, ?_⟩
      apply stepStar_stepPlus_stepPlus big_round
      rw [show b + 4 = (b + 3) + 1 from by ring,
          show e - 1 = (e - 2) + 1 from by omega]
      step fm; step fm
      rw [show (5 : ℕ) = 4 + 1 from by ring]
      apply stepStar_trans (drain_b (b + 3) 4 (e - 2))
      ring_nf; finish
  · have hd' : d = 1 ∨ d = 2 ∨ d = 3 ∨ d = 4 := by omega
    rcases hd' with rfl | rfl | rfl | rfl
    · rw [show e = (e - 1) + 1 from by omega]
      exact ⟨3 * b + 4, e - 1 + b, by omega, tail_r1⟩
    · rw [show e = (e - 1) + 1 from by omega]
      exact ⟨3 * b + 6, e - 1 + b + 1, by omega, tail_r2⟩
    · rw [show e = (e - 1) + 1 from by omega]
      exact ⟨3 * b + 8, e - 1 + b + 2, by omega, tail_r3⟩
    · rw [show e = (e - 1) + 1 from by omega]
      exact ⟨3 * b + 10, e - 1 + b + 3, by omega, tail_r4⟩

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨1, 0, 0, 0, 0⟩)
  · exists 0
  apply progress_nonhalt (fm := fm)
    (P := fun q ↦ ∃ a e, q = ⟨a, 0, 0, 0, e⟩ ∧ a ≥ 1)
  · intro c ⟨a, e, hq, ha⟩; subst hq
    have phase12 : (⟨a, 0, 0, 0, e⟩ : Q) [fm]⊢* ⟨0, 0, 0, a, e + a⟩ := by
      apply stepStar_trans (r3_loop a 0 e)
      simp only [Nat.zero_add]
      apply stepStar_trans (r4_loop a 0 (e + a))
      simp only [Nat.zero_add]; finish
    obtain ⟨A, E', hA, hstep⟩ := middle_phase a ha 0 (e + a) (by omega)
    exact ⟨⟨A, 0, 0, 0, E'⟩, ⟨A, E', rfl, hA⟩, stepStar_stepPlus_stepPlus phase12 hstep⟩
  · exact ⟨1, 0, rfl, by omega⟩

end Sz22_2003_unofficial_320
