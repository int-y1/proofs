import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #1345: [63/10, 28/33, 143/2, 5/7, 3/13]

Vector representation:
```
-1  2 -1  1  0  0
 2 -1  0  1 -1  0
-1  0  0  0  1  1
 0  0  1 -1  0  0
 0  1  0  0  0 -1
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_1345

def Q := ℕ × ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a+1, b, c+1, d, e, f⟩ => some ⟨a, b+2, c, d+1, e, f⟩
  | ⟨a, b+1, c, d, e+1, f⟩ => some ⟨a+2, b, c, d+1, e, f⟩
  | ⟨a+1, b, c, d, e, f⟩ => some ⟨a, b, c, d, e+1, f+1⟩
  | ⟨a, b, c, d+1, e, f⟩ => some ⟨a, b, c+1, d, e, f⟩
  | ⟨a, b, c, d, e, f+1⟩ => some ⟨a, b+1, c, d, e, f⟩
  | _ => none

theorem r3_drain : ∀ k, ∀ a d e f,
    ⟨a + k, (0 : ℕ), (0 : ℕ), d, e, f⟩ [fm]⊢*
    ⟨a, (0 : ℕ), (0 : ℕ), d, e + k, f + k⟩ := by
  intro k; induction' k with k ih <;> intro a d e f
  · exists 0
  · rw [show a + (k + 1) = (a + k) + 1 from by ring]; step fm
    apply stepStar_trans (ih a d (e + 1) (f + 1)); ring_nf; finish

theorem r4_transfer : ∀ k, ∀ c d e f,
    ⟨(0 : ℕ), (0 : ℕ), c, d + k, e, f⟩ [fm]⊢*
    ⟨(0 : ℕ), (0 : ℕ), c + k, d, e, f⟩ := by
  intro k; induction' k with k ih <;> intro c d e f
  · exists 0
  · rw [show d + (k + 1) = (d + k) + 1 from by ring]; step fm
    apply stepStar_trans (ih (c + 1) d e f); ring_nf; finish

theorem r211_chain : ∀ k, ∀ b c d e f,
    ⟨(0 : ℕ), b + 1, c + 2 * k, d, e + k, f⟩ [fm]⊢*
    ⟨(0 : ℕ), b + 1 + 3 * k, c, d + 3 * k, e, f⟩ := by
  intro k; induction' k with k ih <;> intro b c d e f
  · simp; exists 0
  · rw [show c + 2 * (k + 1) = (c + 2 * k) + 2 from by ring,
        show e + (k + 1) = (e + k) + 1 from by ring]
    step fm; step fm; step fm
    rw [show b + 2 + 2 = (b + 3) + 1 from by ring,
        show d + 1 + 1 + 1 = d + 3 from by ring]
    apply stepStar_trans (ih (b + 3) c (d + 3) e f); ring_nf; finish

theorem r2_drain : ∀ k, ∀ a b d e f,
    ⟨a, b + k, (0 : ℕ), d, e + k, f⟩ [fm]⊢*
    ⟨a + 2 * k, b, (0 : ℕ), d + k, e, f⟩ := by
  intro k; induction' k with k ih <;> intro a b d e f
  · simp; exists 0
  · rw [show b + (k + 1) = (b + k) + 1 from by ring,
        show e + (k + 1) = (e + k) + 1 from by ring]
    step fm
    apply stepStar_trans (ih (a + 2) b (d + 1) e f); ring_nf; finish

theorem r32_chain : ∀ k, ∀ a b d f,
    ⟨a + 1, b + k, (0 : ℕ), d, (0 : ℕ), f⟩ [fm]⊢*
    ⟨a + k + 1, b, (0 : ℕ), d + k, (0 : ℕ), f + k⟩ := by
  intro k; induction' k with k ih <;> intro a b d f
  · exists 0
  · rw [show b + (k + 1) = (b + k) + 1 from by ring]
    step fm; step fm
    apply stepStar_trans (ih (a + 1) b (d + 1) (f + 1)); ring_nf; finish

-- Even d tail: from state after opening to final
theorem tail_even (m a f : ℕ) (hm : m ≥ 1) (ha : a ≥ m + 1) (hle : a ≤ 4 * m + 1) :
    ⟨(0 : ℕ), (4 : ℕ), 2 * m - 2, (3 : ℕ), a - 1, f + a - 1⟩ [fm]⊢*
    ⟨a + 2 * m + 1, (0 : ℕ), (0 : ℕ), 6 * m + 1, (0 : ℕ), f + 4 * m⟩ := by
  have h211 := r211_chain (m - 1) 3 0 3 (a - m) (f + a - 1)
  rw [show 0 + 2 * (m - 1) = 2 * m - 2 from by omega,
      show (a - m) + (m - 1) = a - 1 from by omega,
      show 3 + 1 + 3 * (m - 1) = 3 * m + 1 from by omega,
      show 3 + 3 * (m - 1) = 3 * m from by omega,
      show (3 : ℕ) + 1 = 4 from rfl] at h211
  apply stepStar_trans h211
  have hrd := r2_drain (a - m) 0 (4 * m + 1 - a) (3 * m) 0 (f + a - 1)
  rw [show (4 * m + 1 - a) + (a - m) = 3 * m + 1 from by omega,
      show 0 + (a - m) = a - m from by ring,
      show 0 + 2 * (a - m) = 2 * a - 2 * m from by omega,
      show 3 * m + (a - m) = 2 * m + a from by omega] at hrd
  apply stepStar_trans hrd
  have hr32 := r32_chain (4 * m + 1 - a) (2 * a - 2 * m - 1) 0 (2 * m + a) (f + a - 1)
  rw [show (2 * a - 2 * m - 1) + 1 = 2 * a - 2 * m from by omega,
      show 0 + (4 * m + 1 - a) = 4 * m + 1 - a from by ring,
      show (2 * a - 2 * m - 1) + (4 * m + 1 - a) + 1 = a + 2 * m + 1 from by omega,
      show (2 * m + a) + (4 * m + 1 - a) = 6 * m + 1 from by omega,
      show (f + a - 1) + (4 * m + 1 - a) = f + 4 * m from by omega] at hr32
  exact hr32

theorem main_even (m a f : ℕ) (hm : m ≥ 1) (ha : a ≥ m + 1) (hle : a ≤ 4 * m + 1) :
    ⟨a, (0 : ℕ), (0 : ℕ), 2 * m, (0 : ℕ), f⟩ [fm]⊢⁺
    ⟨a + 2 * m + 1, (0 : ℕ), (0 : ℕ), 6 * m + 1, (0 : ℕ), f + 4 * m⟩ := by
  rw [show (a : ℕ) = 0 + a from by ring]
  apply stepStar_stepPlus_stepPlus (r3_drain a 0 (2 * m) 0 f)
  rw [show 0 + a = a from by ring, show 2 * m = 0 + 2 * m from by ring]
  apply stepStar_stepPlus_stepPlus (r4_transfer (2 * m) 0 0 a (f + a))
  suffices h : ⟨(0 : ℕ), (0 : ℕ), 2 * m, (0 : ℕ), a, f + a⟩ [fm]⊢⁺
      ⟨a + 2 * m + 1, (0 : ℕ), (0 : ℕ), 6 * m + 1, (0 : ℕ), f + 4 * m⟩ by
    rwa [show (0 : ℕ) + 2 * m = 2 * m from by ring]
  rw [show f + a = (f + a - 1) + 1 from by omega,
      show 2 * m = (2 * m - 2) + 2 from by omega,
      show (a : ℕ) = (a - 1) + 1 from by omega]
  step fm; step fm; step fm; step fm
  rw [show f + (a - 1 + 1) - 1 = f + a - 1 from by omega,
      show a - 1 + 1 + (2 * m - 2 + 2) + 1 = a + 2 * m + 1 from by omega]
  exact stepPlus_stepStar (stepStar_stepPlus (tail_even m a f hm ha hle) (by simp [Q]))

-- Odd d=1 tail
theorem tail_odd_zero (a f : ℕ) (ha : a ≥ 1) (hle : a ≤ 3) :
    ⟨(1 : ℕ), (2 : ℕ), (0 : ℕ), (2 : ℕ), a - 1, f + a - 1⟩ [fm]⊢*
    ⟨a + 2, (0 : ℕ), (0 : ℕ), (4 : ℕ), (0 : ℕ), f + 2⟩ := by
  have hrd := r2_drain (a - 1) 1 (3 - a) 2 0 (f + a - 1)
  rw [show (3 - a) + (a - 1) = 2 from by omega,
      show 0 + (a - 1) = a - 1 from by ring,
      show 1 + 2 * (a - 1) = 2 * a - 1 from by omega,
      show 2 + (a - 1) = a + 1 from by omega] at hrd
  apply stepStar_trans hrd
  have hr32 := r32_chain (3 - a) (2 * a - 2) 0 (a + 1) (f + a - 1)
  rw [show (2 * a - 2) + 1 = 2 * a - 1 from by omega,
      show 0 + (3 - a) = 3 - a from by ring,
      show (2 * a - 2) + (3 - a) + 1 = a + 2 from by omega,
      show (a + 1) + (3 - a) = 4 from by omega,
      show (f + a - 1) + (3 - a) = f + 2 from by omega] at hr32
  exact hr32

theorem main_odd_zero (a f : ℕ) (ha : a ≥ 1) (hle : a ≤ 3) :
    ⟨a, (0 : ℕ), (0 : ℕ), (1 : ℕ), (0 : ℕ), f⟩ [fm]⊢⁺
    ⟨a + 2, (0 : ℕ), (0 : ℕ), (4 : ℕ), (0 : ℕ), f + 2⟩ := by
  rw [show (a : ℕ) = 0 + a from by ring]
  apply stepStar_stepPlus_stepPlus (r3_drain a 0 1 0 f)
  rw [show 0 + a = a from by ring, show (1 : ℕ) = 0 + 1 from by ring]
  apply stepStar_stepPlus_stepPlus (r4_transfer 1 0 0 a (f + a))
  suffices h : ⟨(0 : ℕ), (0 : ℕ), (1 : ℕ), (0 : ℕ), a, f + a⟩ [fm]⊢⁺
      ⟨a + 2, (0 : ℕ), (0 : ℕ), (4 : ℕ), (0 : ℕ), f + 2⟩ by
    rwa [show (0 : ℕ) + 1 = 1 from by ring]
  rw [show f + a = (f + a - 1) + 1 from by omega,
      show (a : ℕ) = (a - 1) + 1 from by omega]
  step fm; step fm; step fm
  rw [show f + (a - 1 + 1) - 1 = f + a - 1 from by omega,
      show a - 1 + 1 + 2 = a + 2 from by omega]
  exact stepPlus_stepStar (stepStar_stepPlus (tail_odd_zero a f ha hle) (by simp [Q]))

-- Odd d=2m+1 tail (m ≥ 1)
theorem tail_odd_succ (m a f : ℕ) (hm : m ≥ 1) (ha : a ≥ m + 1) (hle : a ≤ 4 * m + 3) :
    ⟨(0 : ℕ), (4 : ℕ), 2 * m - 1, (3 : ℕ), a - 1, f + a - 1⟩ [fm]⊢*
    ⟨a + 2 * m + 2, (0 : ℕ), (0 : ℕ), 6 * m + 4, (0 : ℕ), f + 4 * m + 2⟩ := by
  have h211 := r211_chain (m - 1) 3 1 3 (a - m) (f + a - 1)
  rw [show 1 + 2 * (m - 1) = 2 * m - 1 from by omega,
      show (a - m) + (m - 1) = a - 1 from by omega,
      show 3 + 1 + 3 * (m - 1) = 3 * m + 1 from by omega,
      show 3 + 3 * (m - 1) = 3 * m from by omega,
      show (3 : ℕ) + 1 = 4 from rfl] at h211
  apply stepStar_trans h211
  -- R2, R1 to consume c=1
  rw [show 3 * m + 1 = (3 * m) + 1 from by ring,
      show a - m = (a - m - 1) + 1 from by omega]
  step fm; step fm
  rw [show 3 * m + 2 = 3 * m + 2 from rfl]
  have hrd := r2_drain (a - m - 1) 1 (4 * m + 3 - a) (3 * m + 2) 0 (f + a - 1)
  rw [show (4 * m + 3 - a) + (a - m - 1) = 3 * m + 2 from by omega,
      show 0 + (a - m - 1) = a - m - 1 from by ring,
      show 1 + 2 * (a - m - 1) = 2 * a - 2 * m - 1 from by omega,
      show (3 * m + 2) + (a - m - 1) = 2 * m + a + 1 from by omega] at hrd
  apply stepStar_trans hrd
  have hr32 := r32_chain (4 * m + 3 - a) (2 * a - 2 * m - 2) 0 (2 * m + a + 1) (f + a - 1)
  rw [show (2 * a - 2 * m - 2) + 1 = 2 * a - 2 * m - 1 from by omega,
      show 0 + (4 * m + 3 - a) = 4 * m + 3 - a from by ring,
      show (2 * a - 2 * m - 2) + (4 * m + 3 - a) + 1 = a + 2 * m + 2 from by omega,
      show (2 * m + a + 1) + (4 * m + 3 - a) = 6 * m + 4 from by omega,
      show (f + a - 1) + (4 * m + 3 - a) = f + 4 * m + 2 from by omega] at hr32
  exact hr32

theorem main_odd_succ (m a f : ℕ) (hm : m ≥ 1) (ha : a ≥ m + 1) (hle : a ≤ 4 * m + 3) :
    ⟨a, (0 : ℕ), (0 : ℕ), 2 * m + 1, (0 : ℕ), f⟩ [fm]⊢⁺
    ⟨a + 2 * m + 2, (0 : ℕ), (0 : ℕ), 6 * m + 4, (0 : ℕ), f + 4 * m + 2⟩ := by
  rw [show (a : ℕ) = 0 + a from by ring]
  apply stepStar_stepPlus_stepPlus (r3_drain a 0 (2 * m + 1) 0 f)
  rw [show 0 + a = a from by ring, show 2 * m + 1 = 0 + (2 * m + 1) from by ring]
  apply stepStar_stepPlus_stepPlus (r4_transfer (2 * m + 1) 0 0 a (f + a))
  suffices h : ⟨(0 : ℕ), (0 : ℕ), 2 * m + 1, (0 : ℕ), a, f + a⟩ [fm]⊢⁺
      ⟨a + 2 * m + 2, (0 : ℕ), (0 : ℕ), 6 * m + 4, (0 : ℕ), f + 4 * m + 2⟩ by
    rwa [show (0 : ℕ) + (2 * m + 1) = 2 * m + 1 from by ring]
  rw [show f + a = (f + a - 1) + 1 from by omega,
      show 2 * m + 1 = (2 * m - 1) + 2 from by omega,
      show (a : ℕ) = (a - 1) + 1 from by omega]
  step fm; step fm; step fm; step fm
  rw [show a - 1 + 1 + 2 * m + 2 = a + 2 * m + 2 from by omega,
      show f + (a - 1 + 1) - 1 = f + a - 1 from by omega]
  exact stepPlus_stepStar (stepStar_stepPlus (tail_odd_succ m a f hm ha hle) (by simp [Q]))

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨2, 0, 0, 1, 0, 0⟩) (by execute fm 3)
  apply progress_nonhalt (fm := fm)
    (P := fun q ↦ ∃ a d f, q = ⟨a, 0, 0, d, 0, f⟩ ∧ 2 * a ≥ d + 1 ∧ a ≤ 2 * d + 1 ∧ d ≥ 1)
  · intro c ⟨a, d, f, hq, hinv1, hinv2, hd⟩
    subst hq
    rcases Nat.even_or_odd d with ⟨m, hm⟩ | ⟨m, hm⟩
    · rw [show m + m = 2 * m from by ring] at hm; subst hm
      exact ⟨⟨a + 2 * m + 1, 0, 0, 6 * m + 1, 0, f + 4 * m⟩,
        ⟨a + 2 * m + 1, 6 * m + 1, f + 4 * m, rfl, by omega, by omega, by omega⟩,
        main_even m a f (by omega) (by omega) (by omega)⟩
    · subst hm
      rcases m with _ | m
      · exact ⟨⟨a + 2, 0, 0, 4, 0, f + 2⟩,
          ⟨a + 2, 4, f + 2, rfl, by omega, by omega, by omega⟩,
          main_odd_zero a f (by omega) (by omega)⟩
      · exact ⟨⟨a + 2 * (m + 1) + 2, 0, 0, 6 * (m + 1) + 4, 0, f + 4 * (m + 1) + 2⟩,
          ⟨a + 2 * (m + 1) + 2, 6 * (m + 1) + 4, f + 4 * (m + 1) + 2, rfl,
           by omega, by omega, by omega⟩,
          main_odd_succ (m + 1) a f (by omega) (by omega) (by omega)⟩
  · exact ⟨2, 1, 0, rfl, by omega, by omega, by omega⟩

end Sz22_2003_unofficial_1345
