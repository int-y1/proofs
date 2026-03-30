import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #1019: [4/15, 99/14, 275/2, 7/11, 2/5]

Vector representation:
```
 2 -1 -1  0  0
-1  2  0 -1  1
-1  0  2  0  1
 0  0  0  1 -1
 1  0 -1  0  0
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_1019

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a, b+1, c+1, d, e⟩ => some ⟨a+2, b, c, d, e⟩
  | ⟨a+1, b, c, d+1, e⟩ => some ⟨a, b+2, c, d, e+1⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b, c+2, d, e+1⟩
  | ⟨a, b, c, d, e+1⟩ => some ⟨a, b, c, d+1, e⟩
  | ⟨a, b, c+1, d, e⟩ => some ⟨a+1, b, c, d, e⟩
  | _ => none

theorem r4_chain : ∀ k, ∀ c d,
    ⟨(0 : ℕ), 0, c, d, k⟩ [fm]⊢* ⟨0, 0, c, d + k, 0⟩ := by
  intro k; induction' k with k ih <;> intro c d
  · ring_nf; finish
  · rw [show d + (k + 1) = (d + 1) + k from by ring]
    step fm
    apply stepStar_trans (ih c (d + 1))
    ring_nf; finish

theorem r3_chain : ∀ k, ∀ a c e,
    ⟨a + k, (0 : ℕ), c, 0, e⟩ [fm]⊢* ⟨a, 0, c + 2 * k, 0, e + k⟩ := by
  intro k; induction' k with k ih <;> intro a c e
  · ring_nf; finish
  · rw [show a + (k + 1) = (a + k) + 1 from by ring,
        show c + 2 * (k + 1) = (c + 2) + 2 * k from by ring,
        show e + (k + 1) = (e + 1) + k from by ring]
    step fm
    apply stepStar_trans (ih a (c + 2) (e + 1))
    ring_nf; finish

theorem r2r1r1_chain : ∀ k, ∀ a c d e,
    ⟨a + 1, (0 : ℕ), c + 2 * k, d + k, e⟩ [fm]⊢* ⟨a + 3 * k + 1, 0, c, d, e + k⟩ := by
  intro k; induction' k with k ih <;> intro a c d e
  · ring_nf; finish
  · rw [show c + 2 * (k + 1) = (c + 2 * k) + 2 from by ring,
        show d + (k + 1) = (d + k) + 1 from by ring,
        show a + 3 * (k + 1) + 1 = (a + 3) + 3 * k + 1 from by ring,
        show e + (k + 1) = (e + 1) + k from by ring]
    step fm; step fm; step fm
    apply stepStar_trans (ih (a + 3) c d (e + 1))
    ring_nf; finish

theorem r2_chain : ∀ k, ∀ a b e,
    ⟨a + k, b, (0 : ℕ), k, e⟩ [fm]⊢* ⟨a, b + 2 * k, 0, 0, e + k⟩ := by
  intro k; induction' k with k ih <;> intro a b e
  · ring_nf; finish
  · rw [show a + (k + 1) = (a + k) + 1 from by ring,
        show (k : ℕ) + 1 = k + 1 from rfl,
        show b + 2 * (k + 1) = (b + 2) + 2 * k from by ring,
        show e + (k + 1) = (e + 1) + k from by ring]
    step fm
    apply stepStar_trans (ih a (b + 2) (e + 1))
    ring_nf; finish

theorem r3r1r1_chain : ∀ k, ∀ a b e,
    ⟨a + 1, b + 2 * k, (0 : ℕ), 0, e⟩ [fm]⊢* ⟨a + 3 * k + 1, b, 0, 0, e + k⟩ := by
  intro k; induction' k with k ih <;> intro a b e
  · ring_nf; finish
  · rw [show b + 2 * (k + 1) = (b + 2 * k) + 2 from by ring,
        show a + 3 * (k + 1) + 1 = (a + 3) + 3 * k + 1 from by ring,
        show e + (k + 1) = (e + 1) + k from by ring]
    step fm; step fm; step fm
    apply stepStar_trans (ih (a + 3) b (e + 1))
    ring_nf; finish

-- Simple case: c ≥ 2e+1, any parity.
-- (0, 0, c, 0, e) →⁺ (0, 0, c+4e+1, 0, 4e+1).
theorem main_trans_simple (c e : ℕ) (he : e ≥ 1) (hc : c ≥ 2 * e + 1) :
    ⟨(0 : ℕ), 0, c, 0, e⟩ [fm]⊢⁺ ⟨0, 0, c + 4 * e + 1, 0, 4 * e + 1⟩ := by
  have h1 : ⟨(0 : ℕ), 0, c, 0, e⟩ [fm]⊢* ⟨0, 0, c, e, 0⟩ := by
    have := r4_chain e c 0
    rw [show (0 : ℕ) + e = e from by ring] at this; exact this
  have h2 : ⟨(0 : ℕ), 0, c, e, 0⟩ [fm]⊢⁺ ⟨1, 0, c - 1, e, 0⟩ := by
    rw [show c = (c - 1) + 1 from by omega]
    step fm; finish
  have h3 : ⟨(1 : ℕ), 0, c - 1, e, 0⟩ [fm]⊢* ⟨3 * e + 1, 0, c - 1 - 2 * e, 0, e⟩ := by
    have := r2r1r1_chain e 0 (c - 1 - 2 * e) 0 0
    rw [show (0 : ℕ) + 1 = 1 from by ring,
        show (c - 1 - 2 * e) + 2 * e = c - 1 from by omega,
        show (0 : ℕ) + e = e from by ring,
        show 0 + 3 * e + 1 = 3 * e + 1 from by ring] at this; exact this
  have h4 : ⟨3 * e + 1, (0 : ℕ), c - 1 - 2 * e, 0, e⟩ [fm]⊢*
      ⟨0, 0, c + 4 * e + 1, 0, 4 * e + 1⟩ := by
    have := r3_chain (3 * e + 1) 0 (c - 1 - 2 * e) e
    rw [show 0 + (3 * e + 1) = 3 * e + 1 from by ring,
        show (c - 1 - 2 * e) + 2 * (3 * e + 1) = c + 4 * e + 1 from by omega,
        show e + (3 * e + 1) = 4 * e + 1 from by ring] at this; exact this
  exact stepStar_stepPlus_stepPlus h1
    (stepPlus_stepStar_stepPlus h2 (stepStar_trans h3 h4))

-- Complex case, c odd: c = 2f+1, e+1 ≤ c ≤ 2e. So f < e.
-- (0, 0, 2f+1, 0, e) →⁺ (0, 0, 2f+4e+2, 0, 4e+1).
theorem main_trans_odd (f e : ℕ) (he : e ≥ 1) (hfe : e ≥ f + 1) (hce : 2 * f + 1 ≥ e + 1) :
    ⟨(0 : ℕ), 0, 2 * f + 1, 0, e⟩ [fm]⊢⁺
    ⟨0, 0, 2 * f + 4 * e + 2, 0, 4 * e + 1⟩ := by
  have h1 : ⟨(0 : ℕ), 0, 2 * f + 1, 0, e⟩ [fm]⊢* ⟨0, 0, 2 * f + 1, e, 0⟩ := by
    have := r4_chain e (2 * f + 1) 0
    rw [show (0 : ℕ) + e = e from by ring] at this; exact this
  have h2 : ⟨(0 : ℕ), 0, 2 * f + 1, e, 0⟩ [fm]⊢⁺ ⟨1, 0, 2 * f, e, 0⟩ := by
    rw [show 2 * f + 1 = (2 * f) + 1 from by ring]
    step fm; finish
  have h3 : ⟨(1 : ℕ), 0, 2 * f, e, 0⟩ [fm]⊢* ⟨3 * f + 1, 0, 0, e - f, f⟩ := by
    have := r2r1r1_chain f 0 0 (e - f) 0
    rw [show 0 + 1 = 1 from by ring,
        show 0 + 2 * f = 2 * f from by ring,
        show (e - f) + f = e from by omega,
        show 0 + 3 * f + 1 = 3 * f + 1 from by ring,
        show 0 + f = f from by ring] at this; exact this
  have h4 : ⟨3 * f + 1, (0 : ℕ), 0, e - f, f⟩ [fm]⊢*
      ⟨4 * f + 1 - e, 2 * (e - f), 0, 0, e⟩ := by
    have := r2_chain (e - f) (4 * f + 1 - e) 0 f
    rw [show 4 * f + 1 - e + (e - f) = 3 * f + 1 from by omega,
        show 0 + 2 * (e - f) = 2 * (e - f) from by ring,
        show f + (e - f) = e from by omega] at this; exact this
  have h5 : ⟨4 * f + 1 - e, 2 * (e - f), (0 : ℕ), 0, e⟩ [fm]⊢*
      ⟨f + 2 * e + 1, 0, 0, 0, 2 * e - f⟩ := by
    have := r3r1r1_chain (e - f) (4 * f - e) 0 e
    rw [show 4 * f - e + 1 = 4 * f + 1 - e from by omega,
        show 0 + 2 * (e - f) = 2 * (e - f) from by ring,
        show 4 * f - e + 3 * (e - f) + 1 = f + 2 * e + 1 from by omega,
        show e + (e - f) = 2 * e - f from by omega] at this; exact this
  have h6 : ⟨f + 2 * e + 1, (0 : ℕ), 0, 0, 2 * e - f⟩ [fm]⊢*
      ⟨0, 0, 2 * f + 4 * e + 2, 0, 4 * e + 1⟩ := by
    have := r3_chain (f + 2 * e + 1) 0 0 (2 * e - f)
    rw [show 0 + (f + 2 * e + 1) = f + 2 * e + 1 from by ring,
        show 0 + 2 * (f + 2 * e + 1) = 2 * f + 4 * e + 2 from by ring,
        show 2 * e - f + (f + 2 * e + 1) = 4 * e + 1 from by omega] at this; exact this
  exact stepStar_stepPlus_stepPlus h1
    (stepPlus_stepStar_stepPlus h2
      (stepStar_trans h3 (stepStar_trans h4 (stepStar_trans h5 h6))))

-- Complex case, c even: c = 2m, e+1 ≤ c ≤ 2e. So m ≤ e.
-- f = m-1, R2R1R1 × f then R2R1, R2 chain, R3R1R1, R3R1, R3 chain.
-- (0, 0, 2m, 0, e) →⁺ (0, 0, 2m+4e+1, 0, 4e+1).
theorem main_trans_even (m e : ℕ) (hm : m ≥ 1) (he : e ≥ m) (hce : 2 * m ≥ e + 1) :
    ⟨(0 : ℕ), 0, 2 * m, 0, e⟩ [fm]⊢⁺
    ⟨0, 0, 2 * m + 4 * e + 1, 0, 4 * e + 1⟩ := by
  have h1 : ⟨(0 : ℕ), 0, 2 * m, 0, e⟩ [fm]⊢* ⟨0, 0, 2 * m, e, 0⟩ := by
    have := r4_chain e (2 * m) 0
    rw [show (0 : ℕ) + e = e from by ring] at this; exact this
  have h2 : ⟨(0 : ℕ), 0, 2 * m, e, 0⟩ [fm]⊢⁺ ⟨1, 0, 2 * m - 1, e, 0⟩ := by
    rw [show 2 * m = (2 * m - 1) + 1 from by omega]
    step fm; finish
  -- R2R1R1 × (m-1) rounds: c goes from 2m-1 to 1, d from e to e-m+1
  have h3 : ⟨(1 : ℕ), 0, 2 * m - 1, e, 0⟩ [fm]⊢*
      ⟨3 * m - 2, 0, 1, e - m + 1, m - 1⟩ := by
    have := r2r1r1_chain (m - 1) 0 1 (e - m + 1) 0
    rw [show 0 + 1 = 1 from by ring,
        show 1 + 2 * (m - 1) = 2 * m - 1 from by omega,
        show (e - m + 1) + (m - 1) = e from by omega,
        show 0 + 3 * (m - 1) + 1 = 3 * m - 2 from by omega,
        show 0 + (m - 1) = m - 1 from by omega] at this; exact this
  -- R2, R1: (3m-2, 0, 1, e-m+1, m-1) → (3m-1, 1, 0, e-m, m)
  have h4 : ⟨3 * m - 2, (0 : ℕ), 1, e - m + 1, m - 1⟩ [fm]⊢*
      ⟨3 * m - 1, 1, 0, e - m, m⟩ := by
    rw [show 3 * m - 2 = (3 * m - 2 - 1) + 1 from by omega,
        show e - m + 1 = (e - m) + 1 from by omega]
    step fm; step fm
    rw [show 3 * m - 2 - 1 + 2 = 3 * m - 1 from by omega,
        show m - 1 + 1 = m from by omega]
    finish
  -- R2-only × (e-m) rounds
  have h5 : ⟨3 * m - 1, (1 : ℕ), 0, e - m, m⟩ [fm]⊢*
      ⟨4 * m - 1 - e, 2 * e - 2 * m + 1, 0, 0, e⟩ := by
    have := r2_chain (e - m) (4 * m - 1 - e) 1 m
    rw [show 4 * m - 1 - e + (e - m) = 3 * m - 1 from by omega,
        show 1 + 2 * (e - m) = 2 * e - 2 * m + 1 from by omega,
        show m + (e - m) = e from by omega] at this; exact this
  -- R3R1R1 × (e-m) rounds
  have h6 : ⟨4 * m - 1 - e, 2 * e - 2 * m + 1, (0 : ℕ), 0, e⟩ [fm]⊢*
      ⟨m + 2 * e - 1, 1, 0, 0, 2 * e - m⟩ := by
    have := r3r1r1_chain (e - m) (4 * m - 2 - e) 1 e
    rw [show 4 * m - 2 - e + 1 = 4 * m - 1 - e from by omega,
        show 1 + 2 * (e - m) = 2 * e - 2 * m + 1 from by omega,
        show 4 * m - 2 - e + 3 * (e - m) + 1 = m + 2 * e - 1 from by omega,
        show e + (e - m) = 2 * e - m from by omega] at this; exact this
  -- R3, R1: (m+2e-1, 1, 0, 0, 2e-m) → (m+2e, 0, 1, 0, 2e-m+1)
  have h7 : ⟨m + 2 * e - 1, (1 : ℕ), 0, 0, 2 * e - m⟩ [fm]⊢*
      ⟨m + 2 * e, 0, 1, 0, 2 * e - m + 1⟩ := by
    rw [show m + 2 * e - 1 = (m + 2 * e - 2) + 1 from by omega]
    step fm; step fm
    rw [show m + 2 * e - 2 + 2 = m + 2 * e from by omega,
        show 2 * e - m + 1 = 2 * e - m + 1 from rfl]
    finish
  -- R3 chain × (m+2e) rounds
  have h8 : ⟨m + 2 * e, (0 : ℕ), 1, 0, 2 * e - m + 1⟩ [fm]⊢*
      ⟨0, 0, 2 * m + 4 * e + 1, 0, 4 * e + 1⟩ := by
    have := r3_chain (m + 2 * e) 0 1 (2 * e - m + 1)
    rw [show 0 + (m + 2 * e) = m + 2 * e from by ring,
        show 1 + 2 * (m + 2 * e) = 2 * m + 4 * e + 1 from by ring,
        show (2 * e - m + 1) + (m + 2 * e) = 4 * e + 1 from by omega] at this; exact this
  exact stepStar_stepPlus_stepPlus h1
    (stepPlus_stepStar_stepPlus h2
      (stepStar_trans h3 (stepStar_trans h4 (stepStar_trans h5
        (stepStar_trans h6 (stepStar_trans h7 h8))))))

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨0, 0, 2, 0, 1⟩) (by execute fm 1)
  apply progress_nonhalt (fm := fm)
    (P := fun q ↦ ∃ c e, q = ⟨0, 0, c, 0, e⟩ ∧ c ≥ e + 1 ∧ e ≥ 1)
  · intro q ⟨c, e, hq, hce, he⟩
    subst hq
    refine ⟨⟨0, 0, c + 4 * e + 1, 0, 4 * e + 1⟩,
      ⟨c + 4 * e + 1, 4 * e + 1, rfl, by omega, by omega⟩, ?_⟩
    by_cases h : c ≥ 2 * e + 1
    · exact main_trans_simple c e he h
    · push_neg at h
      rcases Nat.even_or_odd c with ⟨m, hm⟩ | ⟨m, hm⟩
      · subst hm
        rw [show m + m = 2 * m from by ring,
            show 2 * m + 4 * e + 1 = 2 * m + 4 * e + 1 from rfl]
        exact main_trans_even m e (by omega) (by omega) (by omega)
      · subst hm
        rw [show 2 * m + 1 + 4 * e + 1 = 2 * m + 4 * e + 2 from by ring]
        exact main_trans_odd m e he (by omega) (by omega)
  · exact ⟨2, 1, rfl, by omega, by omega⟩
