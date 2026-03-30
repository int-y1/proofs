import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #1145: [5/6, 44/35, 539/2, 3/11, 25/7]

Vector representation:
```
-1 -1  1  0  0
 2  0 -1 -1  1
-1  0  0  2  1
 0  1  0  0 -1
 0  0  2 -1  0
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_1145

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a+1, b+1, c, d, e⟩ => some ⟨a, b, c+1, d, e⟩
  | ⟨a, b, c+1, d+1, e⟩ => some ⟨a+2, b, c, d, e+1⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b, c, d+2, e+1⟩
  | ⟨a, b, c, d, e+1⟩ => some ⟨a, b+1, c, d, e⟩
  | ⟨a, b, c, d+1, e⟩ => some ⟨a, b, c+2, d, e⟩
  | _ => none

theorem round_step :
    ⟨0, b+2, c+1, d+1, e⟩ [fm]⊢* ⟨(0 : ℕ), b, c+2, d, e+1⟩ := by
  step fm; step fm; step fm; finish

theorem interaction_chain :
    ∀ k, ∀ c d e, ⟨0, 2*k, c+1, d+k, e⟩ [fm]⊢* ⟨(0 : ℕ), 0, c+k+1, d, e+k⟩ := by
  intro k; induction' k with k ih <;> intro c d e
  · exists 0
  · rw [show 2 * (k + 1) = (2 * k) + 2 from by ring,
        show d + (k + 1) = d + k + 1 from by ring]
    apply stepStar_trans (round_step (b := 2 * k) (c := c) (d := d + k) (e := e))
    rw [show c + 2 = (c + 1) + 1 from by ring]
    apply stepStar_trans (ih (c + 1) d (e + 1))
    ring_nf; finish

theorem r2_chain :
    ∀ k, ∀ a c d e, ⟨a, 0, c+k, d+k, e⟩ [fm]⊢* ⟨a+2*k, 0, c, d, e+k⟩ := by
  intro k; induction' k with k ih <;> intro a c d e
  · exists 0
  · rw [show c + (k + 1) = (c + k) + 1 from by ring,
        show d + (k + 1) = (d + k) + 1 from by ring]
    step fm
    apply stepStar_trans (ih (a + 2) c d (e + 1))
    ring_nf; finish

theorem r3_chain :
    ∀ k, ∀ a d e, ⟨a+k, 0, 0, d, e⟩ [fm]⊢* ⟨a, 0, 0, d+2*k, e+k⟩ := by
  intro k; induction' k with k ih <;> intro a d e
  · exists 0
  · rw [show a + (k + 1) = (a + k) + 1 from by ring]
    step fm
    apply stepStar_trans (ih a (d + 2) (e + 1))
    ring_nf; finish

theorem r4_chain :
    ∀ k, ∀ b d e, ⟨0, b, 0, d, e+k⟩ [fm]⊢* ⟨(0 : ℕ), b+k, 0, d, e⟩ := by
  intro k; induction' k with k ih <;> intro b d e
  · exists 0
  · rw [show e + (k + 1) = (e + k) + 1 from by ring]
    step fm
    apply stepStar_trans (ih (b + 1) d e)
    ring_nf; finish

-- Drain c (even) + R3 chain + R4 chain combined.
theorem drain_even_r3_r4 (m a e : ℕ) :
    ⟨a+1, 0, 2*(m+1), 0, e⟩ [fm]⊢* ⟨(0 : ℕ), a+e+6*m+7, 0, 2*a+6*m+8, 0⟩ := by
  -- drain_even
  apply stepStar_trans
  · exact (drain_even_aux m a e)
  -- R3+R4
  rw [show a + 3 * m + 4 = 0 + (a + 3 * m + 4) from by ring]
  apply stepStar_trans (r3_chain (a + 3 * m + 4) 0 0 (e + 3 * m + 3))
  rw [show 0 + 2 * (a + 3 * m + 4) = 2 * a + 6 * m + 8 from by ring,
      show e + 3 * m + 3 + (a + 3 * m + 4) = 0 + (a + e + 6 * m + 7) from by ring]
  apply stepStar_trans (r4_chain (a + e + 6 * m + 7) 0 (2 * a + 6 * m + 8) 0)
  ring_nf; finish
where
  drain_even_aux : ∀ m, ∀ a e, ⟨a+1, 0, 2*(m+1), 0, e⟩ [fm]⊢* ⟨a+3*m+4, 0, 0, 0, e+3*m+3⟩ := by
    intro m; induction' m with m ih <;> intro a e
    · rw [show 2 * (0 + 1) = 0 + 2 from by ring]
      step fm; step fm; step fm
      ring_nf; finish
    · rw [show 2 * ((m + 1) + 1) = (2 * (m + 1)) + 2 from by ring]
      step fm; step fm; step fm
      rw [show a + 4 = (a + 3) + 1 from by ring]
      apply stepStar_trans (ih (a + 3) (e + 3))
      ring_nf; finish

-- Drain c (odd, m >= 1) + tail + R3 chain + R4 chain combined.
theorem drain_odd_r3_r4 (m a e : ℕ) :
    ⟨a+1, 0, 2*m+1, 0, e⟩ [fm]⊢* ⟨(0 : ℕ), a+e+6*m+4, 0, 2*a+6*m+5, 0⟩ := by
  -- drain_odd_to_one
  apply stepStar_trans
  · exact (drain_odd_aux m a e)
  -- drain_tail
  rw [show a + 3 * m + 1 = (a + 3 * m) + 1 from by ring]
  apply stepStar_trans (drain_tail_lemma (a + 3 * m) (e + 3 * m))
  -- R3+R4
  rw [show a + 3 * m + 2 = 0 + (a + 3 * m + 2) from by ring]
  apply stepStar_trans (r3_chain (a + 3 * m + 2) 0 1 (e + 3 * m + 2))
  rw [show 1 + 2 * (a + 3 * m + 2) = 2 * a + 6 * m + 5 from by ring,
      show e + 3 * m + 2 + (a + 3 * m + 2) = 0 + (a + e + 6 * m + 4) from by ring]
  apply stepStar_trans (r4_chain (a + e + 6 * m + 4) 0 (2 * a + 6 * m + 5) 0)
  ring_nf; finish
where
  drain_odd_aux : ∀ m, ∀ a e, ⟨a+1, 0, 2*m+1, 0, e⟩ [fm]⊢* ⟨a+3*m+1, 0, 1, 0, e+3*m⟩ := by
    intro m; induction' m with m ih <;> intro a e
    · exists 0
    · rw [show 2 * (m + 1) + 1 = (2 * m + 1) + 2 from by ring]
      step fm; step fm; step fm
      rw [show a + 4 = (a + 3) + 1 from by ring]
      apply stepStar_trans (ih (a + 3) (e + 3))
      ring_nf; finish
  drain_tail_lemma : ∀ a e, ⟨a+1, 0, 1, 0, e⟩ [fm]⊢* ⟨a+2, 0, 0, 1, e+2⟩ := by
    intro a e; step fm; step fm; finish

-- Drain c = 1: tail + R3 chain + R4 chain.
theorem drain_c1_r3_r4 (a e : ℕ) :
    ⟨a+1, 0, 1, 0, e⟩ [fm]⊢* ⟨(0 : ℕ), a+e+4, 0, 2*a+5, 0⟩ := by
  step fm; step fm
  rw [show a + 2 = 0 + (a + 2) from by ring]
  apply stepStar_trans (r3_chain (a + 2) 0 1 (e + 2))
  rw [show 1 + 2 * (a + 2) = 2 * a + 5 from by ring,
      show e + 2 + (a + 2) = 0 + (a + e + 4) from by ring]
  apply stepStar_trans (r4_chain (a + e + 4) 0 (2 * a + 5) 0)
  ring_nf; finish

-- Main transition: (0, 2h, 0, h+1+j, 0) ⊢⁺ (0, 4h+6, 0, 3h+j+6, 0)
-- where 1 <= j <= h+1.
theorem main_transition (h j : ℕ) (hj1 : j ≥ 1) (hj2 : j ≤ h + 1) :
    ⟨0, 2*h, 0, h+1+j, 0⟩ [fm]⊢⁺ ⟨(0 : ℕ), 4*h+6, 0, 3*h+j+6, 0⟩ := by
  -- Phase 1: R5
  rw [show h + 1 + j = (h + j) + 1 from by ring]
  step fm
  rw [show h + j = j + h from by ring]
  show ⟨0, 2 * h, 1 + 1, j + h, 0⟩ [fm]⊢* _
  apply stepStar_trans (interaction_chain h 1 j 0)
  rw [show 0 + h = h from by ring]
  have hr2 := r2_chain j 0 (h + 2 - j) 0 h
  rw [show 0 + 2 * j = 2 * j from by ring, show 0 + j = j from by ring,
      show (h + 2 - j) + j = 1 + h + 1 from by omega, show h + j = h + j from rfl] at hr2
  apply stepStar_trans hr2
  rcases Nat.even_or_odd (h + 2 - j) with ⟨K, hK⟩ | ⟨K, hK⟩
  · -- c_rem even
    rcases K with _ | m
    · omega
    ·
      rw [show (m + 1) + (m + 1) = 2 * (m + 1) from by ring] at hK
      rw [hK, show 2 * j = (2 * j - 1) + 1 from by omega]
      apply stepStar_trans (drain_even_r3_r4 m (2 * j - 1) (h + j))
      rw [show 2 * j - 1 + (h + j) + 6 * m + 7 = 4 * h + 6 from by omega,
          show 2 * (2 * j - 1) + 6 * m + 8 = 3 * h + j + 6 from by omega]
      finish
  · -- c_rem odd
    rcases K with _ | K
    · simp at hK; rw [hK, show 2 * j = (2 * j - 1) + 1 from by omega]
      apply stepStar_trans (drain_c1_r3_r4 (2 * j - 1) (h + j))
      rw [show 2 * j - 1 + (h + j) + 4 = 4 * h + 6 from by omega,
          show 2 * (2 * j - 1) + 5 = 3 * h + j + 6 from by omega]
      finish
    · rw [hK, show 2 * j = (2 * j - 1) + 1 from by omega]
      apply stepStar_trans (drain_odd_r3_r4 (K + 1) (2 * j - 1) (h + j))
      rw [show 2 * j - 1 + (h + j) + 6 * (K + 1) + 4 = 4 * h + 6 from by omega,
          show 2 * (2 * j - 1) + 6 * (K + 1) + 5 = 3 * h + j + 6 from by omega]
      finish

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨0, 8, 0, 8, 0⟩) (by execute fm 20)
  apply progress_nonhalt (fm := fm)
    (P := fun q ↦ ∃ h j, q = ⟨0, 2*h, 0, h+1+j, 0⟩ ∧ j ≥ 1 ∧ j ≤ h + 1 ∧ h ≥ 4)
  · intro c ⟨h, j, hq, hj1, hj2, hh⟩; subst hq
    refine ⟨⟨0, 4*h+6, 0, 3*h+j+6, 0⟩,
      ⟨2*h+3, h+j+2, ?_, by omega, by omega, by omega⟩,
      main_transition h j hj1 hj2⟩
    rw [show 4 * h + 6 = 2 * (2 * h + 3) from by ring,
        show 3 * h + j + 6 = 2 * h + 3 + 1 + (h + j + 2) from by ring]
  · exact ⟨4, 3, rfl, by omega, by omega, by omega⟩
