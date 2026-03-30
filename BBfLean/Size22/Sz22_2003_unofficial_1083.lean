import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #1083: [5/6, 196/55, 847/2, 3/7, 5/3]

Vector representation:
```
-1 -1  1  0  0
 2  0 -1  2 -1
-1  0  0  1  2
 0  1  0 -1  0
 0 -1  1  0  0
```

This Fractran program doesn't halt.

Author: Claude
-/

namespace Sz22_2003_unofficial_1083

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a+1, b+1, c, d, e⟩ => some ⟨a, b, c+1, d, e⟩
  | ⟨a, b, c+1, d, e+1⟩ => some ⟨a+2, b, c, d+2, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b, c, d+1, e+2⟩
  | ⟨a, b, c, d+1, e⟩ => some ⟨a, b+1, c, d, e⟩
  | ⟨a, b+1, c, d, e⟩ => some ⟨a, b, c+1, d, e⟩
  | _ => none

private theorem r4_chain : ∀ k, ∀ b e,
    ⟨(0 : ℕ), b, 0, k, e⟩ [fm]⊢* ⟨0, b + k, 0, 0, e⟩ := by
  intro k; induction' k with k ih <;> intro b e
  · ring_nf; finish
  · rw [show b + (k + 1) = (b + 1) + k from by ring]
    step fm; exact ih (b + 1) e

private theorem r2_chain : ∀ k, ∀ a c d e,
    ⟨a, (0 : ℕ), c + k, d, e + k⟩ [fm]⊢* ⟨a + 2 * k, 0, c, d + 2 * k, e⟩ := by
  intro k; induction' k with k ih <;> intro a c d e
  · ring_nf; finish
  · rw [show c + (k + 1) = (c + k) + 1 from by ring,
        show e + (k + 1) = (e + k) + 1 from by ring,
        show a + 2 * (k + 1) = (a + 2) + 2 * k from by ring,
        show d + 2 * (k + 1) = (d + 2) + 2 * k from by ring]
    step fm; exact ih (a + 2) c (d + 2) e

private theorem r3_chain : ∀ k, ∀ d e,
    ⟨k, (0 : ℕ), 0, d, e⟩ [fm]⊢* ⟨0, 0, 0, d + k, e + 2 * k⟩ := by
  intro k; induction' k with k ih <;> intro d e
  · ring_nf; finish
  · rw [show d + (k + 1) = (d + 1) + k from by ring,
        show e + 2 * (k + 1) = (e + 2) + 2 * k from by ring]
    step fm; exact ih (d + 1) (e + 2)

private theorem r2r1r1_chain : ∀ k, ∀ b c d e,
    ⟨(0 : ℕ), b + 2 * k, c + 1, d, e + k⟩ [fm]⊢* ⟨0, b, c + k + 1, d + 2 * k, e⟩ := by
  intro k; induction' k with k ih <;> intro b c d e
  · ring_nf; finish
  · rw [show b + 2 * (k + 1) = (b + 2 * k) + 2 from by ring,
        show e + (k + 1) = (e + k) + 1 from by ring,
        show c + (k + 1) + 1 = (c + 1) + k + 1 from by ring,
        show d + 2 * (k + 1) = (d + 2) + 2 * k from by ring]
    step fm; step fm; step fm
    exact ih b (c + 1) (d + 2) e

private theorem r3r2r2_chain : ∀ k, ∀ a c d,
    ⟨a + 1, (0 : ℕ), c + 2 * k, d, 0⟩ [fm]⊢* ⟨a + 3 * k + 1, 0, c, d + 5 * k, 0⟩ := by
  intro k; induction' k with k ih <;> intro a c d
  · ring_nf; finish
  · rw [show c + 2 * (k + 1) = (c + 2 * k) + 2 from by ring,
        show a + 3 * (k + 1) + 1 = (a + 3) + 3 * k + 1 from by ring,
        show d + 5 * (k + 1) = (d + 5) + 5 * k from by ring]
    step fm; step fm; step fm
    exact ih (a + 3) c (d + 5)

private theorem drain_c1 : ∀ a d,
    ⟨a + 1, (0 : ℕ), 1, d, 0⟩ [fm]⊢* ⟨0, 0, 0, d + a + 5, 2 * a + 5⟩ := by
  intro a d; step fm; step fm
  have h := r3_chain (a + 2) (d + 3) 1
  rw [show (d + 3) + (a + 2) = d + a + 5 from by ring,
      show 1 + 2 * (a + 2) = 2 * a + 5 from by ring] at h; exact h

private theorem drain_even : ∀ k, ∀ a d,
    ⟨a + 1, (0 : ℕ), 2 * k, d, 0⟩ [fm]⊢* ⟨0, 0, 0, d + 8 * k + a + 1, 2 * a + 6 * k + 2⟩ := by
  intro k a d
  have h1 := r3r2r2_chain k a 0 d
  rw [show 0 + 2 * k = 2 * k from by ring] at h1
  apply stepStar_trans h1
  have h2 := r3_chain (a + 3 * k + 1) (d + 5 * k) 0
  rw [show (d + 5 * k) + (a + 3 * k + 1) = d + 8 * k + a + 1 from by ring,
      show 0 + 2 * (a + 3 * k + 1) = 2 * a + 6 * k + 2 from by ring] at h2; exact h2

private theorem drain_odd : ∀ k, ∀ a d,
    ⟨a + 1, (0 : ℕ), 2 * k + 1, d, 0⟩ [fm]⊢* ⟨0, 0, 0, d + 8 * k + a + 5, 2 * a + 6 * k + 5⟩ := by
  intro k a d
  have h1 := r3r2r2_chain k a 1 d
  rw [show 1 + 2 * k = 2 * k + 1 from by ring] at h1
  apply stepStar_trans h1
  have h2 := drain_c1 (a + 3 * k) (d + 5 * k)
  rw [show (d + 5 * k) + (a + 3 * k) + 5 = d + 8 * k + a + 5 from by ring,
      show 2 * (a + 3 * k) + 5 = 2 * a + 6 * k + 5 from by ring] at h2; exact h2

private theorem full_drain (a c d : ℕ) :
    ⟨a + 1, (0 : ℕ), c, d, 0⟩ [fm]⊢* ⟨0, 0, 0, d + 4 * c + a + 1, 2 * a + 3 * c + 2⟩ := by
  rcases Nat.even_or_odd c with ⟨K, hK⟩ | ⟨K, hK⟩
  · have h := drain_even K a d
    rw [show 2 * K = c from by omega] at h
    rw [show d + 8 * K + a + 1 = d + 4 * c + a + 1 from by omega,
        show 2 * a + 6 * K + 2 = 2 * a + 3 * c + 2 from by omega] at h; exact h
  · have h := drain_odd K a d
    rw [show 2 * K + 1 = c from by omega] at h
    rw [show d + 8 * K + a + 5 = d + 4 * c + a + 1 from by omega,
        show 2 * a + 6 * K + 5 = 2 * a + 3 * c + 2 from by omega] at h; exact h

-- Odd D=2m+1, E >= 2m+1
private theorem trans_odd_large (m E : ℕ) (hE : E ≥ 2 * m + 1) :
    ⟨(0 : ℕ), 0, 0, 2 * m + 1, E⟩ [fm]⊢⁺ ⟨0, 0, 0, 6 * m + 4, E + 2 * m + 3⟩ := by
  apply stepStar_stepPlus_stepPlus
  · have h := r4_chain (2 * m + 1) 0 E
    rw [show 0 + (2 * m + 1) = 2 * m + 1 from by ring] at h; exact h
  step fm
  apply stepStar_trans
  · have h := r2r1r1_chain m 0 0 0 (E - m)
    rw [show 0 + 2 * m = 2 * m from by ring,
        show 0 + 1 = 1 from by ring,
        show (E - m) + m = E from by omega,
        show 0 + m + 1 = m + 1 from by ring] at h; exact h
  apply stepStar_trans
  · have h := r2_chain (m + 1) 0 0 (2 * m) (E - 2 * m - 1)
    rw [show 0 + (m + 1) = m + 1 from by ring,
        show (E - 2 * m - 1) + (m + 1) = E - m from by omega,
        show 0 + 2 * (m + 1) = 2 * m + 2 from by ring,
        show (2 * m) + 2 * (m + 1) = 4 * m + 2 from by ring] at h; exact h
  have h := r3_chain (2 * m + 2) (4 * m + 2) (E - 2 * m - 1)
  rw [show (4 * m + 2) + (2 * m + 2) = 6 * m + 4 from by ring,
      show (E - 2 * m - 1) + 2 * (2 * m + 2) = E + 2 * m + 3 from by omega] at h; exact h

-- Odd D=2m+1, m+1 <= E < 2m+1
private theorem trans_odd_small (m E : ℕ) (hE1 : E ≥ m + 1) (hE2 : E < 2 * m + 1) :
    ⟨(0 : ℕ), 0, 0, 2 * m + 1, E⟩ [fm]⊢⁺ ⟨0, 0, 0, 6 * m + 4, E + 2 * m + 3⟩ := by
  apply stepStar_stepPlus_stepPlus
  · have h := r4_chain (2 * m + 1) 0 E
    rw [show 0 + (2 * m + 1) = 2 * m + 1 from by ring] at h; exact h
  step fm
  apply stepStar_trans
  · have h := r2r1r1_chain m 0 0 0 (E - m)
    rw [show 0 + 2 * m = 2 * m from by ring,
        show 0 + 1 = 1 from by ring,
        show (E - m) + m = E from by omega,
        show 0 + m + 1 = m + 1 from by ring] at h; exact h
  -- (0, 0, m+1, 2m, E-m). Partial R2: drain E-m < m+1 steps.
  -- r2_chain(E-m, 0, 2m+1-E, 2m, 0): (0, 0, (2m+1-E)+(E-m), 2m, 0+(E-m)) -> (2(E-m), 0, 2m+1-E, 2m+2(E-m), 0)
  apply stepStar_trans
  · have h := r2_chain (E - m) 0 (2 * m + 1 - E) (2 * m) 0
    rw [show (2 * m + 1 - E) + (E - m) = m + 1 from by omega,
        show 0 + (E - m) = E - m from by ring,
        show 0 + 2 * (E - m) = 2 * (E - m) from by ring,
        show (2 * m) + 2 * (E - m) = 2 * E from by omega] at h; exact h
  -- (2(E-m), 0, 2m+1-E, 2E, 0). full_drain.
  have h := full_drain (2 * (E - m) - 1) (2 * m + 1 - E) (2 * E)
  rw [show 2 * (E - m) - 1 + 1 = 2 * (E - m) from by omega,
      show 2 * E + 4 * (2 * m + 1 - E) + (2 * (E - m) - 1) + 1 = 6 * m + 4 from by omega,
      show 2 * (2 * (E - m) - 1) + 3 * (2 * m + 1 - E) + 2 = E + 2 * m + 3 from by omega] at h
  exact h

-- Even D=2(m+1), E >= 2(m+1)
private theorem trans_even_large (m E : ℕ) (hE : E ≥ 2 * m + 2) :
    ⟨(0 : ℕ), 0, 0, 2 * m + 2, E⟩ [fm]⊢⁺ ⟨0, 0, 0, 6 * m + 7, E + 2 * m + 4⟩ := by
  apply stepStar_stepPlus_stepPlus
  · have h := r4_chain (2 * m + 2) 0 E
    rw [show 0 + (2 * m + 2) = 2 * m + 2 from by ring] at h; exact h
  step fm
  apply stepStar_trans
  · have h := r2r1r1_chain m 1 0 0 (E - m)
    rw [show 1 + 2 * m = 2 * m + 1 from by ring,
        show 0 + 1 = 1 from by ring,
        show (E - m) + m = E from by omega,
        show 0 + m + 1 = m + 1 from by ring] at h; exact h
  -- (0, 1, m+1, 2m, E-m). R2+R1.
  rw [show E - m = (E - m - 1) + 1 from by omega]
  step fm; step fm
  -- (1, 0, m+1, 2m+2, E-m-1). R2 chain: drain m+1.
  rw [show (0 : ℕ) + 2 * m + 2 = 2 * m + 2 from by ring]
  apply stepStar_trans
  · have h := r2_chain (m + 1) 1 0 (2 * m + 2) (E - 2 * m - 2)
    rw [show 0 + (m + 1) = m + 1 from by ring,
        show (E - 2 * m - 2) + (m + 1) = E - m - 1 from by omega,
        show 1 + 2 * (m + 1) = 2 * m + 3 from by ring,
        show (2 * m + 2) + 2 * (m + 1) = 4 * m + 4 from by ring] at h; exact h
  have h := r3_chain (2 * m + 3) (4 * m + 4) (E - 2 * m - 2)
  rw [show (4 * m + 4) + (2 * m + 3) = 6 * m + 7 from by ring,
      show (E - 2 * m - 2) + 2 * (2 * m + 3) = E + 2 * m + 4 from by omega] at h; exact h

-- Even D=2(m+1), m+2 <= E < 2(m+1)
private theorem trans_even_small (m E : ℕ) (hE1 : E ≥ m + 2) (hE2 : E < 2 * m + 2) :
    ⟨(0 : ℕ), 0, 0, 2 * m + 2, E⟩ [fm]⊢⁺ ⟨0, 0, 0, 6 * m + 7, E + 2 * m + 4⟩ := by
  apply stepStar_stepPlus_stepPlus
  · have h := r4_chain (2 * m + 2) 0 E
    rw [show 0 + (2 * m + 2) = 2 * m + 2 from by ring] at h; exact h
  step fm
  apply stepStar_trans
  · have h := r2r1r1_chain m 1 0 0 (E - m)
    rw [show 1 + 2 * m = 2 * m + 1 from by ring,
        show 0 + 1 = 1 from by ring,
        show (E - m) + m = E from by omega,
        show 0 + m + 1 = m + 1 from by ring] at h; exact h
  rw [show E - m = (E - m - 1) + 1 from by omega]
  step fm; step fm
  -- (1, 0, m+1, 2m+2, E-m-1). Partial R2: drain E-m-1 steps.
  rw [show (0 : ℕ) + 2 * m + 2 = 2 * m + 2 from by ring]
  apply stepStar_trans
  · have h := r2_chain (E - m - 1) 1 (2 * m + 2 - E) (2 * m + 2) 0
    rw [show (2 * m + 2 - E) + (E - m - 1) = m + 1 from by omega,
        show 0 + (E - m - 1) = E - m - 1 from by ring,
        show 1 + 2 * (E - m - 1) = 2 * E - 2 * m - 1 from by omega,
        show (2 * m + 2) + 2 * (E - m - 1) = 2 * E from by omega] at h; exact h
  -- (2E-2m-1, 0, 2m+2-E, 2E, 0). full_drain.
  have h := full_drain (2 * E - 2 * m - 2) (2 * m + 2 - E) (2 * E)
  rw [show 2 * E - 2 * m - 2 + 1 = 2 * E - 2 * m - 1 from by omega,
      show 2 * E + 4 * (2 * m + 2 - E) + (2 * E - 2 * m - 2) + 1 = 6 * m + 7 from by omega,
      show 2 * (2 * E - 2 * m - 2) + 3 * (2 * m + 2 - E) + 2 = E + 2 * m + 4 from by omega] at h
  exact h

-- Combined transition
private theorem main_trans (d e : ℕ) (hd : d ≥ 1) (he : 2 * e ≥ d + 1) :
    ⟨(0 : ℕ), 0, 0, d, e⟩ [fm]⊢⁺ ⟨0, 0, 0, 3 * d + 1, e + d + 2⟩ := by
  rcases Nat.even_or_odd d with ⟨m, hm⟩ | ⟨m, hm⟩
  · rcases m with _ | m
    · omega
    · subst hm
      have hd2 : m + 1 + (m + 1) = 2 * m + 2 := by omega
      rw [hd2]
      rw [show 3 * (2 * m + 2) + 1 = 6 * m + 7 from by ring,
          show e + (2 * m + 2) + 2 = e + 2 * m + 4 from by ring]
      rcases Nat.lt_or_ge e (2 * (m + 1)) with h | h
      · exact trans_even_small m e (by omega) (by omega)
      · exact trans_even_large m e (by omega)
  · subst hm
    rcases Nat.lt_or_ge e (2 * m + 1) with h | h
    · have ht := trans_odd_small m e (by omega) (by omega)
      rw [show 3 * (2 * m + 1) + 1 = 6 * m + 4 from by ring,
          show e + (2 * m + 1) + 2 = e + 2 * m + 3 from by ring]; exact ht
    · have ht := trans_odd_large m e (by omega)
      rw [show 3 * (2 * m + 1) + 1 = 6 * m + 4 from by ring,
          show e + (2 * m + 1) + 2 = e + 2 * m + 3 from by ring]; exact ht

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨0, 0, 0, 1, 2⟩) (by execute fm 1)
  apply progress_nonhalt (fm := fm)
    (P := fun q ↦ ∃ d e, q = ⟨0, 0, 0, d + 1, e + 1⟩ ∧ 2 * (e + 1) ≥ (d + 1) + 1)
  · intro q ⟨d, e, hq, hinv⟩; subst hq
    refine ⟨⟨0, 0, 0, 3 * (d + 1) + 1, (e + 1) + (d + 1) + 2⟩,
            ⟨3 * d + 3, e + d + 3, by ring_nf, by omega⟩, ?_⟩
    exact main_trans (d + 1) (e + 1) (by omega) (by omega)
  · exact ⟨0, 1, rfl, by omega⟩

end Sz22_2003_unofficial_1083
