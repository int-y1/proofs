import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #841: [36/35, 5/22, 147/2, 11/3, 5/11]

Vector representation:
```
 2  2 -1 -1  0
-1  0  1  0 -1
-1  1  0  2  0
 0 -1  0  0  1
 0  0  1  0 -1
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_841

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a, b, c+1, d+1, e⟩ => some ⟨a+2, b+2, c, d, e⟩
  | ⟨a+1, b, c, d, e+1⟩ => some ⟨a, b, c+1, d, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b+1, c, d+2, e⟩
  | ⟨a, b+1, c, d, e⟩ => some ⟨a, b, c, d, e+1⟩
  | ⟨a, b, c, d, e+1⟩ => some ⟨a, b, c+1, d, e⟩
  | _ => none

theorem b_to_e : ∀ k, ∀ b d e, ⟨0, b + k, 0, d, e⟩ [fm]⊢* ⟨0, b, 0, d, e + k⟩ := by
  intro k; induction' k with k ih <;> intro b d e
  · exists 0
  · rw [show b + (k + 1) = (b + k) + 1 from by ring]
    step fm
    apply stepStar_trans (ih b d (e + 1))
    ring_nf; finish

theorem r3_chain : ∀ k, ∀ a b d, ⟨a + k, b, 0, d, 0⟩ [fm]⊢* ⟨a, b + k, 0, d + 2 * k, 0⟩ := by
  intro k; induction' k with k ih <;> intro a b d
  · exists 0
  · rw [show a + (k + 1) = (a + k) + 1 from by ring]
    step fm
    apply stepStar_trans (ih a (b + 1) (d + 2))
    ring_nf; finish

theorem r2r1_chain : ∀ k, ∀ a b d e, ⟨a + 1, b, 0, d + k, e + k⟩ [fm]⊢* ⟨a + 1 + k, b + 2 * k, 0, d, e⟩ := by
  intro k; induction' k with k ih <;> intro a b d e
  · exists 0
  · rw [show d + (k + 1) = (d + k) + 1 from by ring,
        show e + (k + 1) = (e + k) + 1 from by ring]
    step fm; step fm
    apply stepStar_trans (ih (a + 1) (b + 2) d e)
    ring_nf; finish

theorem r2_drain : ∀ k, ∀ a b c e, ⟨a + k, b, c, 0, e + k⟩ [fm]⊢* ⟨a, b, c + k, 0, e⟩ := by
  intro k; induction' k with k ih <;> intro a b c e
  · exists 0
  · rw [show a + (k + 1) = (a + k) + 1 from by ring,
        show e + (k + 1) = (e + k) + 1 from by ring]
    step fm
    apply stepStar_trans (ih a b (c + 1) e)
    ring_nf; finish

theorem r3r1_process : ∀ p, ∀ q b, ⟨q + 1, b, p, 0, 0⟩ [fm]⊢* ⟨0, b + 4 * p + q + 1, 0, 2 * q + 3 * p + 2, 0⟩ := by
  intro p; induction' p using Nat.strongRecOn with p ih; intro q b
  rcases p with _ | _ | p
  · rw [show q + 1 = 0 + (q + 1) from by ring]
    apply stepStar_trans (r3_chain (q + 1) 0 b 0)
    ring_nf; finish
  · step fm; step fm
    rw [show q + 2 = 0 + (q + 2) from by ring]
    apply stepStar_trans (r3_chain (q + 2) 0 (b + 3) 1)
    ring_nf; finish
  · step fm; step fm; step fm
    apply stepStar_trans (ih p (by omega) (q + 3) (b + 5))
    ring_nf; finish

-- D ≥ E case: with g = D-E, e = E-1, D = g+e+1, E = e+1
theorem main_trans_ge (g e : ℕ) :
    ⟨0, 0, 0, g + e + 1, e + 1⟩ [fm]⊢⁺ ⟨0, 0, 0, g + 2 * e + 4, 3 * e + 4⟩ := by
  step fm; step fm
  -- At (2, 2, 0, g+e, e).
  have h1 : ⟨2, 2, 0, g + e, e⟩ [fm]⊢* ⟨e + 2, 2 * e + 2, 0, g, 0⟩ := by
    have := r2r1_chain e 1 2 g 0
    convert this using 2; ring_nf
  apply stepStar_trans h1
  have h2 : ⟨e + 2, 2 * e + 2, 0, g, 0⟩ [fm]⊢* ⟨0, 3 * e + 4, 0, g + 2 * e + 4, 0⟩ := by
    rw [show e + 2 = 0 + (e + 2) from by ring]
    apply stepStar_trans (r3_chain (e + 2) 0 (2 * e + 2) g)
    ring_nf; finish
  apply stepStar_trans h2
  rw [show 3 * e + 4 = 0 + (3 * e + 4) from by ring]
  apply stepStar_trans (b_to_e (3 * e + 4) 0 (g + 2 * e + 4) 0)
  ring_nf; finish

-- D < E case: parameterized by g = D-E (gap from D to E), e = excess of E over D
-- D = g+e+2, E = g+2*e+3, with g = d-e, so d = g+e
theorem main_trans_lt (g e : ℕ) :
    ⟨0, 0, 0, g + e + 2, g + 2 * e + 3⟩ [fm]⊢⁺ ⟨0, 0, 0, 2 * g + 3 * e + 7, 3 * g + 6 * e + 10⟩ := by
  step fm; step fm
  -- At (2, 2, 0, g+e+1, g+2*e+2).
  have h1 : ⟨2, 2, 0, g + e + 1, g + 2 * e + 2⟩ [fm]⊢* ⟨g + e + 3, 2 * g + 2 * e + 4, 0, 0, e + 1⟩ := by
    have := r2r1_chain (g + e + 1) 1 2 0 (e + 1)
    convert this using 2; ring_nf
  apply stepStar_trans h1
  have h2 : ⟨g + e + 3, 2 * g + 2 * e + 4, 0, 0, e + 1⟩ [fm]⊢* ⟨g + 2, 2 * g + 2 * e + 4, e + 1, 0, 0⟩ := by
    have := r2_drain (e + 1) (g + 2) (2 * g + 2 * e + 4) 0 0
    convert this using 2; ring_nf
  apply stepStar_trans h2
  have h3 : ⟨g + 2, 2 * g + 2 * e + 4, e + 1, 0, 0⟩ [fm]⊢*
      ⟨0, 3 * g + 6 * e + 10, 0, 2 * g + 3 * e + 7, 0⟩ := by
    rw [show g + 2 = (g + 1) + 1 from by ring]
    apply stepStar_trans (r3r1_process (e + 1) (g + 1) (2 * g + 2 * e + 4))
    ring_nf; finish
  apply stepStar_trans h3
  rw [show 3 * g + 6 * e + 10 = 0 + (3 * g + 6 * e + 10) from by ring]
  apply stepStar_trans (b_to_e (3 * g + 6 * e + 10) 0 (2 * g + 3 * e + 7) 0)
  ring_nf; finish

theorem main_trans {D E : ℕ} (hD : D ≥ 2) (hE : E ≥ 1) (hDE : 2 * D ≥ E + 1) :
    ⟨0, 0, 0, D, E⟩ [fm]⊢⁺ ⟨0, 0, 0, D + E + 2, 3 * E + 1⟩ := by
  obtain ⟨e, rfl⟩ : ∃ e, E = e + 1 := ⟨E - 1, by omega⟩
  by_cases h : D ≥ e + 1
  · -- D ≥ E case
    obtain ⟨g, rfl⟩ : ∃ g, D = g + e + 1 := ⟨D - e - 1, by omega⟩
    have key := main_trans_ge g e
    convert key using 2; ring_nf
  · -- D < E case
    push_neg at h
    obtain ⟨ep, rfl⟩ : ∃ ep, e = D + ep := ⟨e - D, by omega⟩
    obtain ⟨g, rfl⟩ : ∃ g, D = g + ep + 2 := ⟨2 * D - (D + ep) - 2, by omega⟩
    have key := main_trans_lt g ep
    convert key using 2; ring_nf

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨0, 0, 0, 2, 1⟩) (by execute fm 2)
  apply progress_nonhalt (fm := fm)
    (P := fun q ↦ ∃ D E, q = ⟨0, 0, 0, D, E⟩ ∧ D ≥ 2 ∧ E ≥ 1 ∧ 2 * D ≥ E + 1)
  · intro c ⟨D, E, hq, hD, hE, hDE⟩; subst hq
    exact ⟨⟨0, 0, 0, D + E + 2, 3 * E + 1⟩,
      ⟨D + E + 2, 3 * E + 1, rfl, by omega, by omega, by omega⟩,
      main_trans hD hE hDE⟩
  · exact ⟨2, 1, rfl, by omega, by omega, by omega⟩

end Sz22_2003_unofficial_841
