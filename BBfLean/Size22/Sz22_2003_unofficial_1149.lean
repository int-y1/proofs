import BBfLean.FM
import Mathlib.Tactic.Ring


/-!
# sz22_2003_unofficial #1149: [5/6, 44/35, 5929/2, 3/11, 2/3]

This Fractran program doesn't halt.
-/

namespace Sz22_2003_unofficial_1149

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a+1, b+1, c, d, e⟩ => some ⟨a, b, c+1, d, e⟩
  | ⟨a, b, c+1, d+1, e⟩ => some ⟨a+2, b, c, d, e+1⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b, c, d+2, e+2⟩
  | ⟨a, b, c, d, e+1⟩ => some ⟨a, b+1, c, d, e⟩
  | ⟨a, b+1, c, d, e⟩ => some ⟨a+1, b, c, d, e⟩
  | _ => none

theorem e_to_b : ∀ k b d e, ⟨0, b, 0, d, e + k⟩ [fm]⊢* ⟨0, b + k, 0, d, e⟩ := by
  intro k; induction' k with k ih <;> intro b d e
  · exists 0
  · rw [show e + (k + 1) = (e + k) + 1 from by ring]; step fm
    apply stepStar_trans (ih (b + 1) d e); ring_nf; finish

theorem r3_drain : ∀ k a d e, ⟨a + k, 0, 0, d, e⟩ [fm]⊢* ⟨a, 0, 0, d + 2 * k, e + 2 * k⟩ := by
  intro k; induction' k with k ih <;> intro a d e
  · exists 0
  · rw [show a + (k + 1) = (a + k) + 1 from by ring]; step fm
    apply stepStar_trans (ih a (d + 2) (e + 2)); ring_nf; finish

theorem r2_chain : ∀ k a c d e, ⟨a, 0, c + k, d + k, e⟩ [fm]⊢* ⟨a + 2 * k, 0, c, d, e + k⟩ := by
  intro k; induction' k with k ih <;> intro a c d e
  · exists 0
  · rw [show c + (k + 1) = (c + k) + 1 from by ring,
        show d + (k + 1) = (d + k) + 1 from by ring]; step fm
    apply stepStar_trans (ih (a + 2) c d (e + 1)); ring_nf; finish

theorem interleaved_a2 : ∀ k r, r ≤ 1 → ∀ C D E,
    ⟨2, 2 * k + r, C, D + k, E⟩ [fm]⊢* ⟨2, r, C + k, D, E + k⟩ := by
  intro k; induction' k with k ih <;> intro r hr C D E
  · simp; exists 0
  · rw [show 2 * (k + 1) + r = (2 * k + r) + 1 + 1 from by ring,
        show D + (k + 1) = (D + k) + 1 from by ring]
    step fm; step fm; step fm
    apply stepStar_trans (ih r hr (C + 1) D (E + 1)); ring_nf; finish

theorem r3_r2_even : ∀ k a e, ⟨a + 1, 0, 2 * k, 0, e⟩ [fm]⊢*
    ⟨a + 1 + 3 * k, 0, 0, 0, e + 4 * k⟩ := by
  intro k; induction' k with k ih <;> intro a e
  · exists 0
  · rw [show 2 * (k + 1) = (2 * k) + 1 + 1 from by ring]
    step fm; step fm; step fm
    rw [show a + 1 + 1 + 2 = (a + 3) + 1 from by ring,
        show e + 2 + 1 + 1 = e + 4 from by ring]
    apply stepStar_trans (ih (a + 3) (e + 4)); ring_nf; finish

theorem r3_r2_odd : ∀ k a e, ⟨a + 1, 0, 2 * k + 1, 0, e⟩ [fm]⊢*
    ⟨a + 2 + 3 * k, 0, 0, 1, e + 4 * k + 3⟩ := by
  intro k; induction' k with k ih <;> intro a e
  · step fm; step fm; finish
  · rw [show 2 * (k + 1) + 1 = (2 * k + 1) + 1 + 1 from by ring]
    step fm; step fm; step fm
    rw [show a + 1 + 1 + 2 = (a + 3) + 1 from by ring,
        show e + 2 + 1 + 1 = e + 4 from by ring]
    apply stepStar_trans (ih (a + 3) (e + 4)); ring_nf; finish

theorem setup (d e : ℕ) :
    ⟨0, 0, 0, d + 2, e + 2⟩ [fm]⊢* ⟨2, e, 0, d + 1, 1⟩ := by
  rw [show e + 2 = 0 + (e + 2) from by ring]
  apply stepStar_trans (e_to_b (e + 2) 0 (d + 2) 0)
  rw [show 0 + (e + 2) = e + 2 from by ring]
  step fm; step fm; step fm; finish

private theorem reentry_even_clean (m d : ℕ) (hd : d + 1 ≥ 2 * m) :
    ⟨2, 2 * m, 0, d + 1, 1⟩ [fm]⊢* ⟨1, 0, 0, d + 2 * m + 3, 6 * m + 3⟩ := by
  have h1 := interleaved_a2 m 0 (by omega) 0 (d + 1 - m) 1
  rw [show (2 : ℕ) * m + 0 = 2 * m from by ring,
      show d + 1 - m + m = d + 1 from by omega] at h1
  apply stepStar_trans h1; clear h1
  have h2 := r2_chain m 2 0 (d + 1 - 2 * m) (1 + m)
  rw [show d + 1 - 2 * m + m = d + 1 - m from by omega] at h2
  apply stepStar_trans h2; clear h2
  rw [show (2 : ℕ) + 2 * m = 1 + (2 * m + 1) from by ring]
  apply stepStar_trans (r3_drain (2 * m + 1) 1 (d + 1 - 2 * m) (1 + m + m))
  rw [show d + 1 - 2 * m + 2 * (2 * m + 1) = d + 2 * m + 3 from by omega,
      show 1 + m + m + 2 * (2 * m + 1) = 6 * m + 3 from by omega]
  finish

private theorem reentry_even_res (m d : ℕ) (hm : m ≤ d + 1) (hd : d + 1 < 2 * m) :
    ⟨2, 2 * m, 0, d + 1, 1⟩ [fm]⊢* ⟨1, 0, 0, d + 2 * m + 3, 6 * m + 3⟩ := by
  have h1 := interleaved_a2 m 0 (by omega) 0 (d + 1 - m) 1
  rw [show (2 : ℕ) * m + 0 = 2 * m from by ring,
      show d + 1 - m + m = d + 1 from by omega] at h1
  apply stepStar_trans h1; clear h1
  have h2 := r2_chain (d + 1 - m) 2 (m - (d + 1 - m)) 0 (1 + m)
  rw [show m - (d + 1 - m) + (d + 1 - m) = 0 + m from by omega,
      show 0 + (d + 1 - m) = d + 1 - m from by omega] at h2
  apply stepStar_trans h2; clear h2
  set j := d + 1 - m
  set C := m - j
  rcases Nat.even_or_odd C with ⟨k, hk⟩ | ⟨k, hk⟩
  · rw [hk, show k + k = 2 * k from by ring,
        show 2 + 2 * j = (2 * j + 1) + 1 from by ring]
    apply stepStar_trans (r3_r2_even k (2 * j + 1) (1 + m + j))
    rw [show 2 * j + 1 + 1 + 3 * k = 1 + (2 * j + 3 * k + 1) from by ring]
    apply stepStar_trans (r3_drain (2 * j + 3 * k + 1) 1 0 (1 + m + j + 4 * k))
    rw [show 0 + 2 * (2 * j + 3 * k + 1) = d + 2 * m + 3 from by omega,
        show 1 + m + j + 4 * k + 2 * (2 * j + 3 * k + 1) = 6 * m + 3 from by omega]
    finish
  · rw [hk, show 2 + 2 * j = (2 * j + 1) + 1 from by ring]
    apply stepStar_trans (r3_r2_odd k (2 * j + 1) (1 + m + j))
    rw [show 2 * j + 1 + 1 + 1 + 3 * k = 1 + (2 * j + 3 * k + 2) from by ring]
    apply stepStar_trans (r3_drain (2 * j + 3 * k + 2) 1 1 (1 + m + j + 4 * k + 3))
    rw [show 1 + 2 * (2 * j + 3 * k + 2) = d + 2 * m + 3 from by omega,
        show 1 + m + j + 4 * k + 3 + 2 * (2 * j + 3 * k + 2) = 6 * m + 3 from by omega]
    finish

private theorem reentry_odd_clean (m d : ℕ) (hd : d ≥ 2 * m) :
    ⟨2, 2 * m + 1, 0, d + 1, 1⟩ [fm]⊢* ⟨1, 0, 0, d + 2 * m + 4, 6 * m + 6⟩ := by
  have h1 := interleaved_a2 m 1 (by omega) 0 (d + 1 - m) 1
  rw [show d + 1 - m + m = d + 1 from by omega] at h1
  apply stepStar_trans h1; clear h1
  step fm
  rw [show 0 + m + 1 = 0 + (m + 1) from by ring]
  have h2 := r2_chain (m + 1) 1 0 (d + 1 - m - (m + 1)) (1 + m)
  rw [show d + 1 - m - (m + 1) + (m + 1) = d + 1 - m from by omega] at h2
  apply stepStar_trans h2; clear h2
  rw [show 1 + 2 * (m + 1) = 1 + (2 * m + 2) from by ring]
  apply stepStar_trans (r3_drain (2 * m + 2) 1 (d + 1 - m - (m + 1)) (1 + m + (m + 1)))
  rw [show d + 1 - m - (m + 1) + 2 * (2 * m + 2) = d + 2 * m + 4 from by omega,
      show 1 + m + (m + 1) + 2 * (2 * m + 2) = 6 * m + 6 from by omega]
  finish

private theorem reentry_odd_res (m d : ℕ) (hm : m ≤ d) (hd : d < 2 * m) :
    ⟨2, 2 * m + 1, 0, d + 1, 1⟩ [fm]⊢* ⟨1, 0, 0, d + 2 * m + 4, 6 * m + 6⟩ := by
  have h1 := interleaved_a2 m 1 (by omega) 0 (d + 1 - m) 1
  rw [show d + 1 - m + m = d + 1 from by omega] at h1
  apply stepStar_trans h1; clear h1
  step fm
  rw [show 0 + m + 1 = 0 + (m + 1) from by ring]
  set j := d + 1 - m
  have h2 := r2_chain j 1 (m + 1 - j) 0 (1 + m)
  rw [show m + 1 - j + j = 0 + (m + 1) from by omega,
      show 0 + j = j from by omega] at h2
  apply stepStar_trans h2; clear h2
  set C := m + 1 - j
  rcases Nat.even_or_odd C with ⟨k, hk⟩ | ⟨k, hk⟩
  · rw [hk, show k + k = 2 * k from by ring,
        show 1 + 2 * j = (2 * j) + 1 from by ring]
    apply stepStar_trans (r3_r2_even k (2 * j) (1 + m + j))
    rw [show 2 * j + 1 + 3 * k = 1 + (2 * j + 3 * k) from by ring]
    apply stepStar_trans (r3_drain (2 * j + 3 * k) 1 0 (1 + m + j + 4 * k))
    rw [show 0 + 2 * (2 * j + 3 * k) = d + 2 * m + 4 from by omega,
        show 1 + m + j + 4 * k + 2 * (2 * j + 3 * k) = 6 * m + 6 from by omega]
    finish
  · rw [hk, show 1 + 2 * j = (2 * j) + 1 from by ring]
    apply stepStar_trans (r3_r2_odd k (2 * j) (1 + m + j))
    rw [show 2 * j + 1 + 1 + 3 * k = 1 + (2 * j + 3 * k + 1) from by ring]
    apply stepStar_trans (r3_drain (2 * j + 3 * k + 1) 1 1 (1 + m + j + 4 * k + 3))
    rw [show 1 + 2 * (2 * j + 3 * k + 1) = d + 2 * m + 4 from by omega,
        show 1 + m + j + 4 * k + 3 + 2 * (2 * j + 3 * k + 1) = 6 * m + 6 from by omega]
    finish

theorem reentry (d e : ℕ) (he : e ≤ 2 * d + 2) :
    ⟨0, 0, 0, d + 2, e + 2⟩ [fm]⊢* ⟨1, 0, 0, d + e + 3, 3 * e + 3⟩ := by
  apply stepStar_trans (setup d e)
  rcases Nat.even_or_odd e with ⟨m, hm⟩ | ⟨m, hm⟩
  · subst hm
    -- e = m + m, so goal becomes about 2*m terms
    -- Target: (2, m+m, 0, d+1, 1) ⊢* (1, 0, 0, d+(m+m)+3, 3*(m+m)+3)
    -- Rewrite to match the helper lemma signatures
    rw [show m + m = 2 * m from by ring,
        show 3 * (2 * m) + 3 = 6 * m + 3 from by ring]
    rcases Nat.lt_or_ge (d + 1) (2 * m) with h | h
    · exact reentry_even_res m d (by omega) h
    · exact reentry_even_clean m d h
  · subst hm
    -- e = 2*m+1
    rw [show d + (2 * m + 1) + 3 = d + 2 * m + 4 from by ring,
        show 3 * (2 * m + 1) + 3 = 6 * m + 6 from by ring]
    rcases Nat.lt_or_ge d (2 * m) with h | h
    · exact reentry_odd_res m d (by omega) h
    · exact reentry_odd_clean m d h

theorem cycle (d e : ℕ) (he : e ≤ 2 * d + 2) :
    ⟨1, 0, 0, d, e⟩ [fm]⊢⁺ ⟨1, 0, 0, d + e + 3, 3 * e + 3⟩ := by
  apply step_stepStar_stepPlus (c₂ := ⟨0, 0, 0, d + 2, e + 2⟩)
  · simp [fm]
  · exact reentry d e he

theorem nonhalt : ¬halts fm c₀ := by
  apply progress_nonhalt (fm := fm)
    (P := fun q ↦ ∃ d e, q = ⟨1, 0, 0, d, e⟩ ∧ e ≤ 2 * d + 2)
  · intro c ⟨d, e, hc, he⟩
    subst hc
    exact ⟨⟨1, 0, 0, d + e + 3, 3 * e + 3⟩,
           ⟨d + e + 3, 3 * e + 3, rfl, by omega⟩,
           cycle d e he⟩
  · exact ⟨0, 0, rfl, by omega⟩

end Sz22_2003_unofficial_1149
