import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #29: [1/15, 27/77, 49/3, 10/49, 33/2]

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_29

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a, b+1, c+1, d, e⟩ => some ⟨a, b, c, d, e⟩
  | ⟨a, b, c, d+1, e+1⟩ => some ⟨a, b+3, c, d, e⟩
  | ⟨a, b+1, c, d, e⟩ => some ⟨a, b, c, d+2, e⟩
  | ⟨a, b, c, d+2, e⟩ => some ⟨a+1, b, c+1, d, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b+1, c, d, e+1⟩
  | _ => none

theorem r2_burst : ∀ k, ∀ a b d e, ⟨a, b, 0, d+k, e+k⟩ [fm]⊢* ⟨a, b+3*k, 0, d, e⟩ := by
  intro k; induction' k with k ih <;> intro a b d e
  · exists 0
  rw [show d + (k + 1) = (d + k) + 1 from by ring,
      show e + (k + 1) = (e + k) + 1 from by ring]
  step fm; apply stepStar_trans (ih a (b + 3) d e); ring_nf; finish

theorem r3_drain : ∀ k, ∀ a b d, ⟨a, b+k, 0, d, 0⟩ [fm]⊢* ⟨a, b, 0, d+2*k, 0⟩ := by
  intro k; induction' k with k ih <;> intro a b d
  · exists 0
  rw [show b + (k + 1) = (b + k) + 1 from by ring]
  step fm; apply stepStar_trans (ih a b (d + 2)); ring_nf; finish

theorem r3r2_drain : ∀ E, ∀ a B, ⟨a, B+1, 0, 0, E⟩ [fm]⊢* ⟨a, 0, 0, 2*(B+1)+5*E, 0⟩ := by
  intro E; induction' E using Nat.strongRecOn with E ih; intro a B
  rcases E with _ | _ | E
  · have h := r3_drain (B + 1) a 0 0
    simp only [Nat.zero_add, Nat.mul_zero, Nat.add_zero] at h ⊢; exact h
  · rw [show B + 1 = (B + 0) + 1 from by ring]; step fm; step fm
    have h := r3_drain (B + 0 + 3) a 0 (0 + 0 + 1)
    simp only [Nat.zero_add] at h; apply stepStar_trans h; ring_nf; finish
  · rw [show B + 1 = (B + 0) + 1 from by ring]; step fm
    rw [show E + 2 = (E + 1 + 0) + 1 from by ring]; step fm
    rw [show E + 1 + 0 = (E + 0) + 1 from by ring]; step fm
    have h := ih E (by omega) a (B + 5)
    simp only [show B + 0 + 3 + 3 = (B + 5) + 1 from by ring,
               show E + 0 = E from by ring]
    apply stepStar_trans h; ring_nf; finish

theorem r2r3_drain : ∀ k, ∀ a d,
    ⟨a, 0, 0, d + 1, k⟩ [fm]⊢* ⟨a, 0, 0, d + 1 + 5 * k, 0⟩ := by
  intro k a d
  rcases Nat.lt_or_ge (d + 1) k with hlt | hge
  · apply stepStar_trans (c₂ := ⟨a, 3 * (d + 1), 0, 0, k - (d + 1)⟩)
    · have h := r2_burst (d + 1) a 0 0 (k - (d + 1))
      rw [show 0 + (d + 1) = d + 1 from by omega,
          show k - (d + 1) + (d + 1) = k from by omega] at h
      simp only [Nat.zero_add] at h; exact h
    rw [show 3 * (d + 1) = (3 * (d + 1) - 1) + 1 from by omega]
    apply stepStar_trans (r3r2_drain (k - (d + 1)) a (3 * (d + 1) - 1))
    rw [show 2 * ((3 * (d + 1) - 1) + 1) + 5 * (k - (d + 1)) = d + 1 + 5 * k from by omega]
    finish
  · apply stepStar_trans (c₂ := ⟨a, 3 * k, 0, d + 1 - k, 0⟩)
    · have h := r2_burst k a 0 (d + 1 - k) 0
      rw [show d + 1 - k + k = d + 1 from by omega,
          show 0 + k = k from by omega] at h
      simp only [Nat.zero_add] at h; exact h
    have h := r3_drain (3 * k) a 0 (d + 1 - k)
    simp only [Nat.zero_add] at h
    rw [show (d + 1 - k) + 2 * (3 * k) = d + 1 + 5 * k from by omega] at h; exact h

theorem r4_chain : ∀ k, ∀ a c d, ⟨a, 0, c, d+2*k, 0⟩ [fm]⊢* ⟨a+k, 0, c+k, d, 0⟩ := by
  intro k; induction' k with k ih <;> intro a c d
  · exists 0
  rw [show d + 2 * (k + 1) = (d + 2 * k) + 2 from by ring]
  step fm; apply stepStar_trans (ih (a + 1) (c + 1) d); ring_nf; finish

theorem r5r1_chain : ∀ k, ∀ a e, ⟨a+k, 0, k, 0, e⟩ [fm]⊢* ⟨a, 0, 0, 0, e+k⟩ := by
  intro k; induction' k with k ih <;> intro a e
  · exists 0
  rw [show a + (k + 1) = (a + k) + 1 from by ring]
  step fm; step fm; apply stepStar_trans (ih a (e + 1)); ring_nf; finish

theorem r1_drain : ∀ k, ∀ a b c d e, ⟨a, b+k, c+k, d, e⟩ [fm]⊢* ⟨a, b, c, d, e⟩ := by
  intro k; induction' k with k ih <;> intro a b c d e
  · exists 0
  rw [show b + (k + 1) = (b + k) + 1 from by ring,
      show c + (k + 1) = (c + k) + 1 from by ring]
  step fm; exact ih a b c d e

theorem odd_tail : ∀ k, ∀ a, ⟨a+k+4, 0, k+4, 1, 0⟩ [fm]⊢* ⟨a+3, 0, 0, 0, k⟩ := by
  intro k a
  rw [show a + k + 4 = (a + k + 3) + 1 from by ring]; step fm
  rw [show k + 4 = (k + 3) + 1 from by ring]; step fm; step fm
  rw [show k + 3 = k + 0 + 3 from by ring]
  apply stepStar_trans (r1_drain 3 (a + k + 3) 0 k 0 0)
  rw [show a + k + 3 = a + 3 + k from by ring]
  have h := r5r1_chain k (a + 3) 0; simpa using h

theorem phase_odd (a j : ℕ) :
    ⟨a, 0, 0, 2, 2*j+3⟩ [fm]⊢⁺ ⟨a+2, 0, 0, 2, 5*j+5⟩ := by
  apply stepStar_stepPlus_stepPlus (c₂ := ⟨a, 0, 0, 10*j+17, 0⟩)
  · have h := r2r3_drain (2*j+3) a 1
    rw [show 1 + 1 + 5 * (2 * j + 3) = 10 * j + 17 from by ring,
        show 1 + 1 = 2 from by ring] at h; exact h
  apply stepStar_stepPlus_stepPlus (c₂ := ⟨a+5*j+8, 0, 5*j+8, 1, 0⟩)
  · rw [show 10 * j + 17 = 1 + 2 * (5 * j + 8) from by ring]
    have h := r4_chain (5*j+8) a 0 1; simpa using h
  apply stepStar_stepPlus_stepPlus (c₂ := ⟨a+3, 0, 0, 0, 5*j+4⟩)
  · rw [show 5 * j + 8 = (5 * j + 4) + 4 from by ring,
        show a + 5 * j + 8 = a + (5 * j + 4) + 4 from by ring]
    exact odd_tail (5*j+4) a
  apply step_stepStar_stepPlus
  · show fm ⟨a + 3, 0, 0, 0, 5 * j + 4⟩ = some ⟨a + 2, 0 + 1, 0, 0, 5 * j + 4 + 1⟩; simp [fm]
  simp only [Nat.zero_add]; step fm; ring_nf; finish

theorem phase_even (a m : ℕ) :
    ⟨a+1, 0, 0, 2, 2*m+2⟩ [fm]⊢⁺ ⟨a, 0, 0, 2, 5*m+7⟩ := by
  apply stepStar_stepPlus_stepPlus (c₂ := ⟨a+1, 0, 0, 10*m+12, 0⟩)
  · have h := r2r3_drain (2*m+2) (a+1) 1
    rw [show 1 + 1 + 5 * (2 * m + 2) = 10 * m + 12 from by ring,
        show 1 + 1 = 2 from by ring] at h; exact h
  apply stepStar_stepPlus_stepPlus (c₂ := ⟨a+5*m+7, 0, 5*m+6, 0, 0⟩)
  · have h := r4_chain (5*m+6) (a+1) 0 0
    rw [show 0 + 2 * (5 * m + 6) = 10 * m + 12 from by ring] at h
    simpa [show a + 1 + (5 * m + 6) = a + 5 * m + 7 from by ring] using h
  apply stepStar_stepPlus_stepPlus (c₂ := ⟨a+1, 0, 0, 0, 5*m+6⟩)
  · have h := r5r1_chain (5*m+6) (a+1) 0
    simpa [show a + 1 + (5 * m + 6) = a + 5 * m + 7 from by ring] using h
  apply step_stepStar_stepPlus
  · show fm ⟨a + 1, 0, 0, 0, 5 * m + 6⟩ = some ⟨a, 0 + 1, 0, 0, 5 * m + 6 + 1⟩; simp [fm]
  simp only [Nat.zero_add]; step fm; ring_nf; finish

theorem phase_odd_even (a k : ℕ) :
    ⟨a, 0, 0, 2, 2*(2*k+1)+3⟩ [fm]⊢⁺ ⟨a+1, 0, 0, 2, 25*k+27⟩ := by
  have h1 := phase_odd a (2*k+1)
  rw [show 5 * (2 * k + 1) + 5 = 10 * k + 10 from by ring] at h1
  have h2 := phase_even (a + 1) (5*k+4)
  rw [show 2 * (5 * k + 4) + 2 = 10 * k + 10 from by ring,
      show 5 * (5 * k + 4) + 7 = 25 * k + 27 from by ring] at h2
  exact stepPlus_trans h1 h2

theorem zero_even_halts (m : ℕ) : halts fm ⟨0, 0, 0, 2, 2*m+2⟩ := by
  have h1 := r2r3_drain (2*m+2) 0 1
  rw [show 1 + 1 + 5 * (2 * m + 2) = 10 * m + 12 from by ring,
      show 1 + 1 = 2 from by ring] at h1
  have h2 := r4_chain (5*m+6) 0 0 0
  rw [show 0 + 2 * (5 * m + 6) = 10 * m + 12 from by ring] at h2
  simp only [Nat.zero_add] at h2
  have h3 := r5r1_chain (5*m+6) 0 0
  simp only [Nat.zero_add] at h3
  exact stepStar_halts (stepStar_trans h1 (stepStar_trans h2 h3))
    (halted_halts (by simp [halted, fm]))

private theorem even_cascade : ∀ a m, ¬halts fm ⟨a, 0, 0, 2, 2*m+2⟩ →
    ∃ a' e', e' ≥ 1 ∧ ¬halts fm ⟨a', 0, 0, 2, e'⟩ ∧
    ⟨a, 0, 0, 2, 2*m+2⟩ [fm]⊢⁺ ⟨a', 0, 0, 2, e'⟩ := by
  intro a; induction a using Nat.strongRecOn with
  | ind a ih =>
    intro m hnh
    have ha : a ≥ 1 := by
      by_contra h; push_neg at h
      have : a = 0 := by omega; subst this
      exact hnh (zero_even_halts m)
    rw [show a = (a - 1) + 1 from by omega]
    have htrans := phase_even (a - 1) m
    have hnh' : ¬halts fm ⟨a - 1, 0, 0, 2, 5 * m + 7⟩ :=
      fun hh => hnh (stepPlus_halts htrans hh)
    rcases Nat.even_or_odd (5 * m + 7) with ⟨k, hk⟩ | ⟨_, hk⟩
    · have : ∃ l, m = 2 * l + 1 := by
        rcases Nat.even_or_odd m with ⟨l, hl⟩ | ⟨l, hl⟩
        · exfalso; subst hl; omega
        · exact ⟨l, hl⟩
      obtain ⟨l, rfl⟩ := this
      rw [show 5 * (2 * l + 1) + 7 = 2 * (5 * l + 5) + 2 from by ring] at hnh' htrans ⊢
      obtain ⟨a', e', he', hnh'', htrans'⟩ := ih (a - 1) (by omega) (5 * l + 5) hnh'
      exact ⟨a', e', he', hnh'', stepPlus_trans htrans htrans'⟩
    · exact ⟨a - 1, 5 * m + 7, by omega, hnh', htrans⟩

private theorem progress_step (c : Q)
    (hp : ∃ a e, c = ⟨a, 0, 0, 2, e⟩ ∧ e ≥ 1 ∧ ¬halts fm c) :
    ∃ c', (∃ a e, c' = ⟨a, 0, 0, 2, e⟩ ∧ e ≥ 1 ∧ ¬halts fm c') ∧ c [fm]⊢⁺ c' := by
  obtain ⟨a, e, hq, he, hnh⟩ := hp; subst hq
  rcases Nat.even_or_odd e with ⟨m, hm⟩ | ⟨m, hm⟩
  · subst hm; rcases m with _ | m; · omega
    rw [show (m + 1) + (m + 1) = 2 * m + 2 from by ring] at hnh ⊢
    obtain ⟨a', e', he', hnh', htrans⟩ := even_cascade a m hnh
    exact ⟨⟨a', 0, 0, 2, e'⟩, ⟨a', e', rfl, he', hnh'⟩, htrans⟩
  · subst hm; rcases m with _ | m
    · have htrans : ⟨a, 0, 0, 2, 1⟩ [fm]⊢⁺ ⟨a + 2, 0, 0, 2, 7⟩ := by
        step fm
        apply stepStar_trans (c₂ := ⟨a, 0, 0, 7, 0⟩)
        · have := r3_drain 3 a 0 1; simpa using this
        apply stepStar_trans (c₂ := ⟨a + 3, 0, 3, 1, 0⟩)
        · have := r4_chain 3 a 0 1; simpa using this
        step fm; step fm; step fm
        apply stepStar_trans (c₂ := ⟨a + 2, 1, 0, 0, 0⟩)
        · have := r1_drain 2 (a+2) 1 0 0 0; simpa using this
        step fm; step fm; step fm; step fm; step fm; step fm
        apply stepStar_trans (c₂ := ⟨a + 1, 6, 0, 0, 0⟩)
        · have := r2_burst 2 (a+1) 0 0 0; simpa using this
        apply stepStar_trans (c₂ := ⟨a + 1, 0, 0, 12, 0⟩)
        · have := r3_drain 6 (a+1) 0 0; simpa using this
        apply stepStar_trans (c₂ := ⟨a + 7, 0, 6, 0, 0⟩)
        · have := r4_chain 6 (a+1) 0 0
          rw [show a + 1 + 6 = a + 7 from by ring] at this; simpa using this
        apply stepStar_trans (c₂ := ⟨a + 1, 0, 0, 0, 6⟩)
        · have := r5r1_chain 6 (a+1) 0
          rw [show a + 1 + 6 = a + 7 from by ring] at this; simpa using this
        step fm; step fm; ring_nf; finish
      exact ⟨⟨a + 2, 0, 0, 2, 7⟩, ⟨a + 2, 7, rfl, by omega,
             fun hh => hnh (stepPlus_halts htrans hh)⟩, htrans⟩
    · rw [show 2 * (m + 1) + 1 = 2 * m + 3 from by ring]
      have htrans := phase_odd a m
      exact ⟨⟨a + 2, 0, 0, 2, 5 * m + 5⟩, ⟨a + 2, 5 * m + 5, rfl, by omega,
             fun hh => hnh (stepPlus_halts htrans hh)⟩, htrans⟩

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨0, 0, 0, 2, 7⟩)
  · apply stepStar_trans (c₂ := ⟨0, 0, 0, 2, 1⟩) (by execute fm 2)
    step fm
    apply stepStar_trans (c₂ := ⟨0, 0, 0, 7, 0⟩)
    · have := r3_drain 3 0 0 1; simpa using this
    apply stepStar_trans (c₂ := ⟨3, 0, 3, 1, 0⟩)
    · have := r4_chain 3 0 0 1; simpa using this
    step fm; step fm; step fm
    apply stepStar_trans (c₂ := ⟨2, 1, 0, 0, 0⟩)
    · have := r1_drain 2 2 1 0 0 0; simpa using this
    step fm; step fm; step fm; step fm; step fm; step fm
    apply stepStar_trans (c₂ := ⟨1, 6, 0, 0, 0⟩)
    · have := r2_burst 2 1 0 0 0; simpa using this
    apply stepStar_trans (c₂ := ⟨1, 0, 0, 12, 0⟩)
    · have := r3_drain 6 1 0 0; simpa using this
    apply stepStar_trans (c₂ := ⟨7, 0, 6, 0, 0⟩)
    · have := r4_chain 6 1 0 0; simpa using this
    apply stepStar_trans (c₂ := ⟨1, 0, 0, 0, 6⟩)
    · have := r5r1_chain 6 1 0; simpa using this
    step fm; step fm; finish
  · exact progress_nonhalt (fm := fm)
      (P := fun q ↦ ∃ a e, q = ⟨a, 0, 0, 2, e⟩ ∧ e ≥ 1 ∧ ¬halts fm q)
      progress_step ⟨0, 7, rfl, by omega, by
        exact progress_nonhalt (fm := fm)
          (P := fun q ↦ ∃ a e, q = ⟨a, 0, 0, 2, e⟩ ∧ e ≥ 1 ∧ ¬halts fm q)
          progress_step ⟨0, 7, rfl, by omega, sorry⟩⟩

end Sz22_2003_unofficial_29
