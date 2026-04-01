import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #1151: [5/6, 44/35, 5929/2, 3/11, 5/3]

Vector representation:
```
-1 -1  1  0  0
 2  0 -1 -1  1
-1  0  0  2  2
 0  1  0  0 -1
 0 -1  1  0  0
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_1151

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a+1, b+1, c, d, e⟩ => some ⟨a, b, c+1, d, e⟩
  | ⟨a, b, c+1, d+1, e⟩ => some ⟨a+2, b, c, d, e+1⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b, c, d+2, e+2⟩
  | ⟨a, b, c, d, e+1⟩ => some ⟨a, b+1, c, d, e⟩
  | ⟨a, b+1, c, d, e⟩ => some ⟨a, b, c+1, d, e⟩
  | _ => none

theorem e_to_b : ∀ k b d e, ⟨0, b, 0, d, e + k⟩ [fm]⊢* ⟨0, b + k, 0, d, e⟩ := by
  intro k; induction k with
  | zero => intro b d e; exists 0
  | succ k ih =>
    intro b d e
    rw [show e + (k + 1) = (e + k) + 1 from by ring]
    step fm
    rw [show b + (k + 1) = (b + 1) + k from by ring]
    exact ih (b + 1) d e

theorem r2r1r1_round : ⟨0, b + 2, c + 1, d + 1, e⟩ [fm]⊢* ⟨0, b, c + 2, d, e + 1⟩ := by
  step fm; step fm; step fm; finish

theorem r2r1r1_chain : ∀ k c d e, ⟨0, 2 * k, c + 1, d + k, e⟩ [fm]⊢* ⟨0, 0, c + k + 1, d, e + k⟩ := by
  intro k; induction k with
  | zero => intro c d e; exists 0
  | succ k ih =>
    intro c d e
    rw [show 2 * (k + 1) = 2 * k + 2 from by ring,
        show d + (k + 1) = (d + k) + 1 from by ring]
    show ⟨0, 2 * k + (0 + 2), c + 1, (d + k) + 1, e⟩ [fm]⊢* _
    apply stepStar_trans (r2r1r1_round (b := 2 * k) (c := c) (d := d + k) (e := e))
    rw [show c + (k + 1) + 1 = (c + 1) + k + 1 from by ring,
        show e + (k + 1) = (e + 1) + k from by ring]
    exact ih (c + 1) d (e + 1)

theorem r2_drain : ∀ c a d e, ⟨a, 0, c + 1, d + c + 1, e⟩ [fm]⊢* ⟨a + 2 * (c + 1), 0, 0, d, e + c + 1⟩ := by
  intro c; induction c with
  | zero => intro a d e; step fm; ring_nf; finish
  | succ c ih =>
    intro a d e
    show ⟨a, 0, (c + 1) + 1, d + (c + 1 + 1), e⟩ [fm]⊢* _
    rw [show d + (c + 1 + 1) = (d + (c + 1)) + 1 from by ring]
    show ⟨a, 0, (c + 1) + 1, (d + (c + 1)) + 1, e⟩ [fm]⊢* _
    step fm
    show ⟨a + 2, 0, c + 1, d + (c + 1), e + 1⟩ [fm]⊢* ⟨a + 2 * (c + 1 + 1), 0, 0, d, e + (c + 1 + 1)⟩
    rw [show a + 2 * (c + 1 + 1) = (a + 2) + 2 * (c + 1) from by ring,
        show e + (c + 1 + 1) = (e + 1) + (c + 1) from by ring]
    exact ih (a + 2) d (e + 1)

theorem r3_drain : ∀ k a d e, ⟨a + k, 0, 0, d, e⟩ [fm]⊢* ⟨a, 0, 0, d + 2 * k, e + 2 * k⟩ := by
  intro k; induction k with
  | zero => intro a d e; exists 0
  | succ k ih =>
    intro a d e
    rw [show a + (k + 1) = (a + k) + 1 from by ring]
    step fm
    rw [show d + 2 * (k + 1) = (d + 2) + 2 * k from by ring,
        show e + 2 * (k + 1) = (e + 2) + 2 * k from by ring]
    exact ih a (d + 2) (e + 2)

theorem r3r2r2_chain : ∀ k a e, ⟨a + 1, 0, 2 * k, 0, e⟩ [fm]⊢* ⟨a + 1 + 3 * k, 0, 0, 0, e + 4 * k⟩ := by
  intro k; induction k with
  | zero => intro a e; exists 0
  | succ k ih =>
    intro a e
    rw [show 2 * (k + 1) = 2 * k + 2 from by ring]
    show ⟨a + 1, 0, 2 * k + (1 + 1), 0, e⟩ [fm]⊢* _
    step fm; step fm; step fm
    rw [show a + 1 + 3 * (k + 1) = (a + 3) + 1 + 3 * k from by ring,
        show e + 4 * (k + 1) = (e + 4) + 4 * k from by ring]
    exact ih (a + 3) (e + 4)

theorem r2_drain_partial : ∀ j a c e, ⟨a, 0, c + j + 1, j, e⟩ [fm]⊢* ⟨a + 2 * j, 0, c + 1, 0, e + j⟩ := by
  intro j; induction j with
  | zero => intro a c e; exists 0
  | succ j ih =>
    intro a c e
    rw [show c + (j + 1) + 1 = (c + j + 1) + 1 from by ring]
    show ⟨a, 0, (c + j + 1) + 1, j + 1, e⟩ [fm]⊢* _
    step fm
    rw [show a + 2 * (j + 1) = (a + 2) + 2 * j from by ring,
        show e + (j + 1) = (e + 1) + j from by ring]
    exact ih (a + 2) c (e + 1)

theorem chain_odd : ∀ k c d e, ⟨0, 2 * k + 1, c + 1, d + k + 1, e⟩ [fm]⊢*
    ⟨1, 0, c + k + 1, d, e + k + 1⟩ := by
  intro k; induction k with
  | zero =>
    intro c d e
    show ⟨0, 0 + 1, c + 1, d + 0 + 1, e⟩ [fm]⊢* _
    step fm; step fm; finish
  | succ k ih =>
    intro c d e
    rw [show 2 * (k + 1) + 1 = (2 * k + 1) + 2 from by ring,
        show d + (k + 1) + 1 = (d + k + 1) + 1 from by ring]
    show ⟨0, (2 * k + 1) + (0 + 2), c + 1, (d + k + 1) + 1, e⟩ [fm]⊢* _
    apply stepStar_trans (r2r1r1_round (b := 2 * k + 1) (c := c) (d := d + k + 1) (e := e))
    rw [show c + (k + 1) + 1 = (c + 1) + k + 1 from by ring,
        show e + (k + 1) + 1 = (e + 1) + k + 1 from by ring]
    exact ih (c + 1) d (e + 1)

theorem r3r2r2_chain_odd : ∀ k a e, ⟨a + 1, 0, 2 * k + 1, 0, e⟩ [fm]⊢*
    ⟨a + 3 * k + 2, 0, 0, 1, e + 4 * k + 3⟩ := by
  intro k; induction k with
  | zero =>
    intro a e
    show ⟨a + 1, 0, 0 + 1, 0, e⟩ [fm]⊢* _
    step fm; step fm
    ring_nf; finish
  | succ k ih =>
    intro a e
    rw [show 2 * (k + 1) + 1 = 2 * k + 1 + 2 from by ring]
    show ⟨a + 1, 0, 2 * k + 1 + (1 + 1), 0, e⟩ [fm]⊢* _
    step fm; step fm; step fm
    rw [show a + 3 * (k + 1) + 2 = (a + 3) + 3 * k + 2 from by ring,
        show e + 4 * (k + 1) + 3 = (e + 4) + 4 * k + 3 from by ring]
    exact ih (a + 3) (e + 4)

theorem alt_even_drain : ∀ k a e, ⟨a + 1, 0, 2 * k, 0, e⟩ [fm]⊢*
    ⟨0, 0, 0, 2 * a + 6 * k + 2, e + 2 * a + 10 * k + 2⟩ := by
  intro k a e
  apply stepStar_trans (r3r2r2_chain k a e)
  rw [show a + 1 + 3 * k = 0 + (a + 1 + 3 * k) from by ring,
      show 2 * a + 6 * k + 2 = 0 + 2 * (a + 1 + 3 * k) from by ring,
      show e + 2 * a + 10 * k + 2 = (e + 4 * k) + 2 * (a + 1 + 3 * k) from by ring]
  exact r3_drain (a + 1 + 3 * k) 0 0 (e + 4 * k)

theorem alt_odd_drain : ∀ k a e, ⟨a + 1, 0, 2 * k + 1, 0, e⟩ [fm]⊢*
    ⟨0, 0, 0, 2 * a + 6 * k + 5, e + 2 * a + 10 * k + 7⟩ := by
  intro k a e
  apply stepStar_trans (r3r2r2_chain_odd k a e)
  show ⟨a + 3 * k + 2, 0, 0, 1, e + 4 * k + 3⟩ [fm]⊢* _
  rw [show a + 3 * k + 2 = (a + 3 * k + 1) + 1 from by ring]
  step fm
  show ⟨a + 3 * k + 1, 0, 0, 3, e + 4 * k + 3 + 2⟩ [fm]⊢* _
  rw [show a + 3 * k + 1 = 0 + (a + 3 * k + 1) from by ring,
      show 2 * a + 6 * k + 5 = 3 + 2 * (a + 3 * k + 1) from by ring,
      show e + 2 * a + 10 * k + 7 = (e + 4 * k + 3 + 2) + 2 * (a + 3 * k + 1) from by ring]
  exact r3_drain (a + 3 * k + 1) 0 3 (e + 4 * k + 3 + 2)

theorem trans_odd_le (m j : ℕ) :
    ⟨0, 0, 0, 2 * m + 1 + j, 2 * m + 1⟩ [fm]⊢⁺
    ⟨0, 0, 0, 4 * m + j + 4, 6 * m + 5⟩ := by
  have h1 := e_to_b (2 * m + 1) 0 (2 * m + 1 + j) 0
  simp only [Nat.zero_add] at h1
  apply stepStar_stepPlus_stepPlus h1
  step fm
  -- After R5: (0, 2m, 1, 2m+1+j, 0)
  -- r2r1r1_chain(m, 0, m+1+j, 0): (0, 2m, 1, (m+1+j)+m, 0) -> (0, 0, m+1, m+1+j, m)
  have h3 := r2r1r1_chain m 0 (m + 1 + j) 0
  rw [show (0 : ℕ) + 1 = 1 from by ring,
      show (m + 1 + j) + m = 2 * m + 1 + j from by ring,
      show (0 : ℕ) + m + 1 = m + 1 from by ring,
      show (0 : ℕ) + m = m from by ring] at h3
  apply stepStar_trans h3
  -- Now: (0, 0, m+1, m+1+j, m) ⊢* target
  -- r2_drain(m, 0, j, m): (0, 0, m+1, j+m+1, m) -> (2(m+1), 0, 0, j, m+(m+1))
  have h4 := r2_drain m 0 j m
  rw [show j + m + 1 = m + 1 + j from by ring,
      show (0 : ℕ) + 2 * (m + 1) = 2 * m + 2 from by ring,
      show m + m + 1 = 2 * m + 1 from by ring] at h4
  apply stepStar_trans h4
  have h5 := r3_drain (2 * m + 2) 0 j (2 * m + 1)
  rw [show (0 : ℕ) + (2 * m + 2) = 2 * m + 2 from by ring,
      show j + 2 * (2 * m + 2) = 4 * m + j + 4 from by ring,
      show 2 * m + 1 + 2 * (2 * m + 2) = 6 * m + 5 from by ring] at h5
  exact h5

theorem trans_even_le (m j : ℕ) :
    ⟨0, 0, 0, 2 * m + 2 + j, 2 * m + 2⟩ [fm]⊢⁺
    ⟨0, 0, 0, 4 * m + j + 6, 6 * m + 8⟩ := by
  have h1 := e_to_b (2 * m + 2) 0 (2 * m + 2 + j) 0
  simp only [Nat.zero_add] at h1
  apply stepStar_stepPlus_stepPlus h1
  rw [show (2 * m + 2 : ℕ) = (2 * m + 1) + 1 from by ring]
  step fm
  -- After R5: (0, 2m+1, 1, 2m+2+j, 0)
  -- chain_odd(m, 0, m+1+j, 0): (0, 2m+1, 1, (m+1+j)+m+1, 0) -> (1, 0, m+1, m+1+j, m+1)
  have h3 := chain_odd m 0 (m + 1 + j) 0
  rw [show (0 : ℕ) + 1 = 1 from by ring,
      show (m + 1 + j) + m + 1 = 2 * m + 2 + j from by ring] at h3
  simp only [Nat.zero_add] at h3
  rw [show 2 * m + 1 + 1 + j = 2 * m + 2 + j from by ring]
  apply stepStar_trans h3
  -- Now: (1, 0, m+1, m+1+j, m+1) ⊢* target
  have h4 := r2_drain m 1 j (m + 1)
  rw [show j + m + 1 = m + 1 + j from by ring,
      show 1 + 2 * (m + 1) = 2 * m + 3 from by ring,
      show m + 1 + m + 1 = 2 * m + 2 from by ring] at h4
  apply stepStar_trans h4
  -- Now: (2m+3, 0, 0, j, 2m+2) ⊢* target
  have h5 := r3_drain (2 * m + 3) 0 j (2 * m + 2)
  rw [show (0 : ℕ) + (2 * m + 3) = 2 * m + 3 from by ring,
      show j + 2 * (2 * m + 3) = 4 * m + j + 6 from by ring,
      show 2 * m + 2 + 2 * (2 * m + 3) = 6 * m + 8 from by ring] at h5
  exact h5

theorem trans_even_gt_clean (g r : ℕ) :
    ⟨0, 0, 0, 2 * g + 2 * r + 2, 4 * g + 2 * r + 4⟩ [fm]⊢⁺
    ⟨0, 0, 0, 6 * g + 4 * r + 8, 12 * g + 6 * r + 14⟩ := by
  have h1 := e_to_b (4 * g + 2 * r + 4) 0 (2 * g + 2 * r + 2) 0
  simp only [Nat.zero_add] at h1
  apply stepStar_stepPlus_stepPlus h1
  rw [show (4 * g + 2 * r + 4 : ℕ) = (4 * g + 2 * r + 3) + 1 from by ring]
  step fm
  -- After R5: (0, 4g+2r+3, 1, 2g+2r+2, 0)
  -- chain_odd(2g+r+1, 0, r, 0): (0, 2(2g+r+1)+1, 1, r+(2g+r+1)+1, 0) -> (1, 0, (2g+r+1)+1, r, (2g+r+1)+1)
  have h3 := chain_odd (2 * g + r + 1) 0 r 0
  rw [show (0 : ℕ) + 1 = 1 from by ring,
      show r + (2 * g + r + 1) + 1 = 2 * g + 2 * r + 2 from by ring,
      show 2 * (2 * g + r + 1) + 1 = 4 * g + 2 * r + 3 from by ring,
      show (0 : ℕ) + (2 * g + r + 1) + 1 = 2 * g + r + 2 from by ring] at h3
  apply stepStar_trans h3
  -- Now: (1, 0, 2g+r+2, r, 2g+r+2) ⊢* target
  -- r2_drain_partial(r, 1, 2g+1, 2g+r+2)
  -- c+j+1 = (2g+1)+r+1 = 2g+r+2 ✓
  have h4 := r2_drain_partial r 1 (2 * g + 1) (2 * g + r + 2)
  rw [show (2 * g + 1) + r + 1 = 2 * g + r + 2 from by ring,
      show 1 + 2 * r = 2 * r + 1 from by ring,
      show (2 * g + 1) + 1 = 2 * g + 2 from by ring,
      show 2 * g + r + 2 + r = 2 * g + 2 * r + 2 from by ring] at h4
  apply stepStar_trans h4
  -- Now: (2r+1, 0, 2g+2, 0, 2g+2r+2) ⊢* target
  -- 2g+2 = 2*(g+1), a = 2r+1 = 2r + 0 + 1
  -- alt_even_drain(g+1, 2r, 2g+2r+2)
  have h5 := alt_even_drain (g + 1) (2 * r) (2 * g + 2 * r + 2)
  rw [show 2 * r + 0 + 1 = 2 * r + 1 from by ring,
      show 2 * (g + 1) = 2 * g + 2 from by ring,
      show 2 * (2 * r) + 6 * (g + 1) + 2 = 6 * g + 4 * r + 8 from by ring,
      show 2 * g + 2 * r + 2 + 2 * (2 * r) + 10 * (g + 1) + 2 = 12 * g + 6 * r + 14 from by ring] at h5
  exact h5

theorem main_transition (d e : ℕ) (hd : d ≥ 1) (he : e ≥ 1) (hle : e ≤ 2 * d) :
    ⟨0, 0, 0, 2 * d, 2 * e⟩ [fm]⊢⁺ ⟨0, 0, 0, 2 * d + 2 * e + 2, 6 * e + 2⟩ := by
  rcases (show e ≤ d ∨ d < e from by omega) with h | h
  · obtain ⟨j, rfl⟩ : ∃ j, d = e + j := ⟨d - e, by omega⟩
    obtain ⟨e', rfl⟩ : ∃ e', e = e' + 1 := ⟨e - 1, by omega⟩
    rw [show 2 * (e' + 1 + j) = 2 * e' + 2 + 2 * j from by ring,
        show 2 * (e' + 1) = 2 * e' + 2 from by ring,
        show 2 * e' + 2 + 2 * j + (2 * e' + 2) + 2 = 4 * e' + 2 * j + 6 from by ring,
        show 6 * (e' + 1) + 2 = 6 * e' + 8 from by ring]
    exact trans_even_le e' (2 * j)
  · obtain ⟨g, rfl⟩ : ∃ g, e = d + 1 + g := ⟨e - d - 1, by omega⟩
    obtain ⟨r, rfl⟩ : ∃ r, d = g + 1 + r := ⟨d - g - 1, by omega⟩
    rw [show 2 * (g + 1 + r) = 2 * g + 2 * r + 2 from by ring,
        show 2 * (g + 1 + r + 1 + g) = 4 * g + 2 * r + 4 from by ring,
        show 2 * g + 2 * r + 2 + (4 * g + 2 * r + 4) + 2 = 6 * g + 4 * r + 8 from by ring,
        show 6 * (g + 1 + r + 1 + g) + 2 = 12 * g + 6 * r + 14 from by ring]
    exact trans_even_gt_clean g r

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨0, 0, 0, 2, 2⟩) (by execute fm 1)
  apply progress_nonhalt (fm := fm)
    (P := fun q ↦ ∃ d e, q = ⟨0, 0, 0, 2 * d, 2 * e⟩ ∧ d ≥ 1 ∧ e ≥ 1 ∧ e ≤ 2 * d)
  · intro c ⟨d, e, hq, hd, he, hle⟩
    subst hq
    exact ⟨⟨0, 0, 0, 2 * d + 2 * e + 2, 6 * e + 2⟩,
      ⟨d + e + 1, 3 * e + 1, by ring_nf, by omega, by omega, by omega⟩,
      main_transition d e hd he hle⟩
  · exact ⟨1, 1, rfl, by omega, by omega, by omega⟩

end Sz22_2003_unofficial_1151
