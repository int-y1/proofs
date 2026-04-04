import BBfLean.FM
import Mathlib.Tactic.Ring
import Mathlib.Tactic.IntervalCases

namespace Sz22_2003_unofficial_1628

def Q := ℕ × ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a, b+1, c+1, d, e, f⟩ => some ⟨a, b, c, d+1, e+1, f⟩
  | ⟨a, b+1, c, d, e, f⟩ => some ⟨a+1, b, c, d, e, f+1⟩
  | ⟨a, b, c, d+1, e, f+1⟩ => some ⟨a, b+3, c, d, e, f⟩
  | ⟨a, b, c, d, e+1, f⟩ => some ⟨a, b, c+1, d, e, f⟩
  | ⟨a+1, b, c, d, e, f⟩ => some ⟨a, b+1, c, d, e+1, f⟩
  | _ => none

-- R4 drain: move e to c
theorem r4_drain : ∀ k, ∀ a c f, ⟨a, 0, c, 0, k, f⟩ [fm]⊢* ⟨a, 0, c + k, 0, 0, f⟩ := by
  intro k; induction' k with k ih <;> intro a c f
  · exists 0
  · rw [show c + (k + 1) = (c + 1) + k from by ring]
    step fm; exact ih a (c + 1) f

-- R3+R2x3 drain
theorem r3_r2x3_drain : ∀ k, ∀ a e G,
    ⟨a, 0, 0, k, e, G + k⟩ [fm]⊢* ⟨a + 3 * k, 0, 0, 0, e, G + 3 * k⟩ := by
  intro k; induction' k with k ih <;> intro a e G
  · simp; exists 0
  · rw [show G + (k + 1) = G + k + 1 from by ring]
    step fm; step fm; step fm; step fm
    rw [show a + 3 * (k + 1) = (a + 3) + 3 * k from by ring,
        show G + 3 * (k + 1) = (G + 3) + 3 * k from by ring,
        show G + k + 3 = (G + 3) + k from by ring]
    exact ih (a + 3) e (G + 3)

-- Inner loop for r=0
theorem inner_r0 : ∀ q, ∀ a d e f,
    ⟨a, 3, 3 * q, d, e, f + q⟩ [fm]⊢* ⟨a + 3, 0, 0, d + 2 * q, e + 3 * q, f + 3⟩ := by
  intro q; induction' q with q ih <;> intro a d e f
  · simp; step fm; step fm; step fm; ring_nf; finish
  · rw [show 3 * (q + 1) = (3 * q + 2) + 1 from by ring,
        show f + (q + 1) = (f + 1) + q from by ring]
    step fm
    rw [show 3 * q + 2 = (3 * q + 1) + 1 from by ring]
    step fm
    rw [show 3 * q + 1 = 3 * q + 0 + 1 from by ring]
    step fm
    rw [show (f + 1 : ℕ) + q = f + q + 1 from by ring]
    step fm
    -- Goal has e+1+1+1 and d+1+1, need to match IH target
    rw [show d + 1 + 1 = d + 2 from by ring,
        show e + 1 + 1 + 1 = e + 3 from by ring]
    have h := ih a (d + 2) (e + 3) f
    rw [show d + 2 + 2 * q = d + 2 * (q + 1) from by ring,
        show e + 3 + 3 * q = e + 3 * (q + 1) from by ring] at h
    exact h

-- Inner loop for r=1
theorem inner_r1 : ∀ q, ∀ a d e f,
    ⟨a, 3, 3 * q + 1, d, e, f + q⟩ [fm]⊢* ⟨a + 2, 0, 0, d + 2 * q + 1, e + 3 * q + 1, f + 2⟩ := by
  intro q; induction' q with q ih <;> intro a d e f
  · simp; step fm; step fm; step fm; ring_nf; finish
  · rw [show 3 * (q + 1) + 1 = (3 * q + 1 + 2) + 1 from by ring,
        show f + (q + 1) = (f + 1) + q from by ring]
    step fm
    rw [show 3 * q + 1 + 2 = (3 * q + 1 + 1) + 1 from by ring]
    step fm
    rw [show 3 * q + 1 + 1 = (3 * q + 1) + 0 + 1 from by ring]
    step fm
    rw [show (f + 1 : ℕ) + q = f + q + 1 from by ring]
    step fm
    rw [show d + 1 + 1 = d + 2 from by ring,
        show e + 1 + 1 + 1 = e + 3 from by ring]
    have h := ih a (d + 2) (e + 3) f
    rw [show d + 2 + 2 * q + 1 = d + 2 * (q + 1) + 1 from by ring,
        show e + 3 + 3 * q + 1 = e + 3 * (q + 1) + 1 from by ring] at h
    exact h

-- Inner loop for r=2
theorem inner_r2 : ∀ q, ∀ a d e f,
    ⟨a, 3, 3 * q + 2, d, e, f + q⟩ [fm]⊢* ⟨a + 1, 0, 0, d + 2 * q + 2, e + 3 * q + 2, f + 1⟩ := by
  intro q; induction' q with q ih <;> intro a d e f
  · simp; step fm; step fm; step fm; ring_nf; finish
  · rw [show 3 * (q + 1) + 2 = (3 * q + 2 + 2) + 1 from by ring,
        show f + (q + 1) = (f + 1) + q from by ring]
    step fm
    rw [show 3 * q + 2 + 2 = (3 * q + 2 + 1) + 1 from by ring]
    step fm
    rw [show 3 * q + 2 + 1 = (3 * q + 2) + 0 + 1 from by ring]
    step fm
    rw [show (f + 1 : ℕ) + q = f + q + 1 from by ring]
    step fm
    rw [show d + 1 + 1 = d + 2 from by ring,
        show e + 1 + 1 + 1 = e + 3 from by ring]
    have h := ih a (d + 2) (e + 3) f
    rw [show d + 2 + 2 * q + 2 = d + 2 * (q + 1) + 2 from by ring,
        show e + 3 + 3 * q + 2 = e + 3 * (q + 1) + 2 from by ring] at h
    exact h

-- Opening: R5, R1, R3
theorem opening : ∀ A n G,
    ⟨A + 1, 0, n + 1, 0, 0, G + 1⟩ [fm]⊢* ⟨A, 3, n, 0, 2, G⟩ := by
  intro A n G
  step fm; step fm; step fm; finish

-- Full transition for n = 3m
theorem trans_mod0 (m G : ℕ) :
    ⟨9 * m * m + 3 * m + 1, 0, 0, 0, 3 * m + 1, G + 3 * m + 1⟩ [fm]⊢⁺
    ⟨9 * m * m + 9 * m + 3, 0, 0, 0, 3 * m + 2, G + 6 * m + 3⟩ := by
  have p1 := r4_drain (3 * m + 1) (9 * m * m + 3 * m + 1) 0 (G + 3 * m + 1)
  rw [show (0 : ℕ) + (3 * m + 1) = 3 * m + 1 from by ring] at p1
  have p2 := opening (9 * m * m + 3 * m) (3 * m) (G + 3 * m)
  rw [show 9 * m * m + 3 * m + 1 = (9 * m * m + 3 * m) + 1 from by ring,
      show 3 * m + 1 = (3 * m) + 1 from by ring,
      show G + 3 * m + 1 = (G + 3 * m) + 1 from by ring] at p2
  have p3 := inner_r0 m (9 * m * m + 3 * m) 0 2 (G + 2 * m)
  rw [show G + 2 * m + m = G + 3 * m from by ring,
      show 0 + 2 * m = 2 * m from by ring,
      show 2 + 3 * m = 3 * m + 2 from by ring] at p3
  have p4 := r3_r2x3_drain (2 * m) (9 * m * m + 3 * m + 3) (3 * m + 2) (G + 3)
  rw [show G + 3 + 2 * m = G + 2 * m + 3 from by ring,
      show 9 * m * m + 3 * m + 3 + 3 * (2 * m) = 9 * m * m + 9 * m + 3 from by ring,
      show G + 3 + 3 * (2 * m) = G + 6 * m + 3 from by ring] at p4
  have p_star := stepStar_trans (stepStar_trans (stepStar_trans p1 p2) p3) p4
  exact stepStar_stepPlus p_star (by simp [Q])

-- Full transition for n = 3m+1
theorem trans_mod1 (m G : ℕ) :
    ⟨9 * m * m + 9 * m + 3, 0, 0, 0, 3 * m + 2, G + 3 * m + 2⟩ [fm]⊢⁺
    ⟨9 * m * m + 15 * m + 7, 0, 0, 0, 3 * m + 3, G + 6 * m + 5⟩ := by
  have p1 := r4_drain (3 * m + 2) (9 * m * m + 9 * m + 3) 0 (G + 3 * m + 2)
  rw [show (0 : ℕ) + (3 * m + 2) = 3 * m + 2 from by ring] at p1
  have p2 := opening (9 * m * m + 9 * m + 2) (3 * m + 1) (G + 3 * m + 1)
  rw [show (9 * m * m + 9 * m + 2) + 1 = 9 * m * m + 9 * m + 3 from by ring,
      show (3 * m + 1) + 1 = 3 * m + 2 from by ring,
      show (G + 3 * m + 1) + 1 = G + 3 * m + 2 from by ring] at p2
  have p3 := inner_r1 m (9 * m * m + 9 * m + 2) 0 2 (G + 2 * m + 1)
  rw [show G + 2 * m + 1 + m = G + 3 * m + 1 from by ring,
      show 9 * m * m + 9 * m + 2 + 2 = 9 * m * m + 9 * m + 4 from by ring,
      show 0 + 2 * m + 1 = 2 * m + 1 from by ring,
      show 2 + 3 * m + 1 = 3 * m + 3 from by ring,
      show G + 2 * m + 1 + 2 = G + 2 * m + 3 from by ring] at p3
  have p4 := r3_r2x3_drain (2 * m + 1) (9 * m * m + 9 * m + 4) (3 * m + 3) (G + 2)
  rw [show G + 2 + (2 * m + 1) = G + 2 * m + 3 from by ring,
      show 9 * m * m + 9 * m + 4 + 3 * (2 * m + 1) = 9 * m * m + 15 * m + 7 from by ring,
      show G + 2 + 3 * (2 * m + 1) = G + 6 * m + 5 from by ring] at p4
  have p_star := stepStar_trans (stepStar_trans (stepStar_trans p1 p2) p3) p4
  exact stepStar_stepPlus p_star (by simp [Q])

-- Full transition for n = 3m+2
theorem trans_mod2 (m G : ℕ) :
    ⟨9 * m * m + 15 * m + 7, 0, 0, 0, 3 * m + 3, G + 3 * m + 3⟩ [fm]⊢⁺
    ⟨9 * m * m + 21 * m + 13, 0, 0, 0, 3 * m + 4, G + 6 * m + 7⟩ := by
  have p1 := r4_drain (3 * m + 3) (9 * m * m + 15 * m + 7) 0 (G + 3 * m + 3)
  rw [show (0 : ℕ) + (3 * m + 3) = 3 * m + 3 from by ring] at p1
  have p2 := opening (9 * m * m + 15 * m + 6) (3 * m + 2) (G + 3 * m + 2)
  rw [show (9 * m * m + 15 * m + 6) + 1 = 9 * m * m + 15 * m + 7 from by ring,
      show (3 * m + 2) + 1 = 3 * m + 3 from by ring,
      show (G + 3 * m + 2) + 1 = G + 3 * m + 3 from by ring] at p2
  have p3 := inner_r2 m (9 * m * m + 15 * m + 6) 0 2 (G + 2 * m + 2)
  rw [show G + 2 * m + 2 + m = G + 3 * m + 2 from by ring,
      show 9 * m * m + 15 * m + 6 + 1 = 9 * m * m + 15 * m + 7 from by ring,
      show 0 + 2 * m + 2 = 2 * m + 2 from by ring,
      show 2 + 3 * m + 2 = 3 * m + 4 from by ring,
      show G + 2 * m + 2 + 1 = G + 2 * m + 3 from by ring] at p3
  have p4 := r3_r2x3_drain (2 * m + 2) (9 * m * m + 15 * m + 7) (3 * m + 4) (G + 1)
  rw [show G + 1 + (2 * m + 2) = G + 2 * m + 3 from by ring,
      show 9 * m * m + 15 * m + 7 + 3 * (2 * m + 2) = 9 * m * m + 21 * m + 13 from by ring,
      show G + 1 + 3 * (2 * m + 2) = G + 6 * m + 7 from by ring] at p4
  have p_star := stepStar_trans (stepStar_trans (stepStar_trans p1 p2) p3) p4
  exact stepStar_stepPlus p_star (by simp [Q])

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨1, 0, 0, 0, 1, 1⟩) (by execute fm 2)
  apply progress_nonhalt (fm := fm)
    (P := fun q ↦ ∃ n G, q = ⟨n * n + n + 1, 0, 0, 0, n + 1, G + n + 1⟩)
  · intro q ⟨n, G, hq⟩
    subst hq
    have hmod : n % 3 < 3 := Nat.mod_lt _ (by omega)
    have hdiv : n = 3 * (n / 3) + n % 3 := (Nat.div_add_mod n 3).symm
    interval_cases (n % 3)
    · -- n mod 3 = 0
      obtain ⟨m, rfl⟩ := Nat.dvd_of_mod_eq_zero (by omega : n % 3 = 0)
      clear hdiv hmod
      refine ⟨⟨9 * m * m + 9 * m + 3, 0, 0, 0, 3 * m + 2, G + 6 * m + 3⟩,
        ⟨3 * m + 1, G + 3 * m + 1, ?_⟩, ?_⟩
      · ring_nf
      · show ⟨3 * m * (3 * m) + 3 * m + 1, 0, 0, 0, 3 * m + 1, G + 3 * m + 1⟩ [fm]⊢⁺
             ⟨9 * m * m + 9 * m + 3, 0, 0, 0, 3 * m + 2, G + 6 * m + 3⟩
        rw [show 3 * m * (3 * m) = 9 * m * m from by ring]
        exact trans_mod0 m G
    · have ⟨m, hm⟩ : ∃ m, n = 3 * m + 1 := ⟨n / 3, by omega⟩
      subst hm; clear hdiv hmod
      refine ⟨⟨9 * m * m + 15 * m + 7, 0, 0, 0, 3 * m + 3, G + 6 * m + 5⟩,
        ⟨3 * m + 2, G + 3 * m + 2, ?_⟩, ?_⟩
      · ring_nf
      · show ⟨(3 * m + 1) * (3 * m + 1) + (3 * m + 1) + 1, 0, 0, 0, 3 * m + 1 + 1,
              G + (3 * m + 1) + 1⟩ [fm]⊢⁺
             ⟨9 * m * m + 15 * m + 7, 0, 0, 0, 3 * m + 3, G + 6 * m + 5⟩
        rw [show (3 * m + 1) * (3 * m + 1) + (3 * m + 1) + 1 = 9 * m * m + 9 * m + 3 from by ring,
            show 3 * m + 1 + 1 = 3 * m + 2 from by ring,
            show G + (3 * m + 1) + 1 = G + 3 * m + 2 from by ring]
        exact trans_mod1 m G
    · have ⟨m, hm⟩ : ∃ m, n = 3 * m + 2 := ⟨n / 3, by omega⟩
      subst hm; clear hdiv hmod
      refine ⟨⟨9 * m * m + 21 * m + 13, 0, 0, 0, 3 * m + 4, G + 6 * m + 7⟩,
        ⟨3 * m + 3, G + 3 * m + 3, ?_⟩, ?_⟩
      · ring_nf
      · show ⟨(3 * m + 2) * (3 * m + 2) + (3 * m + 2) + 1, 0, 0, 0, 3 * m + 2 + 1,
              G + (3 * m + 2) + 1⟩ [fm]⊢⁺
             ⟨9 * m * m + 21 * m + 13, 0, 0, 0, 3 * m + 4, G + 6 * m + 7⟩
        rw [show (3 * m + 2) * (3 * m + 2) + (3 * m + 2) + 1 = 9 * m * m + 15 * m + 7 from by ring,
            show 3 * m + 2 + 1 = 3 * m + 3 from by ring,
            show G + (3 * m + 2) + 1 = G + 3 * m + 3 from by ring]
        exact trans_mod2 m G
  · exact ⟨0, 0, by simp⟩

end Sz22_2003_unofficial_1628
