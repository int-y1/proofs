import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #1891: [9/35, 5/33, 98/3, 11/7, 63/2]

Vector representation:
```
 0  2 -1 -1  0
 0 -1  1  0 -1
 1 -1  0  2  0
 0  0  0 -1  1
-1  2  0  1  0
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_1891

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a, b, c+1, d+1, e⟩ => some ⟨a, b+2, c, d, e⟩
  | ⟨a, b+1, c, d, e+1⟩ => some ⟨a, b, c+1, d, e⟩
  | ⟨a, b+1, c, d, e⟩ => some ⟨a+1, b, c, d+2, e⟩
  | ⟨a, b, c, d+1, e⟩ => some ⟨a, b, c, d, e+1⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b+2, c, d+1, e⟩
  | _ => none

theorem d_to_e : ∀ k d, ⟨a, 0, 0, d + k, 0⟩ [fm]⊢* ⟨a, 0, 0, d, k⟩ := by
  intro k; induction' k with k ih <;> intro d
  · exists 0
  · rw [show d + (k + 1) = d + 1 + k from by ring]
    apply stepStar_trans (ih (d + 1)); step fm; finish

theorem b_to_ad : ∀ b a d, ⟨a, b, 0, d, 0⟩ [fm]⊢* ⟨a + b, 0, 0, d + 2 * b, 0⟩ := by
  intro b; induction' b with b ih <;> intro a d
  · exists 0
  · step fm; apply stepStar_trans (ih (a + 1) (d + 2)); ring_nf; finish

theorem r1r1r3_chain : ∀ k a b c, ⟨a, b, c + 2 * k, 2, 0⟩ [fm]⊢* ⟨a + k, b + 3 * k, c, 2, 0⟩ := by
  intro k; induction' k with k ih <;> intro a b c
  · exists 0
  · rw [show c + 2 * (k + 1) = (c + 2) + 2 * k from by ring]
    apply stepStar_trans (ih a b (c + 2))
    step fm; step fm; step fm; ring_nf; finish

theorem process_chain_even : ∀ k a b, ⟨a, b + 1, 2 * k, 2, 0⟩ [fm]⊢⁺ ⟨a + b + 4 * k + 1, 0, 0, 2 * b + 6 * k + 4, 0⟩ := by
  intro k a b
  apply stepStar_stepPlus_stepPlus
  · rw [show 2 * k = 0 + 2 * k from by ring]; exact r1r1r3_chain k a (b + 1) 0
  rw [show b + 1 + 3 * k = (b + 3 * k) + 1 from by ring]
  exact stepStar_stepPlus (by
    apply stepStar_trans (b_to_ad (b + 3 * k + 1) (a + k) 2)
    ring_nf; finish) (by intro h; have := Prod.mk.inj h; have := Prod.mk.inj this.2; omega)

theorem process_chain_odd : ∀ k a b, ⟨a, b + 1, 2 * k + 1, 2, 0⟩ [fm]⊢⁺ ⟨a + b + 4 * k + 3, 0, 0, 2 * b + 6 * k + 7, 0⟩ := by
  intro k a b
  apply stepStar_stepPlus_stepPlus
  · rw [show 2 * k + 1 = 1 + 2 * k from by ring]; exact r1r1r3_chain k a (b + 1) 1
  rw [show b + 1 + 3 * k = (b + 3 * k) + 1 from by ring]
  step fm
  rw [show (b + 3 * k) + 1 + 2 = (b + 3 * k + 3) from by ring]
  exact stepPlus_stepStar (stepStar_stepPlus (by
    apply stepStar_trans (b_to_ad (b + 3 * k + 3) (a + k) 1); ring_nf; finish)
    (by intro h; have h2 := (Prod.mk.inj h).2; have h3 := (Prod.mk.inj h2).1; omega))

theorem process_chain : ∀ c a b, ⟨a, b + 1, c, 2, 0⟩ [fm]⊢⁺ ⟨a + b + 2 * c + 1, 0, 0, 2 * b + 3 * c + 4, 0⟩ := by
  intro c; rcases Nat.even_or_odd c with ⟨k, hk⟩ | ⟨k, hk⟩ <;> intro a b
  · rw [show k + k = 2 * k from by ring] at hk; subst hk
    have := process_chain_even k a b
    rw [show a + b + 4 * k + 1 = a + b + 2 * (2 * k) + 1 from by ring,
        show 2 * b + 6 * k + 4 = 2 * b + 3 * (2 * k) + 4 from by ring] at this; exact this
  · subst hk; have := process_chain_odd k a b
    rw [show a + b + 4 * k + 3 = a + b + 2 * (2 * k + 1) + 1 from by ring,
        show 2 * b + 6 * k + 7 = 2 * b + 3 * (2 * k + 1) + 4 from by ring] at this; exact this

theorem end_e0 : ⟨a + 1, 0, c + 1, 0, 0⟩ [fm]⊢⁺ ⟨a + 2 * c + 4, 0, 0, 3 * c + 8, 0⟩ := by
  step fm; step fm; step fm
  have h := process_chain c (a + 1) 2
  rw [show a + 1 + 2 + 2 * c + 1 = a + 2 * c + 4 from by ring,
      show 2 * 2 + 3 * c + 4 = 3 * c + 8 from by ring] at h; exact stepPlus_stepStar h

theorem end_e1_base : ⟨a + 1, 0, 1, 0, 1⟩ [fm]⊢⁺ ⟨a + 5, 0, 0, 9, 0⟩ := by execute fm 9

theorem end_e1 : ∀ c, ⟨a + 1, 0, c + 1, 0, 1⟩ [fm]⊢⁺ ⟨a + 2 * c + 5, 0, 0, 3 * c + 9, 0⟩ := by
  intro c; rcases c with _ | c
  · exact end_e1_base
  · step fm; step fm; step fm; step fm; step fm; step fm; step fm
    have h := process_chain c (a + 2) 4
    rw [show a + 2 + 4 + 2 * c + 1 = a + 2 * (c + 1) + 5 from by ring,
        show 2 * 4 + 3 * c + 4 = 3 * (c + 1) + 9 from by ring] at h; exact stepPlus_stepStar h

theorem end_e2 : ⟨a + 1, 0, c + 1, 0, 2⟩ [fm]⊢⁺ ⟨a + 2 * c + 6, 0, 0, 3 * c + 10, 0⟩ := by
  step fm; step fm; step fm; step fm; step fm; step fm; step fm; step fm
  have h := process_chain c (a + 2) 3
  rw [show a + 2 + 3 + 2 * c + 1 = a + 2 * c + 6 from by ring,
      show 2 * 3 + 3 * c + 4 = 3 * c + 10 from by ring] at h; exact stepPlus_stepStar h

theorem end_e3 : ⟨a + 1, 0, c + 1, 0, 3⟩ [fm]⊢⁺ ⟨a + 2 * c + 7, 0, 0, 3 * c + 11, 0⟩ := by
  step fm; step fm; step fm; step fm; step fm; step fm; step fm; step fm; step fm
  have h := process_chain (c + 1) (a + 2) 2
  rw [show a + 2 + 2 + 2 * (c + 1) + 1 = a + 2 * c + 7 from by ring,
      show 2 * 2 + 3 * (c + 1) + 4 = 3 * c + 11 from by ring] at h; exact stepPlus_stepStar h

theorem inner_step : ⟨a + 2, 0, c + 1, 0, e + 4⟩ [fm]⊢* ⟨a + 1, 0, c + 4, 0, e⟩ := by
  step fm; step fm; step fm; step fm; step fm; step fm; ring_nf; finish

theorem main_inner : ∀ e a c, 4 * a ≥ e → ⟨a + 2, 0, c + 1, 0, e⟩ [fm]⊢⁺ ⟨a + 2 * c + 5 + e + e / 4, 0, 0, 3 * c + 8 + e + 5 * (e / 4), 0⟩ := by
  intro e; induction' e using Nat.strongRecOn with e ih; intro a c hae
  rcases e with _ | _ | _ | _ | e'
  · simp; have h := @end_e0 (a + 1) c; rw [show a + 1 + 2 * c + 4 = a + 2 * c + 5 from by ring] at h; exact h
  · simp; have h := end_e1 c (a := a + 1); rw [show a + 1 + 2 * c + 5 = a + 2 * c + 6 from by ring, show 3 * c + 9 = 3 * c + 8 + 1 from by ring] at h; exact h
  · simp; have h := @end_e2 (a + 1) c; rw [show a + 1 + 2 * c + 6 = a + 2 * c + 7 from by ring, show 3 * c + 10 = 3 * c + 8 + 2 from by ring] at h; exact h
  · simp; have h := @end_e3 (a + 1) c; rw [show a + 1 + 2 * c + 7 = a + 2 * c + 8 from by ring, show 3 * c + 11 = 3 * c + 8 + 3 from by ring] at h; exact h
  · obtain ⟨a', rfl⟩ : ∃ a', a = a' + 1 := ⟨a - 1, by omega⟩
    rw [show a' + 1 + 2 = a' + 3 from by ring, show a' + 3 = (a' + 1) + 2 from by ring]
    apply stepStar_stepPlus_stepPlus (inner_step (a := a' + 1) (c := c) (e := e'))
    rw [show a' + 1 + 1 = a' + 2 from by ring, show c + 4 = (c + 3) + 1 from by ring]
    have hlt : e' < e' + 1 + 1 + 1 + 1 := by omega
    have hge : 4 * a' ≥ e' := by omega
    have h := ih e' hlt a' (c + 3) hge
    have h4 : (e' + 1 + 1 + 1 + 1) / 4 = e' / 4 + 1 := by omega
    rw [show a' + 2 * (c + 3) + 5 + e' + e' / 4 = (a' + 1) + 2 * c + 5 + (e' + 1 + 1 + 1 + 1) + (e' / 4 + 1) from by ring,
        show 3 * (c + 3) + 8 + e' + 5 * (e' / 4) = 3 * c + 8 + (e' + 1 + 1 + 1 + 1) + 5 * (e' / 4 + 1) from by ring] at h
    rw [h4]; exact h

theorem r2_drain3 : ⟨a, 3, 0, 0, e + 3⟩ [fm]⊢* ⟨a, 0, 3, 0, e⟩ := by
  step fm; step fm; step fm; ring_nf; finish

theorem opening_full : ⟨a + 2, 0, 0, 0, d + 4⟩ [fm]⊢* ⟨a + 1, 0, 3, 0, d⟩ := by
  step fm; step fm; step fm
  rw [show d + 3 = d + 3 from rfl]
  exact r2_drain3 (a := a + 1) (e := d)

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨9, 0, 0, 15, 0⟩) (by execute fm 29)
  apply progress_nonhalt (fm := fm)
    (P := fun q ↦ ∃ a d, q = ⟨a + 2, 0, 0, d + 5, 0⟩ ∧ 4 * a ≥ d + 5)
  · intro c ⟨a, d, hq, had⟩; subst hq
    have step1 : ⟨a + 2, 0, 0, d + 5, 0⟩ [fm]⊢* ⟨a + 2, 0, 0, 0, d + 5⟩ := by
      have := d_to_e (d + 5) 0 (a := a + 2); simp at this; exact this
    have step2 : ⟨a + 2, 0, 0, 0, d + 5⟩ [fm]⊢* ⟨a + 1, 0, 3, 0, d + 1⟩ := by
      rw [show d + 5 = (d + 1) + 4 from by ring]; exact opening_full (a := a) (d := d + 1)
    have step3 : ⟨a + 1, 0, 3, 0, d + 1⟩ [fm]⊢⁺ ⟨(a - 1) + d + 10 + (d + 1) / 4, 0, 0, d + 15 + 5 * ((d + 1) / 4), 0⟩ := by
      rw [show a + 1 = (a - 1) + 2 from by omega, show (3 : ℕ) = 2 + 1 from by ring]
      have h := main_inner (d + 1) (a - 1) 2 (by omega)
      rw [show (a - 1) + 2 * 2 + 5 + (d + 1) + (d + 1) / 4 = (a - 1) + d + 10 + (d + 1) / 4 from by ring,
          show 3 * 2 + 8 + (d + 1) + 5 * ((d + 1) / 4) = d + 15 + 5 * ((d + 1) / 4) from by ring] at h
      exact h
    refine ⟨⟨(a - 1) + d + 10 + (d + 1) / 4, 0, 0, d + 15 + 5 * ((d + 1) / 4), 0⟩,
      ⟨(a - 1) + d + 8 + (d + 1) / 4, d + 10 + 5 * ((d + 1) / 4), by ring_nf, ?_⟩,
      stepStar_stepPlus_stepPlus step1 (stepStar_stepPlus_stepPlus step2 step3)⟩
    have : (d + 1) / 4 ≤ d + 1 := Nat.div_le_self (d + 1) 4
    omega
  · exact ⟨7, 10, by ring_nf, by omega⟩
