import BBfLean.FM
import Mathlib.Tactic.Ring

namespace Sz22_2003_unofficial_1011

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a, b+1, c+1, d, e⟩ => some ⟨a+2, b, c, d, e⟩
  | ⟨a+1, b, c, d+1, e⟩ => some ⟨a, b+2, c, d, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b, c+1, d, e+1⟩
  | ⟨a, b, c+1, d, e⟩ => some ⟨a, b, c, d+1, e⟩
  | ⟨a, b, c, d, e+1⟩ => some ⟨a+1, b, c+1, d, e⟩
  | _ => none

theorem r3_chain : ∀ k, ∀ a c e,
    ⟨a + k, 0, c, 0, e⟩ [fm]⊢* ⟨a, 0, c + k, 0, e + k⟩ := by
  intro k; induction' k with k ih <;> intro a c e
  · exists 0
  · rw [show a + (k + 1) = (a + k) + 1 from by ring]
    step fm
    apply stepStar_trans (ih a (c + 1) (e + 1))
    ring_nf; finish

theorem r4_chain : ∀ k, ∀ c d e,
    ⟨0, 0, c + k, d, e⟩ [fm]⊢* ⟨0, 0, c, d + k, e⟩ := by
  intro k; induction' k with k ih <;> intro c d e
  · exists 0
  · rw [show c + (k + 1) = (c + k) + 1 from by ring]
    step fm
    apply stepStar_trans (ih c (d + 1) e)
    ring_nf; finish

theorem r3r1_chain : ∀ k, ∀ a e,
    ⟨a + 1, k, 0, 0, e⟩ [fm]⊢* ⟨a + k + 1, 0, 0, 0, e + k⟩ := by
  intro k; induction' k with k ih <;> intro a e
  · ring_nf; finish
  · rw [show (k : ℕ) + 1 = k + 1 from rfl]
    step fm; step fm
    apply stepStar_trans (ih (a + 1) (e + 1))
    ring_nf; finish

theorem r5r2_round_b0 : ∀ d e,
    ⟨0, 0, 0, d + 3, e + 1⟩ [fm]⊢* ⟨0, 5, 0, d, e⟩ := by
  intro d e
  step fm; step fm; step fm; step fm; step fm
  ring_nf; finish

theorem r5r2_round_bS : ∀ b d e,
    ⟨0, b + 5, 0, d + 3, e + 1⟩ [fm]⊢* ⟨0, b + 10, 0, d, e⟩ := by
  intro b d e
  step fm; step fm; step fm; step fm; step fm
  ring_nf; finish

theorem r5r2_one_round : ∀ k, ∀ d e,
    ⟨0, 5 * k, 0, d + 3, e + 1⟩ [fm]⊢* ⟨0, 5 * k + 5, 0, d, e⟩ := by
  intro k; rcases k with _ | k <;> intro d e
  · exact r5r2_round_b0 d e
  · have := r5r2_round_bS (5 * k) d e
    rw [show 5 * k + 5 = 5 * (k + 1) from by ring,
        show 5 * k + 10 = 5 * (k + 1) + 5 from by ring] at this
    exact this

theorem r5r2_chain : ∀ k, ∀ d e,
    ⟨0, 0, 0, d + 3 * k, e + k⟩ [fm]⊢* ⟨0, 5 * k, 0, d, e⟩ := by
  intro k; induction' k with k ih <;> intro d e
  · exists 0
  · rw [show d + 3 * (k + 1) = (d + 3) + 3 * k from by ring,
        show e + (k + 1) = (e + 1) + k from by ring]
    apply stepStar_trans (ih (d + 3) (e + 1))
    rw [show 5 * (k + 1) = 5 * k + 5 from by ring]
    exact r5r2_one_round k d e

theorem leftover_r0 : ∀ b e,
    ⟨0, b + 1, 0, 0, e + 1⟩ [fm]⊢⁺ ⟨b + 3, 0, 0, 0, e + b⟩ := by
  intro b e
  step fm; step fm
  apply stepStar_trans (r3r1_chain b 2 e)
  ring_nf; finish

theorem leftover_r1 : ∀ b e,
    ⟨0, b + 5, 0, 1, e + 1⟩ [fm]⊢⁺ ⟨b + 8, 0, 0, 0, e + b + 6⟩ := by
  intro b e
  step fm; step fm; step fm; step fm; step fm
  apply stepStar_trans (r3r1_chain (b + 5) 2 (e + 1))
  ring_nf; finish

theorem leftover_r2 : ∀ b e,
    ⟨0, b + 5, 0, 2, e + 1⟩ [fm]⊢⁺ ⟨b + 9, 0, 0, 0, e + b + 8⟩ := by
  intro b e
  step fm; step fm; step fm; step fm; step fm; step fm
  apply stepStar_trans (r3r1_chain (b + 7) 1 (e + 1))
  ring_nf; finish

theorem main_mod0 (q e : ℕ) :
    ⟨3 * q + 3, 0, 0, 0, e⟩ [fm]⊢⁺ ⟨5 * q + 7, 0, 0, 0, e + 7 * q + 5⟩ := by
  have h1 : ⟨3 * q + 3, 0, 0, 0, e⟩ [fm]⊢* ⟨0, 0, 3 * q + 3, 0, e + (3 * q + 3)⟩ := by
    have := r3_chain (3 * q + 3) 0 0 e; simp only [Nat.zero_add] at this; exact this
  have h2 : ⟨0, 0, 3 * q + 3, 0, e + (3 * q + 3)⟩ [fm]⊢* ⟨0, 0, 0, 3 * q + 3, e + (3 * q + 3)⟩ := by
    have := r4_chain (3 * q + 3) 0 0 (e + (3 * q + 3)); simp only [Nat.zero_add] at this; exact this
  have h3 : ⟨0, 0, 0, 3 * q + 3, e + (3 * q + 3)⟩ [fm]⊢* ⟨0, 5 * (q + 1), 0, 0, e + 2 * q + 2⟩ := by
    have := r5r2_chain (q + 1) 0 (e + 2 * q + 2)
    rw [show 0 + 3 * (q + 1) = 3 * q + 3 from by ring,
        show e + 2 * q + 2 + (q + 1) = e + (3 * q + 3) from by ring] at this
    exact this
  have h4 : ⟨0, 5 * (q + 1), 0, 0, e + 2 * q + 2⟩ [fm]⊢⁺ ⟨5 * q + 7, 0, 0, 0, e + 7 * q + 5⟩ := by
    have := leftover_r0 (5 * q + 4) (e + 2 * q + 1)
    rw [show 5 * q + 4 + 1 = 5 * (q + 1) from by ring,
        show e + 2 * q + 1 + 1 = e + 2 * q + 2 from by ring,
        show 5 * q + 4 + 3 = 5 * q + 7 from by ring,
        show e + 2 * q + 1 + (5 * q + 4) = e + 7 * q + 5 from by ring] at this
    exact this
  exact stepStar_stepPlus_stepPlus h1
    (stepStar_stepPlus_stepPlus h2
      (stepStar_stepPlus_stepPlus h3 h4))

theorem main_mod1 (q e : ℕ) :
    ⟨3 * q + 4, 0, 0, 0, e⟩ [fm]⊢⁺ ⟨5 * q + 8, 0, 0, 0, e + 7 * q + 8⟩ := by
  have h1 : ⟨3 * q + 4, 0, 0, 0, e⟩ [fm]⊢* ⟨0, 0, 3 * q + 4, 0, e + (3 * q + 4)⟩ := by
    have := r3_chain (3 * q + 4) 0 0 e; simp only [Nat.zero_add] at this; exact this
  have h2 : ⟨0, 0, 3 * q + 4, 0, e + (3 * q + 4)⟩ [fm]⊢* ⟨0, 0, 0, 3 * q + 4, e + (3 * q + 4)⟩ := by
    have := r4_chain (3 * q + 4) 0 0 (e + (3 * q + 4)); simp only [Nat.zero_add] at this; exact this
  have h3 : ⟨0, 0, 0, 3 * q + 4, e + (3 * q + 4)⟩ [fm]⊢* ⟨0, 5 * (q + 1), 0, 1, e + 2 * q + 3⟩ := by
    have := r5r2_chain (q + 1) 1 (e + 2 * q + 3)
    rw [show 1 + 3 * (q + 1) = 3 * q + 4 from by ring,
        show e + 2 * q + 3 + (q + 1) = e + (3 * q + 4) from by ring] at this
    exact this
  have h4 : ⟨0, 5 * (q + 1), 0, 1, e + 2 * q + 3⟩ [fm]⊢⁺ ⟨5 * q + 8, 0, 0, 0, e + 7 * q + 8⟩ := by
    have := leftover_r1 (5 * q) (e + 2 * q + 2)
    rw [show 5 * q + 5 = 5 * (q + 1) from by ring,
        show e + 2 * q + 2 + 1 = e + 2 * q + 3 from by ring,
        show 5 * q + 8 = 5 * q + 8 from rfl,
        show e + 2 * q + 2 + (5 * q) + 6 = e + 7 * q + 8 from by ring] at this
    exact this
  exact stepStar_stepPlus_stepPlus h1
    (stepStar_stepPlus_stepPlus h2
      (stepStar_stepPlus_stepPlus h3 h4))

theorem main_mod2 (q e : ℕ) :
    ⟨3 * q + 5, 0, 0, 0, e⟩ [fm]⊢⁺ ⟨5 * q + 9, 0, 0, 0, e + 7 * q + 11⟩ := by
  have h1 : ⟨3 * q + 5, 0, 0, 0, e⟩ [fm]⊢* ⟨0, 0, 3 * q + 5, 0, e + (3 * q + 5)⟩ := by
    have := r3_chain (3 * q + 5) 0 0 e; simp only [Nat.zero_add] at this; exact this
  have h2 : ⟨0, 0, 3 * q + 5, 0, e + (3 * q + 5)⟩ [fm]⊢* ⟨0, 0, 0, 3 * q + 5, e + (3 * q + 5)⟩ := by
    have := r4_chain (3 * q + 5) 0 0 (e + (3 * q + 5)); simp only [Nat.zero_add] at this; exact this
  have h3 : ⟨0, 0, 0, 3 * q + 5, e + (3 * q + 5)⟩ [fm]⊢* ⟨0, 5 * (q + 1), 0, 2, e + 2 * q + 4⟩ := by
    have := r5r2_chain (q + 1) 2 (e + 2 * q + 4)
    rw [show 2 + 3 * (q + 1) = 3 * q + 5 from by ring,
        show e + 2 * q + 4 + (q + 1) = e + (3 * q + 5) from by ring] at this
    exact this
  have h4 : ⟨0, 5 * (q + 1), 0, 2, e + 2 * q + 4⟩ [fm]⊢⁺ ⟨5 * q + 9, 0, 0, 0, e + 7 * q + 11⟩ := by
    have := leftover_r2 (5 * q) (e + 2 * q + 3)
    rw [show 5 * q + 5 = 5 * (q + 1) from by ring,
        show e + 2 * q + 3 + 1 = e + 2 * q + 4 from by ring,
        show 5 * q + 9 = 5 * q + 9 from rfl,
        show e + 2 * q + 3 + (5 * q) + 8 = e + 7 * q + 11 from by ring] at this
    exact this
  exact stepStar_stepPlus_stepPlus h1
    (stepStar_stepPlus_stepPlus h2
      (stepStar_stepPlus_stepPlus h3 h4))

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨3, 0, 0, 0, 1⟩) (by execute fm 7)
  apply progress_nonhalt (fm := fm) (P := fun q ↦ ∃ a e, q = ⟨a + 3, 0, 0, 0, e⟩)
  · intro c ⟨a, e, hc⟩
    subst hc
    have hmod : a % 3 < 3 := Nat.mod_lt _ (by omega)
    have hdiv : 3 * (a / 3) + a % 3 = a := Nat.div_add_mod a 3
    rcases h : a % 3 with _ | _ | _ | n
    · -- a % 3 = 0: a = 3*(a/3), a+3 = 3*(a/3)+3
      refine ⟨⟨5 * (a / 3) + 7, 0, 0, 0, e + 7 * (a / 3) + 5⟩,
              ⟨5 * (a / 3) + 4, e + 7 * (a / 3) + 5, by ring_nf⟩, ?_⟩
      have ha : a + 3 = 3 * (a / 3) + 3 := by omega
      rw [ha]; exact main_mod0 (a / 3) e
    · -- a % 3 = 1: a = 3*(a/3)+1, a+3 = 3*(a/3)+4
      refine ⟨⟨5 * (a / 3) + 8, 0, 0, 0, e + 7 * (a / 3) + 8⟩,
              ⟨5 * (a / 3) + 5, e + 7 * (a / 3) + 8, by ring_nf⟩, ?_⟩
      have ha : a + 3 = 3 * (a / 3) + 4 := by omega
      rw [ha]; exact main_mod1 (a / 3) e
    · -- a % 3 = 2: a = 3*(a/3)+2, a+3 = 3*(a/3)+5
      refine ⟨⟨5 * (a / 3) + 9, 0, 0, 0, e + 7 * (a / 3) + 11⟩,
              ⟨5 * (a / 3) + 6, e + 7 * (a / 3) + 11, by ring_nf⟩, ?_⟩
      have ha : a + 3 = 3 * (a / 3) + 5 := by omega
      rw [ha]; exact main_mod2 (a / 3) e
    · omega
  · exact ⟨0, 1, by ring_nf⟩
