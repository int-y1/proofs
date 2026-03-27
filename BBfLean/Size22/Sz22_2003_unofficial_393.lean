import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #393: [2/15, 99/14, 325/2, 7/11, 33/13]

Vector representation:
```
 1 -1 -1  0  0  0
-1  2  0 -1  1  0
-1  0  2  0  0  1
 0  0  0  1 -1  0
 0  1  0  0  1 -1
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_393

def Q := ℕ × ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a, b+1, c+1, d, e, f⟩ => some ⟨a+1, b, c, d, e, f⟩
  | ⟨a+1, b, c, d+1, e, f⟩ => some ⟨a, b+2, c, d, e+1, f⟩
  | ⟨a+1, b, c, d, e, f⟩ => some ⟨a, b, c+2, d, e, f+1⟩
  | ⟨a, b, c, d, e+1, f⟩ => some ⟨a, b, c, d+1, e, f⟩
  | ⟨a, b, c, d, e, f+1⟩ => some ⟨a, b+1, c, d, e+1, f⟩
  | _ => none

private theorem q_star
    {a₁ a₂ b₁ b₂ c₁ c₂ d₁ d₂ e₁ e₂ f₁ f₂ g₁ g₂ h₁ h₂ i₁ i₂ j₁ j₂ k₁ k₂ l₁ l₂ : ℕ}
    (ha : a₁ = a₂) (hb : b₁ = b₂) (hc : c₁ = c₂) (hd : d₁ = d₂) (he : e₁ = e₂) (hf : f₁ = f₂)
    (hg : g₁ = g₂) (hh : h₁ = h₂) (hi : i₁ = i₂) (hj : j₁ = j₂) (hk : k₁ = k₂) (hl : l₁ = l₂)
    (h : (⟨a₁, b₁, c₁, d₁, e₁, f₁⟩ : Q) [fm]⊢* ⟨g₁, h₁, i₁, j₁, k₁, l₁⟩) :
    (⟨a₂, b₂, c₂, d₂, e₂, f₂⟩ : Q) [fm]⊢* ⟨g₂, h₂, i₂, j₂, k₂, l₂⟩ := by
  subst_vars; exact h

private theorem q_plus
    {a₁ a₂ b₁ b₂ c₁ c₂ d₁ d₂ e₁ e₂ f₁ f₂ g₁ g₂ h₁ h₂ i₁ i₂ j₁ j₂ k₁ k₂ l₁ l₂ : ℕ}
    (ha : a₁ = a₂) (hb : b₁ = b₂) (hc : c₁ = c₂) (hd : d₁ = d₂) (he : e₁ = e₂) (hf : f₁ = f₂)
    (hg : g₁ = g₂) (hh : h₁ = h₂) (hi : i₁ = i₂) (hj : j₁ = j₂) (hk : k₁ = k₂) (hl : l₁ = l₂)
    (h : (⟨a₁, b₁, c₁, d₁, e₁, f₁⟩ : Q) [fm]⊢⁺ ⟨g₁, h₁, i₁, j₁, k₁, l₁⟩) :
    (⟨a₂, b₂, c₂, d₂, e₂, f₂⟩ : Q) [fm]⊢⁺ ⟨g₂, h₂, i₂, j₂, k₂, l₂⟩ := by
  subst_vars; exact h

private theorem q_eq {a₁ a₂ b₁ b₂ c₁ c₂ d₁ d₂ e₁ e₂ f₁ f₂ : ℕ}
    (ha : a₁ = a₂) (hb : b₁ = b₂) (hc : c₁ = c₂) (hd : d₁ = d₂) (he : e₁ = e₂) (hf : f₁ = f₂) :
    (⟨a₁, b₁, c₁, d₁, e₁, f₁⟩ : Q) = ⟨a₂, b₂, c₂, d₂, e₂, f₂⟩ := by
  subst_vars; rfl

private theorem r4_chain : ⟨0, 0, c, d, e + k, f⟩ [fm]⊢* (⟨0, 0, c, d + k, e, f⟩ : Q) := by
  have go : ∀ k d, ⟨0, 0, c, d, e + k, f⟩ [fm]⊢* (⟨0, 0, c, d + k, e, f⟩ : Q) := by
    intro k; induction' k with k ih <;> intro d
    · exists 0
    rw [show e + (k + 1) = (e + k) + 1 from by ring]
    step fm; apply stepStar_trans (ih _); ring_nf; finish
  exact go k d

private theorem r3_chain : ⟨a + k, 0, c, 0, e, f⟩ [fm]⊢* (⟨a, 0, c + 2 * k, 0, e, f + k⟩ : Q) := by
  have go : ∀ k c f, ⟨a + k, 0, c, 0, e, f⟩ [fm]⊢* (⟨a, 0, c + 2 * k, 0, e, f + k⟩ : Q) := by
    intro k; induction' k with k ih <;> intro c f
    · simp; exists 0
    rw [show a + (k + 1) = (a + k) + 1 from by ring]
    step fm; apply stepStar_trans (ih _ _); ring_nf; finish
  exact go k c f

private theorem inner_loop : ⟨1, 0, c + 2 * k, d + k, e, f⟩ [fm]⊢* (⟨k + 1, 0, c, d, e + k, f⟩ : Q) := by
  have go : ∀ k c d, ⟨1, 0, c + 2 * k, d + k, e, f⟩ [fm]⊢* (⟨k + 1, 0, c, d, e + k, f⟩ : Q) := by
    intro k; induction' k with k ih <;> intro c d
    · simp; exists 0
    rw [show c + 2 * (k + 1) = (c + 2) + 2 * k from by ring,
        show d + (k + 1) = (d + 1) + k from by ring]
    apply stepStar_trans (ih _ _)
    rw [show k + 1 = (k + 0) + 1 from by ring]
    step fm; step fm; step fm; ring_nf; finish
  exact go k c d

private theorem r2_c0_chain : ⟨a + k, b, 0, d + k, e, f⟩ [fm]⊢* (⟨a, b + 2 * k, 0, d, e + k, f⟩ : Q) := by
  have go : ∀ k b e, ⟨a + k, b, 0, d + k, e, f⟩ [fm]⊢* (⟨a, b + 2 * k, 0, d, e + k, f⟩ : Q) := by
    intro k; induction' k with k ih <;> intro b e
    · simp; exists 0
    rw [show a + (k + 1) = (a + k) + 1 from by ring,
        show d + (k + 1) = (d + k) + 1 from by ring]
    step fm; apply stepStar_trans (ih _ _); ring_nf; finish
  exact go k b e

private theorem r3r1_loop : ⟨a + 1, b + 2 * k, 0, 0, e, f⟩ [fm]⊢* (⟨a + k + 1, b, 0, 0, e, f + k⟩ : Q) := by
  have go : ∀ k b a f, ⟨a + 1, b + 2 * k, 0, 0, e, f⟩ [fm]⊢* (⟨a + k + 1, b, 0, 0, e, f + k⟩ : Q) := by
    intro k; induction' k with k ih <;> intro b a f
    · simp; exists 0
    rw [show b + 2 * (k + 1) = (b + 2) + 2 * k from by ring]
    apply stepStar_trans (ih (b + 2) a f)
    rw [show a + k + 1 = (a + k + 0) + 1 from by ring]
    step fm; step fm; step fm; ring_nf; finish
  exact go k b a f

private theorem cycle_even (m f : ℕ) :
    ⟨0, 0, 2 * m + 3, 2 * m + 1, 0, f + 1⟩ [fm]⊢⁺ (⟨0, 0, 2 * m + 4, 2 * m + 2, 0, f + 2 * m + 2⟩ : Q) := by
  step fm; step fm
  -- inner_loop: (1,0,2m+2,2m+1,1,f) -> (m+2,0,0,m,m+2,f)
  have h1 : (⟨1, 0, 2*m+2, 2*m+1, 1, f⟩ : Q) [fm]⊢* ⟨m+2, 0, 0, m, m+2, f⟩ :=
    q_star rfl rfl (by omega) (by omega) rfl rfl (by omega) rfl rfl rfl (by omega) rfl
      (@inner_loop 0 (m+1) m 1 f)
  apply stepStar_trans h1
  -- r2_c0_chain: (m+2,0,0,m,m+2,f) -> (2,2m,0,0,2m+2,f)
  have h2 : (⟨m+2, 0, 0, m, m+2, f⟩ : Q) [fm]⊢* ⟨2, 2*m, 0, 0, 2*m+2, f⟩ :=
    q_star (by omega) rfl rfl (by omega) rfl rfl rfl (by omega) rfl rfl (by omega) rfl
      (@r2_c0_chain 2 m 0 0 (m+2) f)
  apply stepStar_trans h2
  -- r3r1_loop: (2,2m,0,0,2m+2,f) -> (m+2,0,0,0,2m+2,f+m)
  have h3 : (⟨2, 2*m, 0, 0, 2*m+2, f⟩ : Q) [fm]⊢* ⟨m+2, 0, 0, 0, 2*m+2, f+m⟩ :=
    q_star (by omega) (by omega) rfl rfl rfl rfl (by omega) rfl rfl rfl rfl (by omega)
      (@r3r1_loop 1 0 m (2*m+2) f)
  apply stepStar_trans h3
  -- r3_chain: (m+2,0,0,0,2m+2,f+m) -> (0,0,2m+4,0,2m+2,f+2m+2)
  have h4 : (⟨m+2, 0, 0, 0, 2*m+2, f+m⟩ : Q) [fm]⊢* ⟨0, 0, 2*m+4, 0, 2*m+2, f+2*m+2⟩ :=
    q_star (by omega) rfl rfl rfl rfl (by omega) rfl rfl (by omega) rfl rfl (by omega)
      (@r3_chain 0 (m+2) 0 (2*m+2) (f+m))
  apply stepStar_trans h4
  -- r4_chain: (0,0,2m+4,0,2m+2,f+2m+2) -> (0,0,2m+4,2m+2,0,f+2m+2)
  exact q_star rfl rfl rfl rfl (by omega) rfl rfl rfl rfl (by omega) rfl rfl
    (@r4_chain (2*m+4) 0 0 (2*m+2) (f+2*m+2))

private theorem cycle_odd (m f : ℕ) :
    ⟨0, 0, 2 * m + 4, 2 * m + 2, 0, f + 1⟩ [fm]⊢⁺ (⟨0, 0, 2 * m + 5, 2 * m + 3, 0, f + 2 * m + 3⟩ : Q) := by
  step fm; step fm
  -- inner_loop: (1,0,2m+3,2m+2,1,f) -> (m+2,0,1,m+1,m+2,f)
  have h1 : (⟨1, 0, 2*m+3, 2*m+2, 1, f⟩ : Q) [fm]⊢* ⟨m+2, 0, 1, m+1, m+2, f⟩ :=
    q_star rfl rfl (by omega) (by omega) rfl rfl (by omega) rfl rfl rfl (by omega) rfl
      (@inner_loop 1 (m+1) (m+1) 1 f)
  apply stepStar_trans h1
  -- R2+R1: (m+2,0,1,m+1,m+2,f) -> (m+2,1,0,m,m+3,f)
  have hr : (⟨m+2, 0, 1, m+1, m+2, f⟩ : Q) [fm]⊢* ⟨m+2, 1, 0, m, m+3, f⟩ := by
    rw [show m + 2 = (m + 1 + 0) + 1 from by omega, show m + 1 = (m + 0) + 1 from by omega]
    step fm; step fm; ring_nf; finish
  apply stepStar_trans hr
  -- r2_c0_chain: (m+2,1,0,m,m+3,f) -> (2,2m+1,0,0,2m+3,f)
  have h2 : (⟨m+2, 1, 0, m, m+3, f⟩ : Q) [fm]⊢* ⟨2, 2*m+1, 0, 0, 2*m+3, f⟩ :=
    q_star (by omega) rfl rfl (by omega) rfl rfl rfl (by omega) rfl rfl (by omega) rfl
      (@r2_c0_chain 2 m 1 0 (m+3) f)
  apply stepStar_trans h2
  -- r3r1_loop: (2,2m+1,0,0,2m+3,f) -> (m+2,1,0,0,2m+3,f+m)
  have h3 : (⟨2, 2*m+1, 0, 0, 2*m+3, f⟩ : Q) [fm]⊢* ⟨m+2, 1, 0, 0, 2*m+3, f+m⟩ :=
    q_star (by omega) (by omega) rfl rfl rfl rfl (by omega) rfl rfl rfl rfl (by omega)
      (@r3r1_loop 1 1 m (2*m+3) f)
  apply stepStar_trans h3
  -- R3+R1+R3: (m+2,1,0,0,2m+3,f+m) -> (m+1,0,3,0,2m+3,f+m+2)
  have hc : (⟨m+2, 1, 0, 0, 2*m+3, f+m⟩ : Q) [fm]⊢* ⟨m+1, 0, 3, 0, 2*m+3, f+m+2⟩ := by
    rw [show m + 2 = (m + 0 + 1) + 1 from by omega, show (1 : ℕ) = 0 + 1 from rfl]
    step fm; step fm; step fm; ring_nf; finish
  apply stepStar_trans hc
  -- r3_chain: (m+1,0,3,0,2m+3,f+m+2) -> (0,0,2m+5,0,2m+3,f+2m+3)
  have h4 : (⟨m+1, 0, 3, 0, 2*m+3, f+m+2⟩ : Q) [fm]⊢* ⟨0, 0, 2*m+5, 0, 2*m+3, f+2*m+3⟩ :=
    q_star (by omega) rfl rfl rfl rfl (by omega) rfl rfl (by omega) rfl rfl (by omega)
      (@r3_chain 0 (m+1) 3 (2*m+3) (f+m+2))
  apply stepStar_trans h4
  -- r4_chain: (0,0,2m+5,0,2m+3,f+2m+3) -> (0,0,2m+5,2m+3,0,f+2m+3)
  exact q_star rfl rfl rfl rfl (by omega) rfl rfl rfl rfl (by omega) rfl rfl
    (@r4_chain (2*m+5) 0 0 (2*m+3) (f+2*m+3))

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := (⟨0, 0, 3, 1, 0, 1⟩ : Q))
  · execute fm 5
  apply progress_nonhalt (fm := fm)
    (P := fun q ↦ ∃ n f, q = (⟨0, 0, n + 3, n + 1, 0, f + 1⟩ : Q))
  · intro c ⟨n, f, hq⟩; subst hq
    rcases Nat.even_or_odd n with ⟨m, hm⟩ | ⟨m, hm⟩
    · subst hm
      exact ⟨_, ⟨2*m+1, f+2*m+1, q_eq rfl rfl (by omega) (by omega) rfl (by omega)⟩,
        q_plus rfl rfl (by omega) (by omega) rfl rfl rfl rfl rfl rfl rfl rfl (cycle_even m f)⟩
    · subst hm
      exact ⟨_, ⟨2*m+2, f+2*m+2, q_eq rfl rfl (by omega) (by omega) rfl (by omega)⟩,
        q_plus rfl rfl (by omega) (by omega) rfl rfl rfl rfl rfl rfl rfl rfl (cycle_odd m f)⟩
  · exact ⟨0, 0, rfl⟩
