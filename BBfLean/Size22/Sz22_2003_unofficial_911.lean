import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #911: [4/15, 3/14, 55/2, 49/5, 10/11]

Vector representation:
```
 2 -1 -1  0  0
-1  1  0 -1  0
-1  0  1  0  1
 0  0 -1  2  0
 1  0  1  0 -1
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_911

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a, b+1, c+1, d, e⟩ => some ⟨a+2, b, c, d, e⟩
  | ⟨a+1, b, c, d+1, e⟩ => some ⟨a, b+1, c, d, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b, c+1, d, e+1⟩
  | ⟨a, b, c+1, d, e⟩ => some ⟨a, b, c, d+2, e⟩
  | ⟨a, b, c, d, e+1⟩ => some ⟨a+1, b, c+1, d, e⟩
  | _ => none

theorem r3_chain : ∀ k c e, ⟨k, (0 : ℕ), c, (0 : ℕ), e⟩ [fm]⊢* ⟨0, 0, c + k, 0, e + k⟩ := by
  intro k; induction k with
  | zero => intro c e; simp; exists 0
  | succ k ih =>
    intro c e; step fm
    apply stepStar_trans (ih (c + 1) (e + 1))
    ring_nf; finish

theorem r4_chain : ∀ k d e, ⟨(0 : ℕ), (0 : ℕ), k, d, e⟩ [fm]⊢* ⟨0, 0, 0, d + 2 * k, e⟩ := by
  intro k; induction k with
  | zero => intro d e; simp; exists 0
  | succ k ih =>
    intro d e; step fm
    apply stepStar_trans (ih (d + 2) e)
    ring_nf; finish

theorem r3r1_chain : ∀ b a e, ⟨a + 1, b + 1, (0 : ℕ), (0 : ℕ), e⟩ [fm]⊢*
    ⟨a + b + 2, 0, 0, 0, e + b + 1⟩ := by
  intro b; induction b with
  | zero =>
    intro a e; step fm; step fm
    ring_nf; finish
  | succ b ih =>
    intro a e
    step fm; step fm
    apply stepStar_trans (ih (a + 1) (e + 1))
    ring_nf; finish

theorem accum_round_zero : ∀ d e,
    ⟨(0 : ℕ), (0 : ℕ), (0 : ℕ), d + 3, e + 1⟩ [fm]⊢* ⟨0, 2, 0, d, e⟩ := by
  intro d e
  step fm; step fm; step fm; step fm; step fm
  ring_nf; finish

theorem accum_round_pos : ∀ b d e,
    ⟨(0 : ℕ), 2 * b + 2, (0 : ℕ), d + 3, e + 1⟩ [fm]⊢* ⟨0, 2 * b + 4, 0, d, e⟩ := by
  intro b d e
  rw [show 2 * b + 2 = (2 * b + 1) + 1 from by ring]
  step fm; step fm; step fm; step fm; step fm
  ring_nf; finish

theorem accum_chain : ∀ k d e,
    ⟨(0 : ℕ), (0 : ℕ), (0 : ℕ), d + 3 * (k + 1), e + (k + 1)⟩ [fm]⊢*
    ⟨0, 2 * (k + 1), 0, d, e⟩ := by
  intro k; induction k with
  | zero =>
    intro d e
    rw [show d + 3 * (0 + 1) = d + 3 from by ring,
        show e + (0 + 1) = e + 1 from by ring]
    apply stepStar_trans (accum_round_zero d e)
    ring_nf; finish
  | succ k ih =>
    intro d e
    rw [show d + 3 * (k + 1 + 1) = (d + 3 * (k + 1)) + 3 from by ring,
        show e + (k + 1 + 1) = (e + (k + 1)) + 1 from by ring]
    apply stepStar_trans (accum_round_zero (d + 3 * (k + 1)) (e + (k + 1)))
    rw [show (2 : ℕ) = 2 * 0 + 2 from by ring]
    apply stepStar_trans (accum_pos_chain k 0 d e)
    ring_nf; finish
  where
    accum_pos_chain : ∀ k b d e,
        ⟨(0 : ℕ), 2 * b + 2, (0 : ℕ), d + 3 * (k + 1), e + (k + 1)⟩ [fm]⊢*
        ⟨0, 2 * b + 2 + 2 * (k + 1), 0, d, e⟩ := by
      intro k; induction k with
      | zero =>
        intro b d e
        rw [show d + 3 * (0 + 1) = d + 3 from by ring,
            show e + (0 + 1) = e + 1 from by ring]
        apply stepStar_trans (accum_round_pos b d e)
        ring_nf; finish
      | succ k ih =>
        intro b d e
        rw [show d + 3 * (k + 1 + 1) = (d + 3 * (k + 1)) + 3 from by ring,
            show e + (k + 1 + 1) = (e + (k + 1)) + 1 from by ring]
        apply stepStar_trans (accum_round_pos b (d + 3 * (k + 1)) (e + (k + 1)))
        rw [show 2 * b + 4 = 2 * (b + 1) + 2 from by ring]
        apply stepStar_trans (ih (b + 1) d e)
        ring_nf; finish

theorem tail_d0 : ∀ k e,
    ⟨(0 : ℕ), 2 * (k + 1), (0 : ℕ), (0 : ℕ), e + 1⟩ [fm]⊢*
    ⟨2 * k + 4, 0, 0, 0, e + 2 * k + 1⟩ := by
  intro k e
  rw [show 2 * (k + 1) = (2 * k + 1) + 1 from by ring]
  step fm; step fm
  rw [show 2 * k + 1 = (2 * k) + 1 from by ring]
  apply stepStar_trans (r3r1_chain (2 * k) 2 e)
  ring_nf; finish

theorem tail_d1 : ∀ k e,
    ⟨(0 : ℕ), 2 * (k + 1), (0 : ℕ), (1 : ℕ), e + 1⟩ [fm]⊢*
    ⟨2 * k + 4, 0, 0, 0, e + 2 * k + 2⟩ := by
  intro k e
  rw [show 2 * (k + 1) = (2 * k + 1) + 1 from by ring]
  step fm; step fm; step fm
  rw [show 2 * k + 2 = (2 * k + 1) + 1 from by ring]
  apply stepStar_trans (r3r1_chain (2 * k + 1) 1 e)
  ring_nf; finish

theorem tail_d2 : ∀ k e,
    ⟨(0 : ℕ), 2 * (k + 1), (0 : ℕ), (2 : ℕ), e + 1⟩ [fm]⊢*
    ⟨2 * k + 4, 0, 0, 0, e + 2 * k + 3⟩ := by
  intro k e
  rw [show 2 * (k + 1) = (2 * k + 1) + 1 from by ring]
  step fm; step fm; step fm; step fm
  rw [show 2 * k + 3 = (2 * k + 2) + 1 from by ring]
  apply stepStar_trans (r3r1_chain (2 * k + 2) 0 e)
  ring_nf; finish

theorem trans_mod0 : ∀ m e,
    ⟨3 * m + 2, (0 : ℕ), (0 : ℕ), (0 : ℕ), e + 1⟩ [fm]⊢⁺
    ⟨4 * m + 4, 0, 0, 0, e + 5 * m + 3⟩ := by
  intro m e
  step fm
  apply stepStar_trans (r3_chain (3 * m + 1) 1 (e + 2))
  rw [show 1 + (3 * m + 1) = 3 * m + 2 from by ring,
      show e + 2 + (3 * m + 1) = e + 3 * m + 3 from by ring]
  apply stepStar_trans (r4_chain (3 * m + 2) 0 (e + 3 * m + 3))
  rw [show 0 + 2 * (3 * m + 2) = 6 * m + 4 from by ring,
      show 6 * m + 4 = 1 + 3 * (2 * m + 1) from by ring,
      show e + 3 * m + 3 = (e + m + 2) + (2 * m + 1) from by ring]
  apply stepStar_trans (accum_chain (2 * m) 1 (e + m + 2))
  rw [show 2 * (2 * m + 1) = 2 * (2 * m + 1) from rfl,
      show e + m + 2 = (e + m + 1) + 1 from by ring]
  apply stepStar_trans (tail_d1 (2 * m) (e + m + 1))
  rw [show 2 * (2 * m) + 4 = 4 * m + 4 from by ring,
      show e + m + 1 + 2 * (2 * m) + 2 = e + 5 * m + 3 from by ring]
  finish

theorem trans_mod1 : ∀ m e,
    ⟨3 * m + 3, (0 : ℕ), (0 : ℕ), (0 : ℕ), e + 1⟩ [fm]⊢⁺
    ⟨4 * m + 6, 0, 0, 0, e + 5 * m + 4⟩ := by
  intro m e
  step fm
  apply stepStar_trans (r3_chain (3 * m + 2) 1 (e + 2))
  rw [show 1 + (3 * m + 2) = 3 * m + 3 from by ring,
      show e + 2 + (3 * m + 2) = e + 3 * m + 4 from by ring]
  apply stepStar_trans (r4_chain (3 * m + 3) 0 (e + 3 * m + 4))
  rw [show 0 + 2 * (3 * m + 3) = 6 * m + 6 from by ring,
      show 6 * m + 6 = 0 + 3 * (2 * m + 2) from by ring,
      show e + 3 * m + 4 = (e + m + 2) + (2 * m + 2) from by ring]
  apply stepStar_trans (accum_chain (2 * m + 1) 0 (e + m + 2))
  rw [show 2 * (2 * m + 2) = 2 * (2 * m + 2) from rfl,
      show e + m + 2 = (e + m + 1) + 1 from by ring]
  apply stepStar_trans (tail_d0 (2 * m + 1) (e + m + 1))
  rw [show 2 * (2 * m + 1) + 4 = 4 * m + 6 from by ring,
      show e + m + 1 + 2 * (2 * m + 1) + 1 = e + 5 * m + 4 from by ring]
  finish

theorem trans_mod2 : ∀ m e,
    ⟨3 * m + 4, (0 : ℕ), (0 : ℕ), (0 : ℕ), e + 1⟩ [fm]⊢⁺
    ⟨4 * m + 6, 0, 0, 0, e + 5 * m + 7⟩ := by
  intro m e
  step fm
  apply stepStar_trans (r3_chain (3 * m + 3) 1 (e + 2))
  rw [show 1 + (3 * m + 3) = 3 * m + 4 from by ring,
      show e + 2 + (3 * m + 3) = e + 3 * m + 5 from by ring]
  apply stepStar_trans (r4_chain (3 * m + 4) 0 (e + 3 * m + 5))
  rw [show 0 + 2 * (3 * m + 4) = 6 * m + 8 from by ring,
      show 6 * m + 8 = 2 + 3 * (2 * m + 2) from by ring,
      show e + 3 * m + 5 = (e + m + 3) + (2 * m + 2) from by ring]
  apply stepStar_trans (accum_chain (2 * m + 1) 2 (e + m + 3))
  rw [show 2 * (2 * m + 2) = 2 * (2 * m + 2) from rfl,
      show e + m + 3 = (e + m + 2) + 1 from by ring]
  apply stepStar_trans (tail_d2 (2 * m + 1) (e + m + 2))
  rw [show 2 * (2 * m + 1) + 4 = 4 * m + 6 from by ring,
      show e + m + 2 + 2 * (2 * m + 1) + 3 = e + 5 * m + 7 from by ring]
  finish

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨2, 0, 0, 0, 1⟩) (by execute fm 8)
  apply progress_nonhalt (fm := fm)
    (P := fun q ↦ ∃ a e, q = ⟨a + 2, 0, 0, 0, e + 1⟩)
  · intro q ⟨a, e, hq⟩; subst hq
    obtain ⟨m, r, hr, rfl⟩ : ∃ m r, r < 3 ∧ a = 3 * m + r :=
      ⟨a / 3, a % 3, Nat.mod_lt _ (by omega), by omega⟩
    rcases (show r = 0 ∨ r = 1 ∨ r = 2 from by omega) with rfl | rfl | rfl
    · exact ⟨⟨4 * m + 4, 0, 0, 0, e + 5 * m + 3⟩,
        ⟨4 * m + 2, e + 5 * m + 2, by ring_nf⟩, trans_mod0 m e⟩
    · exact ⟨⟨4 * m + 6, 0, 0, 0, e + 5 * m + 4⟩,
        ⟨4 * m + 4, e + 5 * m + 3, by ring_nf⟩, trans_mod1 m e⟩
    · exact ⟨⟨4 * m + 6, 0, 0, 0, e + 5 * m + 7⟩,
        ⟨4 * m + 4, e + 5 * m + 6, by ring_nf⟩, trans_mod2 m e⟩
  · exact ⟨0, 0, rfl⟩

end Sz22_2003_unofficial_911
