import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #1111: [5/6, 4/35, 539/2, 3/7, 28/11]

Vector representation:
```
-1 -1  1  0  0
 2  0 -1 -1  0
-1  0  0  2  1
 0  1  0 -1  0
 2  0  0  1 -1
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_1111

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a+1, b+1, c, d, e⟩ => some ⟨a, b, c+1, d, e⟩
  | ⟨a, b, c+1, d+1, e⟩ => some ⟨a+2, b, c, d, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b, c, d+2, e+1⟩
  | ⟨a, b, c, d+1, e⟩ => some ⟨a, b+1, c, d, e⟩
  | ⟨a, b, c, d, e+1⟩ => some ⟨a+2, b, c, d+1, e⟩
  | _ => none

theorem r4_drain : ∀ k, ∀ b e, ⟨0, b, 0, k, e⟩ [fm]⊢* ⟨0, b + k, 0, 0, e⟩ := by
  intro k; induction' k with k ih <;> intro b e
  · exists 0
  · step fm; apply stepStar_trans (ih (b + 1) e); ring_nf; finish

theorem r3_drain : ∀ k, ∀ d e, ⟨k, 0, 0, d, e⟩ [fm]⊢* ⟨0, 0, 0, d + 2 * k, e + k⟩ := by
  intro k; induction' k with k ih <;> intro d e
  · exists 0
  · step fm; apply stepStar_trans (ih (d + 2) (e + 1)); ring_nf; finish

theorem one_round (b c e : ℕ) : ⟨0, b + 4, c, 0, e + 1⟩ [fm]⊢* ⟨0, b, c + 3, 0, e⟩ := by
  refine ⟨6, ?_⟩; cases c <;> rfl

theorem multi_round : ∀ k, ∀ b c e, ⟨0, b + 4 * k, c, 0, e + k⟩ [fm]⊢* ⟨0, b, c + 3 * k, 0, e⟩ := by
  intro k; induction' k with k ih <;> intro b c e
  · exists 0
  · rw [show b + 4 * (k + 1) = (b + 4) + 4 * k from by ring,
        show e + (k + 1) = (e + 1) + k from by ring]
    apply stepStar_trans (ih (b + 4) c (e + 1))
    apply stepStar_trans (one_round b (c + 3 * k) e); ring_nf; finish

theorem chain_even : ∀ m, ∀ a e, ⟨a + 1, 0, 2 * (m + 1), 0, e⟩ [fm]⊢* ⟨a + 3 * m + 4, 0, 0, 0, e + m + 1⟩ := by
  intro m; induction' m with m ih <;> intro a e
  · step fm; step fm; step fm; finish
  · rw [show 2 * (m + 1 + 1) = 2 * (m + 1) + 2 from by ring]
    step fm; step fm; step fm
    rw [show a + 4 = (a + 3) + 1 from by ring]
    apply stepStar_trans (ih (a + 3) (e + 1)); ring_nf; finish

theorem chain_odd : ∀ m, ∀ a e, ⟨a + 1, 0, 2 * m + 1, 0, e⟩ [fm]⊢* ⟨a + 3 * m + 2, 0, 0, 1, e + m + 1⟩ := by
  intro m; induction' m with m ih <;> intro a e
  · step fm; step fm; finish
  · rw [show 2 * (m + 1) + 1 = 2 * m + 3 from by ring]
    step fm; step fm; step fm
    rw [show a + 4 = (a + 3) + 1 from by ring]
    apply stepStar_trans (ih (a + 3) (e + 1)); ring_nf; finish

theorem tail0 (c f : ℕ) : ⟨0, 0, c + 1, 0, f + 1⟩ [fm]⊢* ⟨4, 0, c, 0, f⟩ := by
  refine ⟨2, ?_⟩; cases c <;> rfl

theorem tail1 (c f : ℕ) : ⟨0, 1, c, 0, f + 1⟩ [fm]⊢* ⟨3, 0, c, 0, f⟩ := by
  refine ⟨3, ?_⟩; cases c <;> rfl

theorem tail2 (c f : ℕ) : ⟨0, 2, c, 0, f + 1⟩ [fm]⊢* ⟨2, 0, c + 1, 0, f⟩ := by
  refine ⟨4, ?_⟩; cases c <;> rfl

theorem tail3 (c f : ℕ) : ⟨0, 3, c, 0, f + 1⟩ [fm]⊢* ⟨1, 0, c + 2, 0, f⟩ := by
  refine ⟨5, ?_⟩; cases c <;> rfl

theorem case_d1 : ⟨0, 0, 0, 1, f + 1⟩ [fm]⊢⁺ ⟨0, 0, 0, 6, f + 3⟩ := by
  step fm; step fm; step fm; step fm
  exact r3_drain 3 0 f

theorem case_d2 : ⟨0, 0, 0, 2, f + 1⟩ [fm]⊢⁺ ⟨0, 0, 0, 7, f + 4⟩ := by
  step fm; step fm; step fm; step fm; step fm; step fm
  rw [show (2 : ℕ) = 1 + 1 from by ring, show (1 : ℕ) = 2 * 0 + 1 from by ring]
  apply stepStar_trans (chain_odd 0 1 f)
  exact r3_drain 3 1 (f + 1)

theorem case_d3 : ⟨0, 0, 0, 3, f + 1⟩ [fm]⊢⁺ ⟨0, 0, 0, 8, f + 5⟩ := by
  step fm; step fm; step fm; step fm; step fm; step fm; step fm; step fm
  rw [show (1 : ℕ) = 0 + 1 from by ring, show (2 : ℕ) = 2 * (0 + 1) from by ring]
  apply stepStar_trans (chain_even 0 0 f)
  exact r3_drain 4 0 (f + 1)

theorem case_8m1 (m : ℕ) (hm : m ≥ 1) :
    ⟨0, 0, 0, 8 * m + 1, 2 * m + 1 + f⟩ [fm]⊢⁺ ⟨0, 0, 0, 18 * m + 6, f + 12 * m + 3⟩ := by
  obtain ⟨m, rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
  step fm
  apply stepStar_trans (r4_drain (8 * (m + 1)) 1 (2 * (m + 1) + 1 + f))
  rw [show 1 + 8 * (m + 1) = 1 + 4 * (2 * (m + 1)) from by ring,
      show 2 * (m + 1) + 1 + f = (f + 1) + 2 * (m + 1) from by ring]
  apply stepStar_trans (multi_round (2 * (m + 1)) 1 0 (f + 1))
  apply stepStar_trans (tail1 (0 + 3 * (2 * (m + 1))) f)
  rw [show (3 : ℕ) = 2 + 1 from by ring,
      show 0 + 3 * (2 * (m + 1)) = 2 * ((3 * (m + 1) - 1) + 1) from by omega]
  apply stepStar_trans (chain_even (3 * (m + 1) - 1) 2 f)
  rw [show 2 + 3 * (3 * (m + 1) - 1) + 4 = 9 * (m + 1) + 3 from by omega]
  apply stepStar_trans (r3_drain (9 * (m + 1) + 3) 0 (f + (3 * (m + 1) - 1) + 1))
  rw [show 3 * (m + 1) - 1 = 3 * m + 2 from by omega]
  ring_nf; finish

theorem case_8m2 (m : ℕ) :
    ⟨0, 0, 0, 8 * m + 2, 2 * m + 1 + f⟩ [fm]⊢⁺ ⟨0, 0, 0, 18 * m + 7, f + 12 * m + 4⟩ := by
  step fm
  apply stepStar_trans (r4_drain (8 * m + 1) 1 (2 * m + 1 + f))
  rw [show 1 + (8 * m + 1) = 2 + 4 * (2 * m) from by ring,
      show 2 * m + 1 + f = (f + 1) + 2 * m from by ring]
  apply stepStar_trans (multi_round (2 * m) 2 0 (f + 1))
  apply stepStar_trans (tail2 (0 + 3 * (2 * m)) f)
  rw [show (2 : ℕ) = 1 + 1 from by ring,
      show 0 + 3 * (2 * m) + 1 = 2 * (3 * m) + 1 from by ring]
  apply stepStar_trans (chain_odd (3 * m) 1 f)
  rw [show 1 + 3 * (3 * m) + 2 = 9 * m + 3 from by ring]
  apply stepStar_trans (r3_drain (9 * m + 3) 1 (f + 3 * m + 1))
  ring_nf; finish

theorem case_8m3 (m : ℕ) :
    ⟨0, 0, 0, 8 * m + 3, 2 * m + 1 + f⟩ [fm]⊢⁺ ⟨0, 0, 0, 18 * m + 8, f + 12 * m + 5⟩ := by
  step fm
  apply stepStar_trans (r4_drain (8 * m + 2) 1 (2 * m + 1 + f))
  rw [show 1 + (8 * m + 2) = 3 + 4 * (2 * m) from by ring,
      show 2 * m + 1 + f = (f + 1) + 2 * m from by ring]
  apply stepStar_trans (multi_round (2 * m) 3 0 (f + 1))
  apply stepStar_trans (tail3 (0 + 3 * (2 * m)) f)
  rw [show (1 : ℕ) = 0 + 1 from by ring,
      show 0 + 3 * (2 * m) + 2 = 2 * ((3 * m) + 1) from by ring]
  apply stepStar_trans (chain_even (3 * m) 0 f)
  rw [show 0 + 3 * (3 * m) + 4 = 9 * m + 4 from by ring]
  apply stepStar_trans (r3_drain (9 * m + 4) 0 (f + 3 * m + 1))
  ring_nf; finish

theorem case_8m4 (m : ℕ) :
    ⟨0, 0, 0, 8 * m + 4, 2 * m + 2 + f⟩ [fm]⊢⁺ ⟨0, 0, 0, 18 * m + 14, f + 12 * m + 8⟩ := by
  step fm
  apply stepStar_trans (r4_drain (8 * m + 3) 1 (2 * m + 2 + f))
  rw [show 1 + (8 * m + 3) = 0 + 4 * (2 * m + 1) from by ring,
      show 2 * m + 2 + f = (f + 1) + (2 * m + 1) from by ring]
  apply stepStar_trans (multi_round (2 * m + 1) 0 0 (f + 1))
  rw [show 0 + 3 * (2 * m + 1) = 3 * (2 * m + 1) from by ring]
  apply stepStar_trans (tail0 (3 * (2 * m + 1) - 1) f)
  rw [show (4 : ℕ) = 3 + 1 from by ring,
      show 3 * (2 * m + 1) - 1 = 2 * ((3 * m) + 1) from by omega]
  apply stepStar_trans (chain_even (3 * m) 3 f)
  rw [show 3 + 3 * (3 * m) + 4 = 9 * m + 7 from by ring]
  apply stepStar_trans (r3_drain (9 * m + 7) 0 (f + 3 * m + 1))
  ring_nf; finish

theorem case_8m5 (m : ℕ) :
    ⟨0, 0, 0, 8 * m + 5, 2 * m + 2 + f⟩ [fm]⊢⁺ ⟨0, 0, 0, 18 * m + 15, f + 12 * m + 9⟩ := by
  step fm
  apply stepStar_trans (r4_drain (8 * m + 4) 1 (2 * m + 2 + f))
  rw [show 1 + (8 * m + 4) = 1 + 4 * (2 * m + 1) from by ring,
      show 2 * m + 2 + f = (f + 1) + (2 * m + 1) from by ring]
  apply stepStar_trans (multi_round (2 * m + 1) 1 0 (f + 1))
  apply stepStar_trans (tail1 (0 + 3 * (2 * m + 1)) f)
  rw [show (3 : ℕ) = 2 + 1 from by ring,
      show 0 + 3 * (2 * m + 1) = 2 * (3 * m + 1) + 1 from by ring]
  apply stepStar_trans (chain_odd (3 * m + 1) 2 f)
  rw [show 2 + 3 * (3 * m + 1) + 2 = 9 * m + 7 from by ring]
  apply stepStar_trans (r3_drain (9 * m + 7) 1 (f + (3 * m + 1) + 1))
  ring_nf; finish

theorem case_8m6 (m : ℕ) :
    ⟨0, 0, 0, 8 * m + 6, 2 * m + 2 + f⟩ [fm]⊢⁺ ⟨0, 0, 0, 18 * m + 16, f + 12 * m + 10⟩ := by
  step fm
  apply stepStar_trans (r4_drain (8 * m + 5) 1 (2 * m + 2 + f))
  rw [show 1 + (8 * m + 5) = 2 + 4 * (2 * m + 1) from by ring,
      show 2 * m + 2 + f = (f + 1) + (2 * m + 1) from by ring]
  apply stepStar_trans (multi_round (2 * m + 1) 2 0 (f + 1))
  apply stepStar_trans (tail2 (0 + 3 * (2 * m + 1)) f)
  rw [show (2 : ℕ) = 1 + 1 from by ring,
      show 0 + 3 * (2 * m + 1) + 1 = 2 * ((3 * m + 1) + 1) from by ring]
  apply stepStar_trans (chain_even (3 * m + 1) 1 f)
  rw [show 1 + 3 * (3 * m + 1) + 4 = 9 * m + 8 from by ring]
  apply stepStar_trans (r3_drain (9 * m + 8) 0 (f + (3 * m + 1) + 1))
  ring_nf; finish

theorem case_8m7 (m : ℕ) :
    ⟨0, 0, 0, 8 * m + 7, 2 * m + 2 + f⟩ [fm]⊢⁺ ⟨0, 0, 0, 18 * m + 17, f + 12 * m + 11⟩ := by
  step fm
  apply stepStar_trans (r4_drain (8 * m + 6) 1 (2 * m + 2 + f))
  rw [show 1 + (8 * m + 6) = 3 + 4 * (2 * m + 1) from by ring,
      show 2 * m + 2 + f = (f + 1) + (2 * m + 1) from by ring]
  apply stepStar_trans (multi_round (2 * m + 1) 3 0 (f + 1))
  apply stepStar_trans (tail3 (0 + 3 * (2 * m + 1)) f)
  rw [show (1 : ℕ) = 0 + 1 from by ring,
      show 0 + 3 * (2 * m + 1) + 2 = 2 * (3 * m + 2) + 1 from by ring]
  apply stepStar_trans (chain_odd (3 * m + 2) 0 f)
  rw [show 0 + 3 * (3 * m + 2) + 2 = 9 * m + 8 from by ring]
  apply stepStar_trans (r3_drain (9 * m + 8) 1 (f + (3 * m + 2) + 1))
  ring_nf; finish

theorem case_8m0 (m : ℕ) :
    ⟨0, 0, 0, 8 * (m + 1), 2 * (m + 1) + 1 + f⟩ [fm]⊢⁺ ⟨0, 0, 0, 18 * (m + 1) + 5, f + 12 * (m + 1) + 2⟩ := by
  step fm
  apply stepStar_trans (r4_drain (8 * (m + 1) - 1) 1 (2 * (m + 1) + 1 + f))
  rw [show 1 + (8 * (m + 1) - 1) = 0 + 4 * (2 * (m + 1)) from by omega,
      show 2 * (m + 1) + 1 + f = (f + 1) + 2 * (m + 1) from by ring]
  apply stepStar_trans (multi_round (2 * (m + 1)) 0 0 (f + 1))
  rw [show 0 + 3 * (2 * (m + 1)) = 3 * (2 * (m + 1)) from by ring]
  apply stepStar_trans (tail0 (3 * (2 * (m + 1)) - 1) f)
  rw [show (4 : ℕ) = 3 + 1 from by ring,
      show 3 * (2 * (m + 1)) - 1 = 2 * (3 * m + 2) + 1 from by omega]
  apply stepStar_trans (chain_odd (3 * m + 2) 3 f)
  rw [show 3 + 3 * (3 * m + 2) + 2 = 9 * m + 11 from by ring]
  apply stepStar_trans (r3_drain (9 * m + 11) 1 (f + (3 * m + 2) + 1))
  ring_nf; finish

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨0, 0, 0, 7, 4⟩) (by execute fm 12)
  apply progress_nonhalt (fm := fm)
    (P := fun q ↦ ∃ d e, q = ⟨0, 0, 0, d + 1, e + 1⟩ ∧ 2 * (e + 1) ≥ d + 1)
  · intro c ⟨d, e, hq, hde⟩; subst hq
    obtain ⟨n, rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl⟩ :
        ∃ n, d = 8 * n ∨ d = 8 * n + 1 ∨ d = 8 * n + 2 ∨ d = 8 * n + 3 ∨
             d = 8 * n + 4 ∨ d = 8 * n + 5 ∨ d = 8 * n + 6 ∨ d = 8 * n + 7 :=
      ⟨d / 8, by omega⟩
    · -- d = 8n, d+1 = 8n+1
      rcases n with _ | n
      · refine ⟨⟨0, 0, 0, 6, e + 3⟩, ⟨5, e + 2, rfl, by omega⟩, ?_⟩
        exact case_d1 (f := e)
      · refine ⟨⟨0, 0, 0, 18 * (n + 1) + 6, (e - 2 * n - 2) + 12 * (n + 1) + 3⟩,
          ⟨18 * (n + 1) + 5, (e - 2 * n - 2) + 12 * (n + 1) + 2, rfl, by omega⟩, ?_⟩
        rw [show 8 * (n + 1) + 1 = 8 * (n + 1) + 1 from rfl,
            show e + 1 = 2 * (n + 1) + 1 + (e - 2 * n - 2) from by omega]
        exact case_8m1 (n + 1) (by omega) (f := e - 2 * n - 2)
    · -- d = 8n+1, d+1 = 8n+2
      rcases n with _ | n
      · refine ⟨⟨0, 0, 0, 7, e + 4⟩, ⟨6, e + 3, rfl, by omega⟩, ?_⟩
        exact case_d2 (f := e)
      · refine ⟨⟨0, 0, 0, 18 * (n + 1) + 7, (e - 2 * n - 2) + 12 * (n + 1) + 4⟩,
          ⟨18 * (n + 1) + 6, (e - 2 * n - 2) + 12 * (n + 1) + 3, rfl, by omega⟩, ?_⟩
        rw [show 8 * (n + 1) + 1 + 1 = 8 * (n + 1) + 2 from by ring,
            show e + 1 = 2 * (n + 1) + 1 + (e - 2 * n - 2) from by omega]
        exact case_8m2 (n + 1) (f := e - 2 * n - 2)
    · -- d = 8n+2, d+1 = 8n+3
      rcases n with _ | n
      · refine ⟨⟨0, 0, 0, 8, e + 5⟩, ⟨7, e + 4, rfl, by omega⟩, ?_⟩
        exact case_d3 (f := e)
      · refine ⟨⟨0, 0, 0, 18 * (n + 1) + 8, (e - 2 * n - 2) + 12 * (n + 1) + 5⟩,
          ⟨18 * (n + 1) + 7, (e - 2 * n - 2) + 12 * (n + 1) + 4, rfl, by omega⟩, ?_⟩
        rw [show 8 * (n + 1) + 2 + 1 = 8 * (n + 1) + 3 from by ring,
            show e + 1 = 2 * (n + 1) + 1 + (e - 2 * n - 2) from by omega]
        exact case_8m3 (n + 1) (f := e - 2 * n - 2)
    · -- d = 8n+3, d+1 = 8n+4
      refine ⟨⟨0, 0, 0, 18 * n + 14, (e - 2 * n - 1) + 12 * n + 8⟩,
        ⟨18 * n + 13, (e - 2 * n - 1) + 12 * n + 7, rfl, by omega⟩, ?_⟩
      rw [show 8 * n + 3 + 1 = 8 * n + 4 from by ring,
          show e + 1 = 2 * n + 2 + (e - 2 * n - 1) from by omega]
      exact case_8m4 n (f := e - 2 * n - 1)
    · -- d = 8n+4, d+1 = 8n+5
      refine ⟨⟨0, 0, 0, 18 * n + 15, (e - 2 * n - 1) + 12 * n + 9⟩,
        ⟨18 * n + 14, (e - 2 * n - 1) + 12 * n + 8, rfl, by omega⟩, ?_⟩
      rw [show 8 * n + 4 + 1 = 8 * n + 5 from by ring,
          show e + 1 = 2 * n + 2 + (e - 2 * n - 1) from by omega]
      exact case_8m5 n (f := e - 2 * n - 1)
    · -- d = 8n+5, d+1 = 8n+6
      refine ⟨⟨0, 0, 0, 18 * n + 16, (e - 2 * n - 1) + 12 * n + 10⟩,
        ⟨18 * n + 15, (e - 2 * n - 1) + 12 * n + 9, rfl, by omega⟩, ?_⟩
      rw [show 8 * n + 5 + 1 = 8 * n + 6 from by ring,
          show e + 1 = 2 * n + 2 + (e - 2 * n - 1) from by omega]
      exact case_8m6 n (f := e - 2 * n - 1)
    · -- d = 8n+6, d+1 = 8n+7
      refine ⟨⟨0, 0, 0, 18 * n + 17, (e - 2 * n - 1) + 12 * n + 11⟩,
        ⟨18 * n + 16, (e - 2 * n - 1) + 12 * n + 10, rfl, by omega⟩, ?_⟩
      rw [show 8 * n + 6 + 1 = 8 * n + 7 from by ring,
          show e + 1 = 2 * n + 2 + (e - 2 * n - 1) from by omega]
      exact case_8m7 n (f := e - 2 * n - 1)
    · -- d = 8n+7, d+1 = 8(n+1)
      refine ⟨⟨0, 0, 0, 18 * (n + 1) + 5, (e - 2 * n - 2) + 12 * (n + 1) + 2⟩,
        ⟨18 * (n + 1) + 4, (e - 2 * n - 2) + 12 * (n + 1) + 1, rfl, by omega⟩, ?_⟩
      rw [show 8 * n + 7 + 1 = 8 * (n + 1) from by ring,
          show e + 1 = 2 * (n + 1) + 1 + (e - 2 * n - 2) from by omega]
      exact case_8m0 n (f := e - 2 * n - 2)
  · exact ⟨6, 3, rfl, by omega⟩

end Sz22_2003_unofficial_1111
