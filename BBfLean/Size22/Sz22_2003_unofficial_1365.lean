import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #1365: [63/10, 4/33, 847/2, 5/7, 3/11]

Vector representation:
```
-1  2 -1  1  0
 2 -1  0  0 -1
-1  0  0  1  2
 0  0  1 -1  0
 0  1  0  0 -1
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_1365

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a+1, b, c+1, d, e⟩ => some ⟨a, b+2, c, d+1, e⟩
  | ⟨a, b+1, c, d, e+1⟩ => some ⟨a+2, b, c, d, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b, c, d+1, e+2⟩
  | ⟨a, b, c, d+1, e⟩ => some ⟨a, b, c+1, d, e⟩
  | ⟨a, b, c, d, e+1⟩ => some ⟨a, b+1, c, d, e⟩
  | _ => none

theorem r3_chain : ∀ k d e, ⟨a + k, 0, 0, d, e⟩ [fm]⊢* ⟨a, 0, 0, d + k, e + 2 * k⟩ := by
  intro k; induction' k with k ih <;> intro d e
  · exists 0
  · rw [show a + (k + 1) = (a + k) + 1 from by ring]
    step fm; apply stepStar_trans (ih (d + 1) (e + 2)); ring_nf; finish

theorem r4_chain : ∀ k c d, ⟨0, 0, c, d + k, e⟩ [fm]⊢* ⟨0, 0, c + k, d, e⟩ := by
  intro k; induction' k with k ih <;> intro c d
  · exists 0
  · rw [show d + (k + 1) = (d + k) + 1 from by ring]
    step fm; apply stepStar_trans (ih (c + 1) d); ring_nf; finish

theorem r2_chain : ∀ n a d, ⟨a, b + n, 0, d, e + n⟩ [fm]⊢* ⟨a + 2 * n, b, 0, d, e⟩ := by
  intro n; induction' n with n ih <;> intro a d
  · exists 0
  · rw [show b + (n + 1) = (b + n) + 1 from by ring,
        show e + (n + 1) = (e + n) + 1 from by ring]
    step fm; apply stepStar_trans (ih (a + 2) d); ring_nf; finish

theorem r3r2r2_one : ⟨a + 1, b + 2, 0, d, 0⟩ [fm]⊢⁺ ⟨a + 4, b, 0, d + 1, 0⟩ := by
  step fm; step fm; step fm; finish

theorem r3r2r2_chain : ∀ k a d, ⟨a + 1, 2 * k + 2, 0, d, 0⟩ [fm]⊢*
    ⟨a + 3 * k + 4, 0, 0, d + k + 1, 0⟩ := by
  intro k; induction' k with k ih <;> intro a d
  · exact stepPlus_stepStar r3r2r2_one
  · rw [show 2 * (k + 1) + 2 = (2 * k + 2) + 2 from by ring]
    apply stepStar_trans (stepPlus_stepStar (@r3r2r2_one a (2 * k + 2) d))
    rw [show a + 4 = (a + 3) + 1 from by ring]
    apply stepStar_trans (ih (a + 3) (d + 1))
    ring_nf; finish

theorem r2r1r1_one : ⟨0, b + 1, c + 2, d, e + 1⟩ [fm]⊢⁺ ⟨0, b + 4, c, d + 2, e⟩ := by
  step fm; step fm; step fm; finish

theorem phase3_inner : ∀ k b d e, ⟨0, b + 1, 2 * k + 2, d, e + k + 1⟩ [fm]⊢*
    ⟨0, b + 3 * k + 4, 0, d + 2 * k + 2, e⟩ := by
  intro k; induction' k with k ih <;> intro b d e
  · exact stepPlus_stepStar r2r1r1_one
  · rw [show 2 * (k + 1) + 2 = (2 * k + 2) + 2 from by ring,
        show e + (k + 1) + 1 = (e + k + 1) + 1 from by ring]
    apply stepStar_trans (stepPlus_stepStar (@r2r1r1_one b (2 * k + 2) d (e + k + 1)))
    rw [show b + 4 = (b + 3) + 1 from by ring]
    apply stepStar_trans (ih (b + 3) (d + 2) e)
    ring_nf; finish

theorem phase3 : ∀ k e, ⟨0, 0, 2 * k + 2, 0, e + k + 2⟩ [fm]⊢*
    ⟨0, 3 * k + 4, 0, 2 * k + 2, e⟩ := by
  intro k e
  rw [show e + k + 2 = (e + k + 1) + 1 from by ring]
  step fm
  show ⟨0, 0 + 1, 2 * k + 2, 0, e + k + 1⟩ [fm]⊢* _
  apply stepStar_trans (phase3_inner k 0 0 e)
  ring_nf; finish

theorem main_trans {a d : ℕ} (ha : a ≥ d + 2) (hd : d ≥ 1) (heven : (a + d) % 2 = 0) :
    ⟨a, 0, 0, d, 0⟩ [fm]⊢⁺ ⟨3 * a + 2 * d + 1, 0, 0, a + 2 * d + 1, 0⟩ := by
  obtain ⟨K, hK⟩ : ∃ K, a + d = 2 * K + 2 := by
    obtain ⟨m, hm⟩ := Nat.dvd_of_mod_eq_zero heven; exact ⟨m - 1, by omega⟩
  obtain ⟨E, hE⟩ : ∃ E, 2 * a = E + K + 2 := ⟨2 * a - K - 2, by omega⟩
  have hBE : 3 * K + 4 = (2 * d + 2) + E := by omega
  have p1 : ⟨a, 0, 0, d, 0⟩ [fm]⊢* ⟨0, 0, 0, a + d, 2 * a⟩ := by
    rw [show (a : ℕ) = 0 + a from by ring]
    apply stepStar_trans (r3_chain a d 0); ring_nf; finish
  have p2 : ⟨0, 0, 0, a + d, 2 * a⟩ [fm]⊢* ⟨0, 0, a + d, 0, 2 * a⟩ := by
    rw [show (a + d : ℕ) = 0 + (a + d) from by ring]
    apply stepStar_trans (r4_chain (a + d) 0 0 (e := 2 * a)); ring_nf; finish
  have p3 : ⟨0, 0, a + d, 0, 2 * a⟩ [fm]⊢* ⟨0, 3 * K + 4, 0, 2 * K + 2, E⟩ := by
    rw [hK, hE]; exact phase3 K E
  have p4 : ⟨0, 3 * K + 4, 0, 2 * K + 2, E⟩ [fm]⊢* ⟨2 * E, 2 * d + 2, 0, 2 * K + 2, 0⟩ := by
    have h := @r2_chain (b := 2 * d + 2) (e := 0) E 0 (2 * K + 2)
    simp only [Nat.zero_add] at h
    rwa [show 2 * d + 2 + E = 3 * K + 4 from by omega] at h
  have h2K : 2 * K + 2 = a + d := by omega
  obtain ⟨E', hE'⟩ : ∃ E', 2 * E = E' + 1 := ⟨2 * E - 1, by omega⟩
  have p5 : ⟨2 * E, 2 * d + 2, 0, 2 * K + 2, 0⟩ [fm]⊢*
      ⟨3 * a + 2 * d + 1, 0, 0, a + 2 * d + 1, 0⟩ := by
    rw [hE', h2K]
    apply stepStar_trans (r3r2r2_chain d E' (a + d))
    have hgoal1 : E' + 3 * d + 4 = 3 * a + 2 * d + 1 := by omega
    have hgoal2 : a + d + d + 1 = a + 2 * d + 1 := by omega
    refine ⟨0, ?_⟩; simp only [stepNat, Nat.repeat, Option.some.injEq]
    rw [hgoal1, hgoal2]
  have combined : ⟨a, 0, 0, d, 0⟩ [fm]⊢* ⟨3 * a + 2 * d + 1, 0, 0, a + 2 * d + 1, 0⟩ :=
    stepStar_trans p1 (stepStar_trans p2 (stepStar_trans p3 (stepStar_trans p4 p5)))
  apply stepStar_stepPlus combined
  intro h; have := congr_arg (fun q : Q => q.2.2.2.1) h; simp at this; omega

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨4, 0, 0, 2, 0⟩) (by execute fm 8)
  apply progress_nonhalt (fm := fm)
    (P := fun q ↦ ∃ a d, q = ⟨a, 0, 0, d, 0⟩ ∧ a ≥ d + 2 ∧ d ≥ 1 ∧ (a + d) % 2 = 0)
  · intro c ⟨a, d, hq, ha, hd, heven⟩
    subst hq
    exact ⟨⟨3 * a + 2 * d + 1, 0, 0, a + 2 * d + 1, 0⟩,
      ⟨3 * a + 2 * d + 1, a + 2 * d + 1, rfl, by omega, by omega, by omega⟩,
      main_trans ha hd heven⟩
  · exact ⟨4, 2, rfl, by omega, by omega, by omega⟩
