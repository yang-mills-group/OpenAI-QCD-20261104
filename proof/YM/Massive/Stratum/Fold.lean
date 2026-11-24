import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Logic.Relation -- check
/-!
# Layered collar scheduling (hit budgets)

Post-choice widths/costs can be restored *independently* along
finite transition segments (laid out before beginning any schedule).
Alphabet is arbitrary *per step*, real labels are never charged at
uncontrolled radii by saying the next period has a new alphabet.

This file is the elementary accounting part, establishing that a
suitable restoration is possible for coupled classes if each class
can meet the linear-inheritance bound at fixed lower-class costs.
It has no RG deductions on its own. See accompanying files
for the specific link to spin/loop-page prices.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Massive.Stratum
open Relation Filter
open scoped Topology

/-- The two competing scales. -/
structure Price where
 r : ℝ
 bill : ℝ
 live : 0 < r
 good : 0 ≤ bill

/-- Exists a fixed standard, repeatable indefinitely once at that
standard, reachable from any initial budgets in finitely many steps. -/
def Century {X:Type*} (H:X→X→Prop) :Prop:=
    ∃ u : X, H u u ∧ ∀ x:X, ReflTransGen H x u
namespace Price
/-- Recovery prescription, one step. Use at sufficiently large ratios. -/
def Permit (P X Y:Price):Prop:= Y.r≤P.r ∧ Y.r ≤ 2*X.r ∧ P.bill+X.bill/2 ≤ Y.bill

def later (P X : Price):Price := ⟨min P.r (2*X.r), P.bill+X.bill/2,
   lt_min P.live (by have h:=X.live; positivity), by have h:=X.good; have k:=P.good; positivity⟩
lemma step (P X :Price):P.Permit X (P.later X):= ⟨min_le_left ..,min_le_right ..,le_rfl⟩

def master (P:Price):Price:= ⟨P.r, 2*P.bill+2,P.live, by have h:=P.good; positivity⟩
theorem hit (P:Price)(S: Price→Price→Prop)(h:∀ X Y,P.Permit X Y → S X Y): Century S:=by
  let Y:=P.master
  have hp:=P.good; have hr:=P.live
  have H (X:Price) (hh:P.r≤X.r)(hb:X.bill ≤ 2*P.bill+2*(1:ℝ)):S X Y:=by
    apply h; unfold Permit Y master; dsimp only; exact ⟨le_rfl,by linarith,by linarith⟩
  refine ⟨Y,H Y le_rfl (by simp [Y,master]),fun X=>?_⟩
  have hX:=X.live
  obtain ⟨n,e,g⟩ : ∃ n:ℕ,P.r ≤ (2:ℝ)^n * X.r ∧ X.bill ≤ 2*P.bill +2*(2:ℝ)^n:= by
    let a:=max (P.r/X.r) (X.bill/2)
    obtain ⟨n,h⟩:=pow_unbounded_of_one_lt a (by norm_num : 1 < (2:ℝ))
    obtain ⟨h,h'⟩:=max_lt_iff.mp h
    exact ⟨n,(div_le_iff₀ hX).1 h.le,by linarith⟩
  induction n generalizing X with
  | zero=> exact .single (H X (by simpa using e) (by simpa only [pow_zero] using g))
  | succ n ih=>
    let Z:= P.later X
    have hz:=one_le_pow₀ (by norm_num : (1:ℝ)≤2) (n:=n); have hv:=X.good
    rw [pow_succ] at e g
    refine .head (h _ _ (step P X)) (ih (X:=Z) ?_ ?_ ?_)
    · exact Z.live
    · unfold Z later; dsimp only; rw [mul_min_of_nonneg _ _ (zero_le_one.trans hz)]; exact le_min (le_mul_of_one_le_left hr.le hz) (by linarith)
    · change P.bill+X.bill/2 ≤ _; linarith
end Price

/-- Permission for the second page may depend on the weaker of
*both* budgets of the lower-class transition. -/
def Tangle {X Z:Type*} (S:X→X→Prop)(H:X→X→Z→Z→Prop) (a b:X×Z) := S a.1 b.1 ∧ H a.1 b.1 a.2 b.2

/-- If every transition of the first layer can carry along a
partner with uncontrolled output budget (but actual, not a deferred
`depends on past`), pin the lower layer at its standard before
prepaying the second layer's recovery. -/
lemma stitch {X Z:Type*} (S:X→X→Prop)(H:X→X→Z→Z→Prop) (hs:Century S)(h:∀ a b: X,S a b→∀ x:Z,∃ y:Z,H a b x y)(hp:∀ a:X,S a a→Century (H a a)) : Century (Tangle S H):=by
  obtain ⟨u,hu,hv⟩:= hs; obtain ⟨W,hW,hH⟩:=hp u hu
  refine ⟨(u,W),⟨hu,hW⟩,?_⟩
  rintro ⟨x,z⟩
  have he(y:X)(he:ReflTransGen S x y):∃ w, ReflTransGen (Tangle S H) (x,z) (y,w):=by
    induction he with
    | refl=> exact ⟨_, .refl⟩
    | tail _ ha ih=>
        obtain ⟨w,hw⟩:=ih; obtain ⟨v,hv⟩:= h _ _ ha w
        exact ⟨v,.tail hw ⟨ha,hv⟩⟩
  obtain ⟨r,ht⟩:= he u (hv _)
  apply ht.trans
  generalize hy: W=B
  have hk: ReflTransGen (H u u) r B:= hy ▸ (hH r)
  clear hy
  induction hk with
  | refl=> exact .refl
  | tail _ hb ih=> exact .tail ih ⟨hu,hb⟩

end YM.Massive.Stratum
