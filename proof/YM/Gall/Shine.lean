import YM.Gall.Bounty
import YM.Oriole.VaryL
import YM.Poised.Furls
/-! Native position metrics for coefficient tests. -/
set_option autoImplicit false
noncomputable section
namespace YM.Massive.Patria.Gall
open Function Filter Set Lattice Wilson RG Source Source.Drops MeasureTheory Finset
open scoped Topology BigOperators ContDiff Matrix.Norms.L2Operator TensorProduct Classical ComplexConjugate
open QCD QCD.Lat QCD.Grass UV Cylinder SourceRead Oriole
open Poised Poised.Display Poised.Beacon Poised.Pipes Further.LogJets PCAC QCD.Kit QCD.Stew QCD.Creek
variable {u t a D C v e s:ℝ}{c:Side}{n j d m r k p w:ℕ}
local notation "V₀" => Grid c
local notation "X₀" => Directions su c
local notation "G₀" => Lat.Fields c 6
local notation "K"=> Modes c 6
noncomputable abbrev sepW (o x y:Site c):=1+max (separation x o:ℝ) (separation y o:ℝ)
lemma arm (o x y:Site c) : 1 ≤ sepW o x y:= le_add_of_nonneg_right (by positivity)
lemma honey (o:Site c) (i j:Fiber)(p q:Flavor 6)(X: Lat.Fields c 6) (hv:0<v)(he:m≤ n) : ∑ x:Site c,∑ y:Site c, (v^2*sepW o x y^m)* ‖Oriole.uncoat X ((x,i),p) ((y,j),q)‖ ≤ ‖framesF (purseX o n v) (mantel 2 X)‖:=by
    let f (x:Site c) : K:= ((x,i),p)
    let G (y:Site c) : K:= ((y,j),q)
    let g : Site c × Site c→ Finset (Pairs K):= fun z=> {Sum.inr (f z.1), Sum.inl (G z.2)}
    have hg:Injective g:=by
        intro s t h; have h1: Sum.inr (f s.1)∈g t:=h ▸ (by simp[g]:_∈g s); have h2:Sum.inl (G s.2)∈g t:=h ▸ (by simp[g]:_∈g s); simp[g,f,G] at h1 h2; exact Prod.ext h1 h2
    let P:= purseX o n v; let Y:= mantel 2 X; change _ ≤ load P Y; have hh i : 0<P i:= purse_pos _ _ _ hv _; rw [dry _ hh]; let Q(s:Finset (Pairs K)):= (∏ i∈s,P i)*‖coef s Y‖
    have hx(x y:Site c):v^2*sepW o x y^m ≤ P (Sum.inr (f x))* P (Sum.inl (G y)):=by
        let x':ℝ:=1+(separation x o:ℝ); let y':ℝ:=1+(separation y o:ℝ); have hx:1≤x':=by unfold x'; simp
        have hy:1 ≤ y':=by unfold y'; simp
        change _≤v*x'^n *(v*y'^n); rw[show v*x'^n*(v*y'^n)= v^2*((x'*y')^n) from (by rw[mul_pow]; ring)]; apply mul_le_mul_of_nonneg_left _ (sq_nonneg _)
        have hS: sepW o x y ≤ x'*y':=by unfold sepW; rw[add_max]; exact max_le (le_mul_of_one_le_right (zero_le_one.trans hx) hy) (le_mul_of_one_le_left (zero_le_one.trans hy) hx)
        exact (pow_le_pow_right₀ (arm ..) he).trans (pow_le_pow_left₀ (zero_le_one.trans (arm ..)) hS n)
    apply le_trans (b:=∑ i∈univ.image g,Q i)
    · rw [sum_image hg.injOn,Fintype.sum_prod_type]; refine sum_le_sum fun x _=> sum_le_sum fun y _=>?_ ; change v^2*_ * ‖uncoat X (f x) (G y)‖≤ Q (g (x,y)); let Z:=g (x,y); have hZ:Z.card=2:=by simp[Z,g]
      have h:‖uncoat X (f x) (G y)‖=‖coef Z Y‖:=by rw [Oriole.ivory]; unfold Y; rw [mantle_val,Stew.angel,if_pos hZ]; congr! 5
      rw[h]; unfold Q; apply mul_le_mul_of_nonneg_right _ (norm_nonneg _); simpa only [g,prod_insert (show Sum.inr (f x) ∉ ({Sum.inl (G y)}:Finset _) by simp), Finset.prod_singleton] using (hx x y)
    apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _); intro i _ _; exact mul_nonneg (prod_nonneg (fun _ _=> (hh _).le)) (norm_nonneg _)
variable {U:BudgetPoint}{F:Grid c→Lat.Fields c 6}{o : Site c}
lemma fruitful (h:Tutor o U F v n j a)(hv:0<v)(p q:Flavor 6)(x y:Fiber)(l: List (Directions su c))(hl:l.length ≤ U.order)(he:∀ i∈l,U.dirBound o i)(hm:m≤n)(hj:2<j) : ∑ i:Site c,∑ j: Site c, sepW o i j^m *‖Oriole.uncoat (leftDerivs F l 1) ((i,x),p) ((j,y),q)‖ ≤ a/v^2:=by
    apply (le_div_iff₀ (pow_pos hv _)).mpr; rw[mul_comm _ (v^2), mul_sum]; simp_rw [Finset.mul_sum,← mul_assoc (v^2)]; exact (honey o x y p q _ hv hm).trans (h.fortune _ hl he _ hj)
open Plans Plans.Stamp QCD.Kit Poised.Plans
variable {H:TaperHol}{T:Hol su} {A:Lining.Temper.Collage.Exhibit T}
open Poised Poised.Pipes
lemma desk (d:ℕ) : 2≤ Fintype.card (Poised.Palette.ZBand d):=by
    change 2≤Fintype.card (Pairs (SpinMode d)); have hi : Nonempty (SpinMode d):=⟨((0,(0,default)),0)⟩ -- lat color syntax
    have hp:=Fintype.card_pos_iff.mpr hi; unfold Pairs; simp only[Fintype.card_sum]; omega
lemma assets (h:Pilot H A d m p n j r s t): 2<j∧ d≤n∧ d*d ≤ p∧ d ≤ m :=by
    refine ⟨(desk _).trans_lt h.band, le_trans ?_ h.weight,h.cap,h.order⟩
    unfold surface; exact Nat.le_mul_of_pos_right d (lt_of_lt_of_le (by decide) (show 2 ≤ pick d from desk d))
end YM.Massive.Patria.Gall
#print axioms YM.Massive.Patria.Gall.assets
#print axioms YM.Massive.Patria.Gall.fruitful
