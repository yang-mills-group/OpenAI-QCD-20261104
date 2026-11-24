import YM.QCD.Fog.Trunk

/-! # new beta & silence exact score formula at paid precision -/
set_option autoImplicit false
noncomputable section
namespace YM.QCD.Fog
open Lat Lattice Wilson Function Finset Filter Metric RG Precision Bloch Laurent
open Extra Iteration QCD.Smoke Work.F08 Work.F03 Exterior Bid YM.Next.Free Matrix Placement
open scoped Topology BigOperators Matrix Matrix.Norms.Frobenius ContDiff Classical InnerProductSpace
variable {I U:Type}{r A C d a:ℝ}{n:Side}
-- scales

def twice (P:I→Rg su):=2*depositG P
def imbue (P:Rg su)(v:ℝ):Rg su:={P with coeff:=v • P.coeff}
lemma imbue_pay (P:Rg su)(w v:ℝ): (imbue P w).budget v=|w| * P.budget v:=by unfold imbue Atom.budget Atom.magnitude; simp [abs_mul,Finset.mul_sum, Finset.sum_mul,mul_assoc,Atom.length]
lemma imbue_sym (P:Rg su)(h:P.Invariant)(v:ℝ): (imbue P v).Invariant:=by
  have hx x : (imbue P v).poly x=v*P.poly x:=by simp [imbue,Atom.poly,mul_sum,mul_assoc]
  intro i x; simp only [hx,h i x]
lemma imbues (P:U→Rg su)(v:ℝ)(h:Charged P r A):Charged (fun i=>imbue (P i) v) r (|v| * A):=by unfold Charged; simp_rw [imbue_pay]; exact Cost.scale h _ (abs_nonneg v)
lemma salary (P:U→Rg su)(v:ℝ):depositG (fun i=>imbue (P i) v)=v*depositG P:=by
  have hb i : propertyG (imbue (P i) v)=v*propertyG (P i):=by unfold propertyG; rw [Finset.mul_sum]; apply sum_congr rfl; intro z _; unfold charge imbue; dsimp only; split <;> simp
  simp_rw [depositG,sharesG,hb,mul_div_assoc, tsum_mul_left]
lemma depositJoint (X:I→Rg su)(Y:U→Rg su)(hr:0<r)(h:Charged X r A)(he:Charged Y r C): depositG (Sum.elim X Y)=depositG X+depositG Y:= Summable.tsum_sum (f:=fun i=>sharesG (Sum.elim X Y i)) (sharesSum _ h hr) (sharesSum _ he hr)
variable {T: Bed}{P:I→Rg su}
def storm (T:Bed)(P:I→Rg su):I⊕ Ledger→ Rg su:= Sum.elim P (fun i=>imbue (boot T i) (-(twice P)))
lemma stormed (hp:SymmetricAtoms P):SymmetricAtoms (storm T P):= by intro i; cases i with| inl i=>exact hp i| inr i=> exact imbue_sym _ (boots T i) _
lemma departed (ht: T.metric.strip r A)(hr:0<r)(he:Charged P r C)(h:T.metric.read 0=1): depositG (storm T P)=0:=by rw [storm,depositJoint _ _ hr he (imbues _ _ (bootBill T ht)),salary,twice,boot_normal T ht hr h]; ring
def cycleTax (A r:ℝ):=1+2*bootPrice r A
lemma cyclone (ht:T.metric.strip r A)(hr:0<r)(hh:Charged P r C):Charged (storm T P) r (cycleTax A r*C):=by
  have he:= deposit_bound P hh hr
  unfold storm; apply Cost.enlarge (Cost.sum (f:=fun j=> (storm T P j).budget r) hh (imbues (boot T) (-(twice P)) (bootBill T ht)))
  unfold cycleTax twice; rw [abs_neg,abs_mul]; rw [abs_of_pos (by norm_num : (0:ℝ)<2)]; linarith only [mul_le_mul_of_nonneg_left he (show 0≤bootPrice r A from Cost.nonneg (bootBill T ht))]
lemma storm_fiscal (ht:T.metric.strip r A)(hr:0<r)(hh:Charged P r C)(x:Dir su n): total (plain ∘ storm T P) (flux x)=total (plain ∘P) (flux x)-twice P*(gaugeFiscal T x x/2):=by
  have hp:= imbues (boot T) (-(twice P)) (bootBill T ht)
  let V:=fun i=>imbue (boot T i) (-(twice P))
  have hz:= Summable.tsum_sum (f:=fun i=>∑ y,((plain∘storm T P) i).sample (flux x) y) (net_summable (plain∘P) (flux x) hr.le hh) (net_summable (plain∘V) (flux x) hr.le hp); unfold total; rw [hz]
  change (_:ℝ)+(total (plain ∘ V) _)=_; rw [sub_eq_add_neg]; congr 1
  rw [← budgetE T ht hr,← neg_mul]; unfold V total; rw [← tsum_mul_left]; apply tsum_congr; intro i; rw [mul_sum]; refine sum_congr rfl fun p _=>?_ ; simp [plain,imbue,Pattern.sample,mul_sum,mul_assoc]

def inertia (T:Bed)(P:I→Rg su):= Lift.strip (whiff (storm T P))
lemma lic (hp:SymmetricAtoms P)(ht:T.metric.strip r A)(hr:0<r)(he:Charged P r C)(h:T.metric.read 0=1)(hk:0 ≤a)(hu:a<r): Palisade (inertia T P) a (momentPrice 2 (r-a)*(Real.exp (12*r)*(cycleTax A r*C))) := ⟨fun p=> Lift.break_both _ p.2,fun i=> Lift.break_symm _ (whiff_sym (stormed hp) i.1) _,Lift.strip_cost (whiff_budget (cyclone ht hr he) hr.le) hk hu⟩ -- h unused
lemma figurines (hp:SymmetricAtoms P)(ht:T.metric.strip r A)(hr:0<r)(he:Charged P r C)(h:T.metric.read 0=1)(hk:0 ≤a)(hu:a<r)(hs: Bid.Sworn T n su) (x: Dir su n) (t:Signed) [Countable I]:
    total (plain ∘ installG (inertia T P)) (flux (pulled x t))= Patch.average (fun r:Signed=> total (plain ∘P) (flux (pulled x r))) - twice P*(gaugeFiscal T x x/2):=by
  have hy:= lic hp ht hr he h hk hu
  have hG:= cyclone ht hr he
  rw [installG,total_padded (assembled hk hy.2.2) hk,assemble_at hy.2.2 hk,inertia,Lift.strip_total (whiff_budget hG hr.le) hk hu (digestG _ hG hr (stormed hp) (departed ht hr he h)), spins _ hG hr.le (pulled x t), reels x t]
  simp_rw [storm_fiscal ht hr he, hs ..]; -- avg
  unfold Patch.average; rw [Finset.sum_sub_distrib,sum_const,card_univ,nsmul_eq_mul,mul_sub, ← mul_assoc (_:ℝ) (Fintype.card Signed:ℝ),inv_mul_cancel₀ (by positivity),one_mul]
end YM.QCD.Fog
