import YM.Poised.Cupcake
/-! # lifting buffered norms across marked support. full credits -/
set_option autoImplicit false
noncomputable section
namespace YM.Massive.Poised
open Function Filter Set Lattice Wilson Tree RG Source Source.Drops MeasureTheory Finset WardBin Work.G05 Planned.PrimaryIntegral295 Planned.PrimaryIntegral295.Place
open scoped Topology BigOperators ContDiff Matrix.Norms.Frobenius TensorProduct Classical ComplexConjugate
open QCD QCD.Lat QCD.Grass UV Cylinder SourceRead
variable {B : Type}{d k j n:ℕ}{c l:Side}
namespace Chute
open Pipes QCD.Kit QCD.Flume QCD.Cove QCD.Creek QCD.Loom QCD.Flume QCD.Fork QCD.Port QCD.Brick Lining Lining.Ferry
open Precision Pressure Garden Run Laurent Carrier Next.Free QCD.Kit
open PhysicalNext.JointLoad Palette Steed Beacon MultiNext.SignedSource Cruising
variable {K : KernelChoices} {v f ν:ℕ}{S:StepData c l}{X:Support l}{Y:Support c}{σ α:ℝ} {b b':Cover}
-- fundamental reserve
section
variable {E F Z : Type}[NormedAddCommGroup E][NormedAddCommGroup F][NormedAddCommGroup Z] [CompleteSpace Z]{q: Cover→E}(M:E→F→Z)(hM:∀ x y, ‖M x y‖≤‖x‖*‖y‖)
variable (hσ:0<σ)(h:Width σ α q){C:ℝ}(hC:0≤C) (f:Cover→F)(hf:∀ i, ‖f i‖≤ C*liftCost n i)
include hσ h hM hC hf
lemma accountV : SumBudget (fun i=> ‖M (q i) (f i)‖) (C*widthCost σ n*α) :=by
   let W:=fun i=>‖q i‖*liftCost n i; have hZ:=width_billG hσ h n
   refine Work.F08.budget_minor (g:=fun i=>C*W i) ⟨fun i=>mul_nonneg hC (hZ.1 _),hZ.2.1.mul_left C,?_⟩ (fun _=>norm_nonneg _) fun i=>?_ ; swap
   · exact (hM _ _).trans ((mul_le_mul_of_nonneg_left (hf i) (norm_nonneg _)).trans_eq (mul_left_comm ..))
   rw [tsum_mul_left,mul_assoc]; exact mul_le_mul_of_nonneg_left hZ.2.2 hC
lemma dregs (g:Cover→F)(hg:∀ i, ‖g i‖≤ C*liftCost n i)(hm:∀ i, size i≤v→ f i=g i):
    ‖(∑' z,M (q z) (f z))-(∑' z,M (q z) (g z))‖ ≤ Real.exp (-(σ/2)*v)*(2*C)*widthCost (σ/2) n*α:=by
    have hx:0 < σ/2:=half_pos hσ; let A:=Real.exp (-(σ/2)*v); let a:=A*(2*C)*widthCost (σ/2) n; have ha:0≤a:=by have ht:= widthCost_ge hx n; unfold a A; positivity
    let D(i:Cover):=M (q i) (f i)-M (q i) (g i); let W(i:Cover):=Real.exp (σ*size i)*‖q i‖
    have hs : SumBudget (fun i=> ‖D i‖) (a*α):=by
       refine Work.F08.budget_minor (g:=fun i=> a*W i) ⟨fun i=>mul_nonneg ha (h.1 i),h.2.1.mul_left _,?_⟩ (fun i=>norm_nonneg _) fun i=>?_
       · rw [tsum_mul_left]; exact mul_le_mul_of_nonneg_left h.2.2 ha
       by_cases he:size i ≤ v; · change ‖D i‖≤ _; unfold D; rw [hm _ he,sub_self,norm_zero]; exact mul_nonneg ha (h.1 _)
       let B:= ‖q i‖; let r:ℝ:= size i; let d':=σ/2; let s:=Real.exp (d'*r)
       have ht:1 ≤ A*s:=by rw [show A*s=_ from (Real.exp_add _ _).symm]; refine Real.one_le_exp ?_; have hV:(v:ℝ)≤r:=Nat.cast_le.mpr ((lt_of_not_ge he).le) -- fix
                                                                     ; unfold d'; nlinarith
       let Z:= B*(C*(widthCost d' n*s)); have hz:0 ≤ Z:=by have h:= widthCost_ge hx n; change 0≤ ‖q i‖*(C*(widthCost (σ/2) n*Real.exp _)); positivity
       have hB: C*liftCost n i≤ C*(widthCost d' n*s) := mul_le_mul_of_nonneg_left (widthBill _ hx _ r (by unfold r; positivity)) hC
       have hp: ‖D i‖≤ Z+Z:= (norm_sub_le ..).trans (add_le_add ((hM ..).trans (mul_le_mul_of_nonneg_left ((hf i).trans hB) (norm_nonneg _))) ((hM ..).trans (mul_le_mul_of_nonneg_left ((hg i).trans hB) (norm_nonneg _))))
       refine hp.trans ((le_mul_of_one_le_right (add_nonneg hz hz) ht).trans_eq ?_); unfold W; rw [show σ*(size i)=d'*r+d'*r by unfold d' r; ring, Real.exp_add]; unfold Z s a d' B; ring
    rw [← Summable.tsum_sub (accountV M hM hσ h hC f hf).2.1.of_norm (accountV M hM hσ h hC g hg).2.1.of_norm]; exact (norm_tsum_le_tsum_norm hs.2.1).trans hs.2.2
end
-- charged stencil distances
variable (P:Flight j k) (h:l.val=c.val*P.L.val)(T:Tube su (Flight.visit P K h)) {w v:ℕ}(Ω:Cruising (sliceL P h) X Y b b' w v)(x:Site l)(hx:x∈X) {C:ℝ}(hk:4≤k)
include Ω hx
-- simultaneous total and discrepancy
local notation "L0"=> P.L
variable (hσ:0 < σ)
def ore (σ:ℝ)(n:ℕ)(C:ℝ)(v:ℕ):=(1+(v:ℝ))^n*C*widthCost σ n
local notation "z'"=> plinth b x
section Gauge
variable {Z Z': Carrier.Window su.Color}{τ:ℝ} (hC:0 ≤ C)(h1:∀ i j, ‖Z i j‖≤ C*liftCost n (i-b'))(h2:∀ i j,‖Z' i j‖ ≤ C*liftCost n (i-b'))
variable (hW:T.R.A0.strip σ τ)
include h1 hC hσ hW
private lemma rice (_f f':ℝ→ su.Color →su.Color)(ht:_f=f') (i a:Axis) : ‖stream (member T.R.A0 z' i a) (cellar P.L z') (fun z=>Z z a)‖ ≤ ore σ n C v*τ:=by
   let W:=member T.R.A0 z' i a; let z:= gate (sliceL P h) b x; let a':=(1+(v:ℝ))^n
   have hb:= accountV (· • ·) (fun (x:ℝ) (y:su.Color)=> (norm_smul ..).le) hσ (hW (wrap _ z', Exterior.coord i) (Exterior.coord a)) (show 0≤a'*C from mul_nonneg (by unfold a'; positivity) hC) (fun p=>Z (z+p) a) (n:=n) (fun j=> ((h1 _ a).trans (mul_le_mul_of_nonneg_left (ticket Ω hx j n) hC)).trans_eq (by unfold a';ring))
   exact (norm_tsum_le_tsum_norm hb.2.1).trans hb.2.2
lemma rice_p (i:Axis): ‖applyLine T.R.A0 Z z' i‖ ≤ 4*ore σ n C v*τ:=by
   apply (norm_sum_le ..).trans ((sum_le_sum (fun j _=> rice P h T Ω x hx hσ hC h1 hW (· • ·) _ rfl i j)).trans (le_of_eq ?_)); simp only [sum_const,card_univ,nsmul_eq_mul]; simp [Axis]; ring
include h2
lemma rice_left (i:Axis)(he:∀ k:Cover,size k ≤ w → Z (gate (sliceL P h) b x+k)=Z' (gate (sliceL P h) b x+k)): ‖applyLine T.R.A0 Z z' i-applyLine T.R.A0 Z' z' i‖ ≤ Real.exp (-(σ/2)*w)*8*ore (σ/2) n C v*τ:=by
   unfold applyLine; rw [←Finset.sum_sub_distrib]; let R:= gate (sliceL P h) b x; let B:=(1+(v:ℝ))^n*C; have hp:0≤B:= by unfold B; positivity; --guard
   let V(a:Axis):= dregs (· • ·) (fun (x:ℝ) (y:su.Color)=> (norm_smul ..).le) hσ (hW (wrap _ z', Exterior.coord i) (Exterior.coord a)) hp (fun p=>Z (R+p) a) (n:=n) (fun j=> ((h1 _ a).trans (mul_le_mul_of_nonneg_left (ticket Ω hx j n) hC)).trans_eq (by unfold B;ring)) (fun p=>Z' (R+p) a) (fun j=> ((h2 _ a).trans (mul_le_mul_of_nonneg_left (ticket Ω hx j n) hC)).trans_eq (by unfold B;ring)) (fun j hj=> congr_fun (he j hj) a)
   exact (norm_sum_le ..).trans ((sum_le_sum fun i _=> V i).trans (le_of_eq (by simp only [sum_const,card_univ,nsmul_eq_mul, B]; simp [Axis]; unfold ore; ring)))
end Gauge
section Spin
variable (hC:0≤C){Z Z':Cover → Flet B}{τ:ℝ}(h1:∀ i j k, ‖Z i j k‖≤ C*liftCost n (i-b'))(h2:∀ i j k,‖Z' i j k‖ ≤ C*liftCost n (i-b'))
variable (hW:∀ (a b:Pipes.Shell)(x:Cover),Width σ τ (arch P a b x)) [Fintype B]
local notation "Φ" => Fintype.card Pipes.Shell
include hC hσ h1 hW
lemma moss (u:Pipes.Shell)(y:B): ‖serve P Z z' u y‖ ≤ Φ*ore σ n C v*τ:=by
   let B':=(1+(v:ℝ))^n; let z:= gate (sliceL P h) b x; have hv(i:Pipes.Shell): ‖∑' j:Cover, arch P u i z' j*Z (z+j) i y‖ ≤ ore σ n C v*τ:=by
        have hb:= accountV (·*·) (fun (x y:ℂ)=> (norm_mul ..).le) hσ (hW u i z') (show 0≤B'*C from mul_nonneg (by unfold B'; positivity) hC) (fun p=>Z (z+p) i y) (n:=n) (fun j=> ((h1 _ i y).trans (mul_le_mul_of_nonneg_left (ticket Ω hx j n) hC)).trans_eq (by unfold B';ring))
        exact (norm_tsum_le_tsum_norm hb.2.1).trans hb.2.2
   apply (norm_sum_le ..).trans ((sum_le_sum (fun j _=> hv j)).trans (le_of_eq ?_)); simp only [sum_const,card_univ,nsmul_eq_mul,mul_assoc]
include h2
lemma moss_left (u:Pipes.Shell)(y:B)(he:∀ k:Cover,size k ≤ w → Z (gate (sliceL P h) b x+k)=Z' (gate (sliceL P h) b x+k)): ‖serve P Z z' u y-serve P Z' z' u y‖ ≤ Real.exp (-(σ/2)*w)*(2*(Φ:ℝ))*ore (σ/2) n C v*τ:=by
   unfold serve; rw [←Finset.sum_sub_distrib]; let R:= gate (sliceL P h) b x; let D:=(1+(v:ℝ))^n*C; have hp:0≤D:= by unfold D; positivity; -- guard
   let V(a:Pipes.Shell):= dregs (· * ·) (fun (x y:ℂ)=> (norm_mul ..).le) hσ (hW u a z') hp (fun p=>Z (R+p) a y) (n:=n) (fun j=> ((h1 _ a y).trans (mul_le_mul_of_nonneg_left (ticket Ω hx j n) hC)).trans_eq (by unfold D;ring)) (fun p=>Z' (R+p) a y) (fun j=> ((h2 _ a y).trans (mul_le_mul_of_nonneg_left (ticket Ω hx j n) hC)).trans_eq (by unfold D;ring)) (fun j hj=> congr_fun (congr_fun (he j hj) a) y)
   exact (norm_sum_le ..).trans ((sum_le_sum fun i _=> V i).trans (le_of_eq (by simp only [sum_const,card_univ,nsmul_eq_mul, D]; unfold ore; ring)))
end Spin
end Chute
end YM.Massive.Poised
#print axioms YM.Massive.Poised.Chute.moss_left
