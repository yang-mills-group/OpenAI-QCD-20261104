import YM.Poised.Reins
/-! # spin jets through all moments, including bar entries without imposing oriented support on output -/
set_option autoImplicit false
noncomputable section
namespace YM.Massive.Poised
open Function Filter Set Lattice Wilson Tree RG Source Source.Drops MeasureTheory Finset WardBin Work.G05 Planned.PrimaryIntegral295 Planned.PrimaryIntegral295.Place
open scoped Topology BigOperators ContDiff Matrix.Norms.L2Operator TensorProduct Classical ComplexConjugate
open QCD QCD.Lat QCD.Grass UV Cylinder SourceRead
variable {B : Type}{d k j n:ℕ}{c l:Side}
namespace Steed
open Pipes QCD.Kit QCD.Flume QCD.Cove QCD.Creek QCD.Loom QCD.Flume QCD.Fork QCD.Port QCD.Brick Lining Lining.Ferry
open Pressure Garden Run Laurent Carrier Next.Free QCD.Kit
variable (P:Flight j k) (h:l.val=c.val*P.L.val)
variable (hk:4≤k)
include hk
-- Coupling-independent reserve
lemma shareG : ∃ W Z:ℝ,0<W ∧ 0≤Z∧∀ x:Cover, Width W Z (gears P x):=by
   obtain ⟨σ,C,hσ,hC,H⟩:=reserves_font P.legal hk
   obtain ⟨b,hb,K⟩:= Sparks.float_norm
   let I:=Lat.Fiber× Lat.Fiber; let U:ℝ := Fintype.card I * C; let A:=Kit.slope P.L; have hA:0<A:=QCD.Kit.slope_pos _; let p:ℝ:=P.L.val; have hp:0<p:=by unfold p; positivity
   refine ⟨σ,b*(U*A/p),hσ,?_ ,fun x=>?_⟩
   · unfold U I; positivity
   let r:= wrap P.L x; let F (i:I) (u:Cover):= ‖fonts P [] r i.1 i.2 u‖
   have he (x:I): RG.SumBudget (fun u=> Real.exp (σ * size u)*F x u) (C*A/p):= by simpa only [List.length_nil,add_zero,pow_one] using! H P r [] (by simp) x.1 x.2
   have hs : SumBudget (fun u=> ∑ i:I,Real.exp (σ * size u)* F i u) (U*A/p):=by
     have hc : Summable (fun u=> ∑ i:I, Real.exp (σ * size u) * F i u):= summable_sum fun i _=> (he i).2.1
     refine ⟨fun i=>sum_nonneg (fun j _=> (he j).1 _),hc,?_⟩; rw [Summable.tsum_finsetSum (f:=fun i u=> Real.exp (σ*size u)*F i u) fun i _=>(he i).2.1]; apply (sum_le_sum fun i _=> (he i).2.2).trans; unfold U; simp only [sum_const,card_univ,nsmul_eq_mul]; exact le_of_eq (by ring)
   have hx (x:Cover) : ‖Garden.sheath P r x‖≤ b*∑ i:I,F i x:=by
     have ha (i:I): 0≤ F i x:=norm_nonneg _; apply K _ _ (sum_nonneg fun i _=>ha i)
     intro i j; change F (i,j) x≤_; exact single_le_sum (s:=Finset.univ) (f:=fun i=>F i x) (fun i _=>ha i) (mem_univ (α:=I) (i,j))
   refine Work.F08.budget_minor (g:=fun u=> b * ∑ i:I,Real.exp (σ*size u)*F i u) ?_ (fun i=>mul_nonneg (Real.exp_pos _).le (norm_nonneg _)) fun i=>?_
   · refine ⟨fun i=>mul_nonneg hb (hs.1 _),hs.2.1.mul_left _,?_⟩; rw [tsum_mul_left]; exact mul_le_mul_of_nonneg_left hs.2.2 hb
   exact le_trans (mul_le_mul_of_nonneg_left (hx i) (Real.exp_pos _).le) (le_of_eq (by rw [←Finset.mul_sum,mul_left_comm]))
set_option maxRecDepth 2100 in
lemma archG : ∃ W Z:ℝ,0<W∧0≤Z∧∀ (u v:Pipes.Shell)(x:Cover),Width W Z (arch P u v x):=by
    choose L hL using fun (i:Pipes.Shell ×Pipes.Shell)=> spin_patch i.1 i.2
    let M:= ∑ i,‖L i‖; have hM:0≤M:= sum_nonneg fun i _=> ContinuousLinearMap.opNorm_nonneg (L i)
    obtain ⟨A,C,hA,hC,H⟩:= shareG P hk; refine ⟨A,M*C,hA,mul_nonneg hM hC,fun u v x=>?_⟩; let f(i:Cover):= Real.exp (A*size i)*‖gears P x i‖; have h:= H x
    refine Work.F08.budget_minor (g:=fun i=>M*f i) ⟨fun i=>mul_nonneg hM (h.1 _),h.2.1.mul_left _,?_⟩ (fun i=>mul_nonneg (Real.exp_pos _).le (norm_nonneg _)) ?_
    · rw [tsum_mul_left]; exact mul_le_mul_of_nonneg_left h.2.2 hM
    intro i; have hE:‖arch P u v x i‖ ≤ M*‖gears P x i‖:=by rw [show arch P u v x i=L (u,v) (gears P x i) from (hL (u,v) _).symm]; exact ((L _).le_opNorm _).trans (mul_le_mul_of_nonneg_right (single_le_sum (f:=fun i=> ‖L i‖) (fun i _=> ContinuousLinearMap.opNorm_nonneg (L i)) (mem_univ _)) (norm_nonneg _))
    exact (mul_le_mul_of_nonneg_left hE (Real.exp_pos _).le).trans_eq (mul_left_comm ..)
section
-- general complex response. Project on axes.Real or ℂ norm.Price independent threshold.
omit hk
variable {E F : Type*}[NormedAddCommGroup E]
-- caution Universe .
lemma width_billG {q:Cover→E}{σ C:ℝ}(hσ:0<σ)(h:Width σ C q)(n:ℕ):
    SumBudget (fun i:Cover=> ‖q i‖ * liftCost n i) (widthCost σ n*C):=by
   have he : Width σ C (fun i=> ‖q i‖):= by simpa only [Width,norm_norm] using h
   simpa only [norm_norm] using width_income hσ he n
variable [NormedSpace ℝ E]
private lemma march_v {q:Cover→E}{σ C:ℝ}(hσ:0<σ)(h:Width σ C q) (x:E4)(w:RouteProbe)(n:ℕ): Summable fun z=> ‖(w (x+Place.seat z))^n • q z‖:=by
    have he:= width_billG hσ h n; apply (he.2.1.mul_left ((‖w‖*(1+‖x‖))^n)).of_nonneg_of_le (fun _=> norm_nonneg _); intro z; rw [norm_smul,norm_pow]; refine le_trans (mul_le_mul_of_nonneg_right (c:= (‖w‖*((1+‖x‖)*(1+(size z:ℝ))))^n) ?_ (norm_nonneg _)) (le_of_eq ?_)
    · apply pow_le_pow_left₀ (norm_nonneg _); apply (w.le_opNorm _).trans; refine mul_le_mul_of_nonneg_left ((norm_add_le ..).trans ((add_le_add_right (shade_seat z) _).trans ?_)) (norm_nonneg _); nlinarith [Nat.cast_nonneg (α:=ℝ) (size z),norm_nonneg x]
    unfold liftCost; simp_rw [mul_pow]; ring
include hk
lemma playlist (x:Cover)(w:RouteProbe)(hn:n<j):let y:=Place.seat (cellar P.L x); let s:=(P.L.val:ℝ)⁻¹ • Place.seat x; ∑' z:Cover, (w (y+Place.seat z))^n • gears P x z = ∑' z:Cover,(w (s+Place.seat z))^n • gears P 0 z:=by
    intro y s; ext i k; let L:Bundle→ₗ[ℝ]ℂ:={ toFun:=fun x=>x i k,map_add':=fun _ _=>rfl,map_smul':=fun _ _=>rfl }; let M:= L.toContinuousLinearMap
    obtain ⟨W,Z,hW,hZ,H⟩:=shareG P hk
    let q (b:Cover)(u:E4)(z:Cover):= (w (u+Place.seat z))^n • gears P b z
    change M (∑' z,q x y z)=M (∑' z,q 0 s z); rw [M.map_tsum (f:=q x y) ((march_v hW (H x) y w n).of_norm), M.map_tsum (f:=q 0 s) ((march_v hW (H 0) s w n).of_norm)]
    have he(b: Cover) (u:E4)(z:Cover): M (q b u z)=(w (u+Place.seat z):ℂ)^n*guy P b i k z:=by unfold q; rw [map_smul, Complex.real_smul, Complex.ofReal_pow];rfl
    simp_rw [he]; have ht:= psalm P hk x i k w n hn; simp only [Place.seat_add] at ht; exact ht
lemma roll_pin (u v:Pipes.Shell)(x:Cover): ∑' z,arch P u v x z= if u=v then lot P.L else 0:=by
   obtain ⟨W,Z,hW,hZ,H⟩:=shareG P hk; let f:= gears P x; have hp:(∑' z,f z)= (Kit.slope P.L*(P.L.val:ℝ)⁻¹) • 1:=by -- use CLM
       refine Matrix.ext fun i j=> ?_;  let L:Bundle→ₗ[ℝ]ℂ:={ toFun:=fun x=>x i j,map_add':=fun _ _=>rfl,map_smul':=fun _ _=>rfl }; let M:= L.toContinuousLinearMap; change M (∑' z:Cover, gears P x z) = M ((Kit.slope P.L*(P.L.val:ℝ)⁻¹) • 1);  rw [M.map_tsum ((H x).unweighted hW.le).2.1.of_norm]; have hz:= survives_sym P hk i j x; change ∑' z,guy P x i j z= _; rw [hz,map_smul]; change _ = (Kit.slope P.L*(P.L.val:ℝ)⁻¹) • (1:Bundle) i j; by_cases i=j <;>simp [*,lot,Matrix.one_apply,Complex.real_smul]
   obtain ⟨L,hL⟩:=spin_patch u v; unfold arch; simp_rw [← hL]; rw [← L.map_tsum ((H x).unweighted hW.le).2.1.of_norm, hp,map_smul,hL,cons]; split <;> simp [lot,Complex.real_smul]
lemma roll_probe (u v:Pipes.Shell)(x:Cover)(w:RouteProbe)(hn:n<j):let y:=Place.seat (cellar P.L x); let s:=(P.L.val:ℝ)⁻¹ • Place.seat x; ∑' z:Cover, (w (y+Place.seat z))^n • arch P u v x z = ∑' z:Cover,(w (s+Place.seat z))^n • arch P u v 0 z:=by
    obtain ⟨W,Z,hW,hZ,H⟩:=shareG P hk; obtain ⟨L,hL⟩:=spin_patch u v; intro y s; have ht:=congr_arg L (playlist P hk x w hn)
    rw [L.map_tsum (march_v hW (H x) y w n).of_norm, L.map_tsum (march_v hW (H 0) s w n).of_norm] at ht; simp_rw [map_smul,hL] at ht; exact ht
end
end Steed
end YM.Massive.Poised
#print axioms YM.Massive.Poised.Steed.roll_probe
