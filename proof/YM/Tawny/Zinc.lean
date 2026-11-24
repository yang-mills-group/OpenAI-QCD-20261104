import YM.Tawny.Trio
import YM.Tawny.Fore
set_option autoImplicit false
noncomputable section
namespace YM.Massive.Tawny
open QCD QCD.Lat QCD.Grass Lattice TensorProduct Function UV PCAC
open scoped BigOperators Topology Matrix Matrix.Norms.L2Operator ContDiff Classical TensorProduct
variable {d:ℕ}(a b:Flavor 6)
open Poised.Display Poised.Stative Module Finset Oriole Pane TensorProduct Revolve UV.Free KeysP BendR Clifford
namespace Cast
open StressFlux.Offer (acts marks Vc)
namespace Zinc
open scoped Kronecker
open Rays StressFlux.Offer
open StressFlux (pair pairDeriv curled curl0 curl1)
variable (i j k l:Axis)(B: Spike)
noncomputable def whirl (c:su.Color)(M:Spike): Bundle:= M ⊗ₖ ore c
local notation "D"=>10
local notation "U"=> (0:Multi 10)
local notation "F"=> Labels.axes su 0
local notation "X"=> SpinPol D
local notation "K" => PowerPair D
noncomputable def yard (a:Flavor 6): Bundle→ₗ[ℂ] CensusA D where
   toFun := fieldB a a U U
   map_add' U' V:= by ext i j; rw [Matrix.add_apply,fieldK,fieldK,fieldK]; simp_rw [Matrix.add_apply]; split; rfl; exact (zero_add _).symm
   map_smul' z S:= C_light ..
noncomputable def weave (a:Flavor 6)(M:Spike)(i j:Axis)(x: Labels.Taylor su 0): CensusA D:= yard a (whirl (curl0 i j x) M)
local notation "Q"=> weave a B i j
noncomputable def youthL : Pol D:= ∑ k:Fin (Labels.dim su 0), (MvPolynomial.X ⟨0,k⟩ ⊗ₜ[ℂ] coat (Q (F k)))
local notation "Y"=> youthL a i j B
noncomputable def trackY : Labels.Taylor su 0 →ₗ[ℝ] CensusA D:=
   let P : su.Color→ₗ[ℝ]Bundle:= { toFun:=fun x=> whirl x B,map_add':=fun x y=>by ext p q; simp only[whirl,Matrix.kroneckerMap_apply]; rw [show ore (x+y)=ore x+ore y from map_add _ _ _,Matrix.add_apply,mul_add,Matrix.add_apply]; rfl,map_smul':=fun r x=>by ext i j; simp only[whirl, Matrix.kroneckerMap_apply]; rw [show ore (r • x)= r • ore x from su.colorMat.map_smul r x, Matrix.smul_apply, Matrix.smul_apply]; exact mul_smul_comm .. }
   ((yard a).restrictScalars ℝ) ∘ₗ P ∘ₗ curl0 i j
variable (J:Labels.Jet su)
lemma neutral_Y(o:Fin (Labels.dim su 0))(p q:SpinMode D)(hp:p.1.1=U)(hq:q.1.1=U)(he:p.2=q.2) (z:ℂ) :
    let x:GPol:=MvPolynomial.X ⟨0,o⟩; let f:X:= coat (Matrix.single p q z); x⊗ₜ[ℂ]f ∈ UV.cap D∧ Quiet (x ⊗ₜ[ℂ] f):=by
    intro x f; have ht:f=z • (bar p*psi q):=by have hi:= congr_arg (ready D (0:Labels.Jet su)) (j_single p q z); change ready _ _ (1⊗ₜ[ℂ] f)=_ at hi; rw [ready_t,ready_t,map_one,one_smul,one_smul] at hi; exact hi
    constructor
    · rw [ht,TensorProduct.tmul_smul]; refine Submodule.smul_mem _ _ ?_; let u:K:=(Finsupp.single ⟨0,o⟩ 1,{Sum.inr p,Sum.inl q}); have hz : gen u∈UV.cap D:=by
               refine Submodule.subset_span ⟨_,?_,rfl⟩; change weight u≤10; have h1:2*Labels.height u.1=4:=by unfold u Labels.height; rw [Finsupp.weight_single,one_smul]; rfl
               unfold UV.weight; rw [h1]; unfold u; rw [Finset.sum_pair (by intro h; cases h)]; change 4+(spinWeight p.1.1+spinWeight q.1.1) ≤_; rw[hp,hq,gradeV]
      unfold bar psi; rcases bladeX (Sum.inr p) (Sum.inl q) (by intro h; cases h) with h|h; rw [h]; exact hz; rw [h,TensorProduct.tmul_neg]; exact Submodule.neg_mem _ hz
    rw [ht]; constructor
    · rw[parityAct,TensorProduct.map_tmul,AlgHom.toLinearMap_apply]; simp_rw [map_smul,map_mul,psi,bar,Grass.grade_atom, neg_mul_neg]; rfl
    intro v; rw [flavorAct,TensorProduct.map_tmul,AlgHom.toLinearMap_apply,map_smul]; congr 1
    rw [psi,bar,map_mul,buck,buck]; change _ • ((star ((v p.2).val) • atom _) *((v q.2).val • atom _))=_; rw[smul_mul_assoc,mul_smul_comm, smul_smul,he,smul_smul,mul_assoc,(v q.2).property.1, mul_one]
lemma first_Y(u:Fin (Labels.dim su 0))(P:Bundle): let x:GPol:=MvPolynomial.X ⟨0,u⟩; let f:= coat (yard a P); x⊗ₜ[ℂ]f ∈ UV.cap D ∧ Quiet (x⊗ₜ[ℂ]f):=by
    intro x f; let q(i:Fiber): SpinMode D:= ((0,i),a); let M(i j:Fiber): CensusA D:= Matrix.single (q i) (q j) (P i j); let FT(i j:Fiber):Pol D:= x⊗ₜ[ℂ] coat (M i j); have hz(i j): FT i j∈ UV.cap D ∧ Quiet (FT i j):= neutral_Y u (q i) (q j) rfl rfl rfl (P i j)
    rw [show f=coat (∑ i:Fiber,∑ j:Fiber,M i j) from rfl]; simp_rw [map_sum,TensorProduct.tmul_sum]; refine ⟨Submodule.sum_mem _ (fun i _=> Submodule.sum_mem _ (fun j _=> (hz i j).1)),?_,?_⟩
    · change parityAct (∑ i:Fiber,∑ j:Fiber,FT i j)= _; simp_rw [map_sum,fun i j=>(hz i j).2.1]; rfl
    intro v; change flavorAct v (∑ i:Fiber,∑ j:Fiber,FT i j)=_; simp_rw[map_sum,fun i j=> (hz i j).2.2 v]; rfl
lemma rubyY : Y ∈ UV.cap D ∧ Quiet Y:=by
    let f(k:Fin (Labels.dim su 0)):Pol D:= MvPolynomial.X ⟨0,k⟩ ⊗ₜ[ℂ] coat (Q (F k)); have hz(k: Fin (Labels.dim su 0)): f k ∈ UV.cap D∧ Quiet (f k):= first_Y a _ _; change ∑ k:Fin (Labels.dim su 0),f k∈ _∧ Quiet (∑ k: Fin _,f k); refine ⟨Submodule.sum_mem _ (fun k _=>(hz k).1),?_,?_⟩; · simp_rw [map_sum,fun i=>(hz i).2.1]
    intro v; simp_rw [map_sum, fun k=>(hz k).2.2 v]
lemma yMobi : ready D J Y=coat (Q (J 0)):=by
    unfold youthL; simp_rw[map_sum,ready_t,Labels.read,MvPolynomial.aeval_X]; conv_rhs=> rw [← (F).sum_repr (J 0)]
    let L:= (coat.restrictScalars ℝ) ∘ₗ (trackY a i j B); change _= L _; rw [map_sum]; refine sum_congr rfl fun t _=>?_ ; rw [map_smul]; rfl
variable (s:Signed)(w:EuPin)(hw:w.Lifts s)(p:su.El)
private lemma faithful(P Kx:CensusA D)(h:∀ a b:Flavor 6,∀ i j: Multi D, Oriole.prism a b i j P= Oriole.prism a b i j Kx):P=Kx:=by ext ⟨⟨p,i⟩,a⟩ ⟨⟨q,j⟩,b⟩; exact congr_fun (congr_fun (h a b p q) i) j
lemma yield_p (p q:Multi D)(u v:Flavor 6)(P:Bundle): Oriole.prism u v p q (yard a P)= if p=0∧q=0∧u=a∧v=a then P else 0:=by
    ext i j; change fieldB a a U U P ((p,i),u) ((q,j),v)=_; rw [fieldK]; simp only; split <;> rename_i h; · obtain ⟨rfl,rfl,rfl,rfl⟩:=h; simp
    rw [if_neg (by tauto)]; rfl
lemma walk (S:Spike)(Z:Mat):S⊗ₖ Z=(wave S)*(touch Z):=by unfold wave touch; rw [← Matrix.mul_kronecker_mul,mul_one,one_mul]
lemma color_Y : colorAct p Y=Y:=by
    apply Poised.Display.distinct; intro J; rw [visual,yMobi,yMobi]; let W:= weave a B i j (J 0); let Z:= weave a B i j ((Labels.colored p J) 0); let X':=colorTable p (d:=D); let V:= colour p; let σ:=touch V
    change adapter X' (star X').transpose (- form Z)= coat W; rw[map_neg,form_map,Matrix.transpose_transpose]; change coat ((star X')*(Z*X'))=coat W; have he:Z*X'= X'*W:=by
        apply faithful; intro u v P S; have hz: (Oriole.prism u v P S Z * σ= σ*Oriole.prism u v P S W):=by
            unfold Z W weave; rw [yield_p,yield_p]; split
            · let A:=curl0 i j (J 0); rw [whirl,whirl]; change ((B⊗ₖ ore (curl0 i j (Labels.Taylor.paint p (J 0)))))*σ= σ*(B ⊗ₖ ore A); rw[ show curl0 i j (Labels.Taylor.paint p (J 0))=su.adjoint p A from StressFlux.curled_paint (J 0) 0 i j p]; rw[show ∀ x:su.Color, ore (su.adjoint p x)=V* ore x*star V from fun _=>Gauge.mat_adjoint _ p _]; unfold σ touch; rw [← Matrix.mul_kronecker_mul,← Matrix.mul_kronecker_mul] -- σ not expanded
              rw [mul_one,one_mul]; congr! 1; rw [mul_assoc _ (star V), show star V*V=1 from Gauge.mat_star_mul _ _,mul_one];
            rw[zero_mul,mul_zero]
        ext l k; exact (hue_right u v P S Z p l k).trans ((congr_fun (congr_fun hz l) k).trans (hue_left u v P S W p l k).symm)
    rw [he,← mul_assoc, (pru (d:=D) p).1,one_mul]
noncomputable def med (a:Flavor 6)(i j:Axis)(B:Spike): Label D:=⟨youthL a i j B,(label_law _).2 ⟨(rubyY a i j B).1, color_Y a i j B⟩⟩
end Zinc
end Cast
end YM.Massive.Tawny
#print axioms YM.Massive.Tawny.Cast.Zinc.med
