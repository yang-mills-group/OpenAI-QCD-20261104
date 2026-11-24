import YM.Tawny.Iona
set_option autoImplicit false
noncomputable section
namespace YM.Massive.Tawny
open QCD QCD.Lat QCD.Grass Lattice TensorProduct Function UV PCAC
open scoped BigOperators Topology Matrix Matrix.Norms.L2Operator ContDiff Classical TensorProduct
variable {d:ℕ}(a b:Flavor 6)
open Poised.Display Poised.Stative Module Finset Oriole Pane TensorProduct Revolve UV.Free KeysP BendR Clifford
namespace Cast
open StressFlux.Offer (acts marks Vc)
namespace Perla
open StressFlux (pair pairDeriv curled curl0 curl1 stress leg0 leg1) -- remove
variable (X:Labels.Jet su)(S:Spike)(u v:Axis)
-- Maxwell independent tests.Radial encode ribbons power.W.C
open scoped Kronecker InnerProductSpace
variable (x:Labels.Taylor su 0)(y:Labels.Taylor su 1) (c:su.Color)
namespace BrickM
open Maxwell
abbrev G:= su
local notation "C"=>su.Color
local notation "R"=>Shell su -- no
-- constructors via enough condition curls.
private theorem on0 : takeCurl x∈ onShell C 0:=by
      refine ⟨(Maxwell.potential x).property,fun b z=>?_⟩
      rw [sum_eq_zero]; intro i _; rw[show Tensor.diagonal (takeCurl x i b)=fun _=>Tensor.diagonal (takeCurl x i b) 0 from funext fun u=> congr_arg (takeCurl x i b) (Subsingleton.elim ..)]; simp [grad,YM.Analysis.D]
lemma rootY : ∃ q: Maxwell.Shell su 0,Maxwell.gaugeJet q=x:=by
      refine ⟨⟨_,on0 x⟩,?_⟩; apply Maxwell.potential.injective; apply Subtype.ext; exact Maxwell.match_leg _
lemma oneH(i j k:Axis)(w:E4): grad i (Tensor.diagonal (takeCurl y j k)) w= curl1 i j k y:=by
      let T':= ContinuousMultilinearMap.ofSubsingleton ℝ E4 C (0:Fin 1); obtain ⟨f,hf⟩ := T'.surjective (takeCurl y j k); change fderiv ℝ (Tensor.diagonal _) w (basis i)= Tensor.diagonal (takeCurl y j k) _; rw[← hf]; exact congr_arg (fun x:E4→L[ℝ]C=> x _) (f.fderiv (x:=w))
lemma on_one (h:∀ b:Axis,∑ i:Axis, curl1 i i b y=0):∃ q: Shell su 1,gaugeJet q=y:=by
     have hz: takeCurl y∈onShell C 1:= by refine ⟨(potential y).property,fun b z=>?_⟩; simp_rw [oneH,h]
     refine ⟨⟨_,hz⟩,?_⟩; apply potential.injective; apply Subtype.ext; exact match_leg _
noncomputable def firstY : Labels.Taylor su 1:= leg1 (0:Axis) 0 1 c - leg1 (2:Axis) 2 1 c
noncomputable def secondY : Labels.Taylor su 1:= leg1 (0:Axis) 1 2 c - leg1 (1:Axis) 2 0 c
set_option maxHeartbeats 800000 in
lemma first_on :∃ q : Shell su 1, gaugeJet q = firstY c:= on_one _ (fun i=>by simp_rw [firstY, map_sub, StressFlux.curl1_leg]; fin_cases i <;> norm_num [Fin.sum_univ_four,basis_eq, Fin.ext_iff] <;> module)
set_option maxHeartbeats 800000 in
lemma second_on :∃ q:Shell su 1, gaugeJet q= secondY c:= on_one _ (fun i=>by simp_rw [secondY,map_sub, StressFlux.curl1_leg]; fin_cases i <;> norm_num [Fin.sum_univ_four,basis_eq,Fin.ext_iff]<;>module)
end BrickM
open BrickM
namespace Fore
local notation "C"=>su.Color
local notation "L"=> leapV
local notation "H"=>lunar
local notation "E"=>eulerV
local notation "R"=>Labels.read
noncomputable def pages (X:Labels.Jet su): Label d→ₗ[ℂ]ℂ:=(Labels.read X).toLinearMap.comp (fog.comp (UV.labels d).subtype)
lemma railX(x:GPol)(b:Label d)(hb:b.val=plain d x): pages X b=Labels.read X x:=by change R X (fog b.val)=_; rw [hb,plainP,unit_fog]
lemma plots : pages (d:=8) X (spire.val (u,v))= ∑ i:Axis, (↑(inner ℝ (curl0 u i (X 0)) (curl0 v i (X 0))):ℂ):=by rw [spire_val,map_sum]; exact sum_congr rfl fun i _=> (railX _ _ _ rfl).trans (StressFlux.pair_value ..)
lemma plotD : pages X (eclipse.val (u,v))=if u=v then ∑ i:Axis,∑ j:Axis, (↑(inner ℝ (curl0 i j (X 0)) (curl0 i j (X 0))):ℂ) else 0:=by
     rw [dark]; split; · rw [map_sum]; apply sum_congr rfl; intro i _; rw [map_sum]; exact sum_congr rfl fun j _=> (railX _ _ _ rfl).trans (StressFlux.pair_value ..)
     exact map_zero _
lemma plotS : pages X (shadow.val (u,v))=if u=v then pages X (spire.val (u,v)) else 0:=by rw [shadow_val]; split; rw[spire_val]; exact map_zero _
lemma plotA : pages X (epi.val (u,v))=if u=v then 1 else 0:=by
     change R X (fog (epi.val (u,v)).val)=_; rw [epi_at]; split; · rw [show UV.unit 8=plain 8 (1:GPol) from rfl,plainP,unit_fog,map_one]
     rw[map_zero,map_zero]
local notation "Y₀"=>X 0
local notation "Y₁"=>X 1
lemma plotL : pages X ((L).val u)=∑ i:Axis, (↑(inner ℝ (curl0 u i Y₀) (curl1 u u i Y₁)):ℂ):=by
     change pages _ (∑ i:Axis,GE u i u u i)=_; rw [map_sum]; exact sum_congr rfl fun i _=> (railX _ _ _ rfl).trans (StressFlux.pairDeriv_value ..)
lemma plotH : pages X ((H).val u)=∑ i:Axis,∑ j:Axis,(↑(inner ℝ (curl0 i j Y₀) (curl1 u i j Y₁)):ℂ):=by
     change pages _ (∑ i:Axis,∑ j:Axis,GE i j u i j)=_; rw[map_sum]; apply sum_congr rfl; intro i _; rw [map_sum]; exact sum_congr rfl fun j _=> (railX _ _ _ rfl).trans (StressFlux.pairDeriv_value ..)
lemma plotE : pages X ((E).val u)=Labels.read X (StressFlux.eom su u).val:=by
     change pages _ (∑ i:Axis,∑ j:Axis,GE u i j j i)=_; rw [map_sum,StressFlux.eom]; simp only [AddSubmonoidClass.coe_finsetSum,_root_.map_sum]; exact sum_congr rfl fun i _=>sum_congr rfl fun j _=> railX _ _ _ rfl
abbrev lexY(X:Maxwell.TaylorTower su): Labels.Jet su:=fun i=>Maxwell.gaugeJet (X i)
lemma E_full (X:Maxwell.TaylorTower su): pages (lexY X) ((E).val u)=0:=by rw [plotE]; exact Maxwell.ideal_meaning.mp (StressFlux.eom_null u) X
lemma E_alive :∃ (u:Axis)(X:Labels.Jet su),pages X ((E).val u) ≠0:=by by_contra! hb; apply StressFlux.eom_nonzero (G:=su) QCD.simple; funext i; apply StressFlux.label_ext; intro J; rw [← plotE,hb]; exact Eq.symm (map_zero _)
lemma plot_X (c:su.Color)(he:‖c‖=1):∃ J:Maxwell.TaylorTower su,pages (lexY J) ((L).val 0)=1 ∧ pages (lexY J) ((H).val 0)=2:=by
    obtain ⟨u,hu⟩:= rootY (leg0 (0:Axis) 1 c); obtain ⟨v,hv⟩:= first_on c; let T':Maxwell.TaylorTower su:=Pi.single 0 u+Pi.single 1 v; refine ⟨T',?_⟩; have h0:T' 0=u:=by simp[T']
    have h1:T' 1=v:=by simp [T']
    rw [plotL,plotH]; simp only[lexY,h0,h1,hu,hv,firstY]; simp_rw [StressFlux.curl0_leg,map_sub,StressFlux.curl1_leg]; norm_num [Fin.sum_univ_four,basis_eq,Fin.ext_iff,he] -- norm convention test.
lemma plot_Y (c:su.Color)(he:‖c‖=1):∃ J:Maxwell.TaylorTower su,pages (lexY J) ((L).val 0)=0∧ pages (lexY J) ((H).val 0)=2:=by
    obtain ⟨u,hu⟩:=rootY (leg0 (1:Axis) 2 c); obtain ⟨v,hv⟩:= second_on c; let T':Maxwell.TaylorTower su:= Pi.single 0 u+Pi.single 1 v; refine ⟨T',?_⟩; have h0:T' 0=u:=by simp [T']
    have h1:T' 1=v:=by simp[T']
    rw[plotL,plotH]; simp only [lexY,h0,h1,hu,hv,secondY]; simp_rw [StressFlux.curl0_leg,map_sub,StressFlux.curl1_leg]; norm_num [Fin.sum_univ_four,basis_eq,Fin.ext_iff,he]; rw [inner_add_right,inner_sub_right,real_inner_smul_right,inner_neg_right]; norm_num [he, real_inner_smul_right] <;> ring
end Fore
end Perla
end Cast
end YM.Massive.Tawny
#print axioms YM.Massive.Tawny.Cast.Perla.Fore.plot_Y
#print axioms YM.Massive.Tawny.Cast.Perla.Fore.plot_X
