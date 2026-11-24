import YM.Eden.Lamp
/-! # Natural scheme.Id and all orientation groups. at every label.Photo.At any horizon minor. -/
set_option autoImplicit false
noncomputable section
namespace YM.Eden
open Function Lattice Wilson RG Metric Precision Bloch Laurent Tensor Work.F03 Exterior
open Finset Matrix AnalyticBridge.LocalGaussianLaws.Current
open YM.Next.Free Bloom Arise Arise.Range Bloom.TreeP
open scoped Topology BigOperators InnerProductSpace Matrix Matrix.Norms.Frobenius TensorProduct Classical
variable {G:Gauge}{d k i m j:ℕ}{c f n:Side} {H:Bed}{t:Clip}{a b:ℝ}{I J :Type}[Fintype I][Fintype J]
open Massive UV QCD QCD.Eden QCD.Grass QCD.Bloom Lat Poised.Display
open Elm Elm.SparK Elm.SparK.Arbor Elm.SparK.Arbor.PrismD Poised Papyrus Lining Next.Rank.Normal Cylinder
variable (U:Grid c)(p:Bard d)(x y:Cover)(η W:ℝ)
variable (s:Signed)(P:EuPin)(u:FlavorTorus)(aV:Axis)(g:Frame c)
local notation "V" => pull s 0 U
local notation "v₀"=>s.act x
lemma windF (p:Lily su d) : incomeF d x V η p=incomeF d (s.act x) U η (posedK s p):=by
    unfold incomeF; rw [swirls, Ferry.wind, Papyrus.scene,stat]; apply congr_arg (fun y:Ink su d=> nestK y p); funext i; change η*(stainK s i * _)= stainK s i*(η*_); ring
lemma starF (p:Lily su d) : star (incomeF d x U η p)= incomeF d x U η (MvPolynomial.map (starRingEnd _) p):=by
    induction p using MvPolynomial.induction_on with
    | C c=> simp [incomeF,nestK]
    | add a b ha hb=>rw [map_add,map_add,map_add,star_add,ha,hb]
    | mul_X p i hp=> rw [map_mul,map_mul,map_mul,star_mul',hp,MvPolynomial.map_X,incomeF,nestK, MvPolynomial.aeval_X]; simp
lemma linkedR (d:ℕ)(A: su.Color→ₗ[ℝ] su.Color)(XV:Ink su d): liftedK A (η • XV)=η • liftedK A XV:=by funext i; unfold liftedK lampK; rw[show WithLp.toLp 2 _= η • WithLp.toLp 2 (fun j: su.ColorIndex=>XV (i.1,j)) from (by rfl),map_smul]; rfl -- Prod
lemma blood(p:Lily su d) : incomeF d x (Massive.conjugate ∘ U) η p=incomeF d x U η (pigmentK reflectColor p):=by unfold incomeF; rw [Arise.Range.pink, show expandAt _ _= Massive.conjugate ∘ expandAt (wrap c x) U from rfl, outer_R,linkedR]
lemma greenF (p:Lily su d) : incomeF d x (Lattice.gauge g U) η p= incomeF d x U η (pigmentK (su.adjoint (g (wrap c x))) p):=by
     unfold incomeF; rw[Arise.Range.pink,Ferry.ferry_stretch,Papyrus.gaugeF, lantern, linkedR]; simp only [Function.comp_apply,Lining.Ferry.gain,zero_add]
variable (p:UV.Pol d)(H:Bed)(F:Train j)(h:(milky 0 H n (G:=su) (d':=d)).IsSymm)
local notation "Xl"=>lotus d H n F h W η
local notation "T"=>wager 0 H n h
local notation "GZ"=> stemsP su d W
local notation "S"=>rateS d x U
local notation "Zt"=>gateP d W
local notation "Y"=>rosewood F n d
-- spin corner helper.
variable (Z:SpinPol d)(A:GPol)
variable (ht:Floor H t n a b) (ha:0<a)(hp:Bid.Sworn H n su)(hj: 2 ≤ j)
include ht ha hp
lemma roseF(hV:P.Lifts s) : incomeF d x V η (milk T (GZ (loCast su d A)))=incomeF d (s.act x) U η (milk T (GZ (loCast su d (Labels.rotated P.coord A)))):=by
    rw [windF,← shineK s ht ha hp h, ←shines_g, poles_eq,hV]
omit ht ha hp
include hj
lemma roseS(hV:P.Lifts s) : changeVars (PinWheel c s P) (rateS d x V (Y (changeVars Zt Z)))=rateS d (s.act x) U (Y (changeVars Zt (changeVars (pinTT d s P) Z))):=by
    unfold rateS; rw [← ingots _ _ (wagesPin s P), ← tintS F hj s _ P hV, multipleChange,multipleChange]; exact congr_arg (fun X:Matrix (Sings d) (Pairs (Modes c 6)) ℂ=> changeVars X (Y (changeVars Zt Z))) (motionM x U s P hV)
include ht ha hp
lemma skies (hp':P.Lifts s) : Action.pin P s ⇑(Xl p c x)=⇑(Xl (pinAct P p) c (s.act x)):=by
    funext U; induction p using TensorProduct.induction_on with
    | zero=> change changeVars _ _= _; simp only [map_zero,Pi.zero_apply,ContinuousMap.zero_apply]; -- seems
    | tmul a b=> rw [← pinWheel,pinAct,TensorProduct.map_tmul,leafs_t,leafs_t,map_smul]; exact congr_arg₂ (· • ·) (roseF U x η W s P H h a ht ha hp hp') (roseS U x W s P F b hj hp')
    | add p q hp hq=>unfold Action.pin; simp only [map_add,Pi.add_apply,ContinuousMap.add_apply]; exact congr_arg₂ _ hp hq
local notation "Hq"=> pull (Signed.mirror aV) 0 U
lemma starR : star (incomeF d x Hq η (milk T (GZ (loCast su d A))))=incomeF d ((Signed.mirror aV).act x) U η (milk T (GZ (loCast su d (Labels.rotated (Signed.reflect aV) (conjGPol A))))):=by
    have hh:= cc_milk (GZ (loCast su d A)) T (fun i j=> (show star (-milky 0 H n i j)= _ from (by rw [star_neg,realS]; rfl))); rw [starF, hh,← burns_g,← real_back, windF,← shineK _ ht ha hp h, ← shines_g, poles_eq]; rfl
omit ht ha hp
lemma starQ : changeVars (moonS c aV) (dagger (rateS d x Hq (Y (changeVars Zt Z)))) = rateS d ((Signed.mirror aV).act x) U (Y (changeVars Zt (aSpin d aV Z))):=by
    let w:= Signed.mirror aV; have hz: aSpin d aV (changeVars Zt Z)=changeVars Zt (aSpin d aV Z):=by unfold aSpin; simp only [LinearMap.comp_apply, AlgHom.toLinearMap_apply]; rw [dagger_change,dignity]; exact ingots _ _ (eyeTracks aV) _
    rw[←hz,← adjS F hj]; unfold rateS aSpin; simp only [LinearMap.comp_apply, AlgHom.toLinearMap_apply]; rw [dagger_change, multipleChange,multipleChange, festiveV]
include ht ha hp
lemma spaces : Action.adj aV ⇑(Xl p c x) =⇑(Xl (UV.adj aV p) c ((Signed.mirror aV).act x)):=by
    funext U; induction p using TensorProduct.induction_on with
    | zero=> simp only [Action.adj,map_zero,Pi.zero_apply,ContinuousMap.coe_zero]
    | tmul a b=> unfold Action.adj UV.adj; rw [TensorProduct.map_tmul,leafs_t,leafs_t,map_smulₛₗ,map_smul]; exact congr_arg₂ (· • ·) (starR U x η W aV H h a ht ha hp hj) (starQ U x W aV F b hj)
    | add p q hp hq=>unfold Action.adj; simp only [map_add,Pi.add_apply,ContinuousMap.add_apply]; exact congr_arg₂ _ hp hq
end YM.Eden
#print axioms YM.Eden.spaces
#print axioms YM.Eden.skies
