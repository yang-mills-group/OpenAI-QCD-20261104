import YM.Eden.Exo
/-! # Compass and exotic color quarks.Serial -/
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
variable (U:Grid c)(x y:Cover)(η W:ℝ)
variable (u:FlavorTorus)(g:Lat.Frame c)
variable (p:UV.Pol d)(H:Bed)(F:Train j)(h:(milky 0 H n (G:=su) (d':=d)).IsSymm)
local notation "Xl"=>lotus d H n F h W η
local notation "T"=>wager 0 H n h
local notation "GZ"=> stemsP su d W
local notation "S"=>rateS d x U
local notation "Zt"=>gateP d W
local notation "Y"=>rosewood F n d
variable (Z:SpinPol d)(A:GPol)
variable (hj: 2 ≤ j)
local notation "Π"=> g (wrap c x)
lemma eyeK (u:su.El) : pigmentK (d:=d) (su.adjoint u) (loCast su d A)=loCast su d (dyesG u A):= colorL _ _ (fun i p x v=>Labels.Taylor.paint_value ..) _ -- eta
local notation "Gu"=> Lattice.gauge g U
lemma coinG : incomeF d x Gu η (milk T (GZ (loCast su d A)))=incomeF d x U η (milk T (GZ (loCast su d (dyesG Π A)))):=by
     let L:su.Color→ₗᵢ[ℝ]su.Color:=⟨su.adjoint Π,su.norm_adjoint Π⟩; rw [greenF]; rw [show pigmentK (su.adjoint Π) (d:=d)=pigmentK L.toLinearMap from rfl, ←minuteR, ← flowing,show pigmentK L.toLinearMap _= _ from eyeK A Π]
include hj
lemma coinS : slots 6 g (rateS d x Gu (Y (changeVars Zt Z)))= S (Y (changeVars Zt (changeVars (noir Π d) Z))):=by
    rw[← ingots _ _ (wagesColor Π), colorS F hj] -- colorS orientation
    unfold slots rateS adapter; rw [multipleChange,multipleChange]; exact congr_arg (fun X:Matrix (Sings d) (Pairs (Modes c 6)) ℂ=> changeVars X _) (gradient_m ..) -- hj provide unused?
lemma colorK : slots 6 g (Xl p c x Gu)=Xl (colorAct Π p) c x U:=by
    induction p using TensorProduct.induction_on with
    | zero=>simp only [map_zero,Pi.zero_apply,ContinuousMap.zero_apply]
    | tmul a b=> rw[colorAct,TensorProduct.map_tmul, leafs_t,leafs_t,map_smul]; exact congr_arg₂ (· • ·) (coinG U x η W g H h a) (coinS U x W g F b hj)
    | add p q hp hq=>simp only [map_add,Pi.add_apply,ContinuousMap.add_apply]; exact congr_arg₂ _ hp hq
lemma gardens (P:Label d)(c:Side): Lat.Invariant (Xl P.val c x):=by intro g; ext1 U; change slots 6 g _= _; rw [colorK, ((label_law _).mp P.property).2]; exact hj
lemma pepper : Action.parity ⇑(Xl p c x) =⇑(Xl (parityAct p) c x):=by
     funext U; induction p using TensorProduct.induction_on with
     | zero=>simp [Action.parity]
     | tmul a b=> rw [Action.parity,parityAct,TensorProduct.map_tmul, leafs_t,leafs_t,map_smul]; apply congr_arg₂ (· • ·) rfl; unfold rateS; have he {A B:Type}[Fintype A][Fintype B](M:Matrix A B ℂ)(x:Alg A): Grass.grade (changeVars M x)=changeVars M (Grass.grade x):=exterior_parity (substitution _) _ ; rw [he, ← gradeS, he]; rfl -- direction
     | add p q hp hq=>unfold Action.parity; simp only [map_add,Pi.add_apply,ContinuousMap.add_apply]; exact congr_arg₂ _ hp hq
local notation "CU"=> conjugate ∘ U
omit hj

lemma onyx : incomeF d x CU η (milk T (GZ (loCast su d A)))=incomeF d x U η (milk T (GZ (loCast su d (wore A)))):=by
   rw [blood]; let L:= vision; rw[show pigmentK (d:=d) reflectColor = pigmentK L.toLinearMap from rfl, ← minuteR, ← flowing, show pigmentK L.toLinearMap _=_ from (show pigmentK (d:=d) reflectColor (loCast su d A)=_ from colorL _ (fun _=>UV.recolor) (fun i p x v=> Papyrus.Scan.value_R ..) A)]
include hj
lemma copES : Action.charge ⇑(Xl p c x)=⇑(Xl (chargeAct p) c x):=by
    funext U; induction p using TensorProduct.induction_on with
    | zero=> simp [Action.charge]
    | tmul a b=> rw [Action.charge,chargeAct,TensorProduct.map_tmul, leafs_t,leafs_t,map_smul]; apply congr_arg₂ (· • ·) (onyx U x η W H h a)
                 unfold rateS; let u:= changeVars Zt b; change changeVars (railN c) _=changeVars (mood d x U) (Y (changeVars Zt (changeVars (masq d) b))); rw [multipleChange, ← ingots _ _ tracks_c, chargeS F hj, multipleChange]; exact congr_arg (fun X:Matrix (Sings d) (Pairs (Modes c 6)) ℂ=> changeVars X _) (reel_char ..)
    | add p q hp hq=>unfold Action.charge; simp only [map_add,Pi.add_apply,ContinuousMap.add_apply]; exact congr_arg₂ _ hp hq
omit hj
local notation "μ"=>gradientE d u
lemma fluts : adapter (Matrix.diagonal (fun i:Modes c 6=> (u i.2).val)) (Matrix.diagonal (fun i:Modes c 6=>star (u i.2).val)) ((rateS d x U) (Y (changeVars Zt Z)))= rateS d x U (Y (changeVars Zt (adapter (byFlavor u Prod.snd) (byFlavor u⁻¹ Prod.snd) Z))):=by
   let ν:= QCD.Eden.slab (flavP c u); have hQ : fromBlocks (flavP c u) (0:Matrix (Modes c 6) (Modes c 6) ℂ) 0 (Matrix.diagonal fun i:Modes c 6=> star (u i.2).val) = ν:=by unfold ν QCD.Eden.slab flavP; rw[phase_conj]; rfl -- one implicit Fχ
   have he : fromBlocks (byFlavor u (fun i:SpinMode d=>i.2)) (0:Matrix (SpinMode d) (SpinMode d) ℂ) 0 (byFlavor u⁻¹ (fun i=>i.2)) = μ:=by unfold gradientE QCD.Eden.slab; rw [phase_conj]
   change changeVars (fromBlocks (flavP c u) _ _ _) (rateS d x U _) = S (Y (changeVars Zt (changeVars (fromBlocks (byFlavor u (fun i:SpinMode d=>i.2)) _ _ _) Z))); unfold rateS; rw [hQ,he, ← ingots _ _ (wagesFlavor u), flavorS F _ u, multipleChange, multipleChange]; exact congr_arg (fun X:Matrix (Sings d) (Pairs (Modes c 6)) ℂ=> changeVars X _) (festival ..)
lemma fluke : Action.flavor u ⇑(Xl p c x)=⇑(Xl (flavorAct u p) c x):=by
     funext U; induction p using TensorProduct.induction_on with
     | zero=> simp [Action.flavor,Action.flavorF]
     | tmul a b=> rw [Action.flavor,Action.flavorF,flavorAct,TensorProduct.map_tmul,leafs_t,leafs_t,map_smul]; apply congr_arg₂ (· • ·) rfl
                  exact fluts U x W u F b
     | add p q hp hq=>unfold Action.flavor Action.flavorF; simp only [map_add,Pi.add_apply,ContinuousMap.add_apply]; exact congr_arg₂ _ hp hq
end YM.Eden
#print axioms YM.Eden.fluke
#print axioms YM.Eden.pepper
#print axioms YM.Eden.copES
#print axioms YM.Eden.gardens
