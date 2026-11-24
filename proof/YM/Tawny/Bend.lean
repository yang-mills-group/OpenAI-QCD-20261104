import YM.Tawny.Gates
import YM.Push.STRESS_FLUX.Polynomial
set_option autoImplicit false
noncomputable section
namespace YM.Massive.Tawny
open QCD QCD.Lat QCD.Grass Lattice TensorProduct Function UV PCAC
open scoped BigOperators Topology Matrix Matrix.Norms.L2Operator ContDiff Classical TensorProduct
variable {d:ℕ}(a b:Flavor 6)
open Poised.Display Poised.Stative Module Finset Oriole
local notation "T" => SpinMode d
local notation "Ae" => Pairs T
local notation "W"=>CensusA d
open Pane TensorProduct Revolve UV.Free
namespace BendR
variable (D:Pol d)(X:CensusA d)(J:Labels.Jet su)(P Q:Spike)
abbrev invertW (d:ℕ)(p:EuPin):SpinPol d→ₐ[ℂ]SpinPol d:= adapter (UV.turned p (wave p.matrix⁻¹.val)) (UV.turned p (wave p.matrix.val.transpose))
variable (w:EuPin)(s:Signed)(hw:w.Lifts s)
local notation "Y" => ready d J
local notation "Y0"=> ready d (0:Labels.Jet su)
local notation "Δ"=> skin (d:=d) J
local notation "Ω"=> skin (d:=d) (0:Labels.Jet su)
local notation "Φ"=> invertW d w
include hw
lemma scored : Y (pinAct w D)=Φ (ready d (StressFlux.shifted s J) D):=by
    induction D using TensorProduct.induction_on with
    | zero=>simp
    | tmul a b=> unfold pinAct; rw[TensorProduct.map_tmul,ready_t,ready_t,map_smul]; congr 1; simp only [AlgHom.toLinearMap_apply,Labels.rotated,Labels.eval_changed, show w.coord=s.ortho from hw]
    | add a b h h'=> simp_rw[map_add,h,h']
omit hw
abbrev darkC (d:ℕ) := changeVars (masq d)
local notation "J★"=> Labels.changedJet (fun _=>UV.recolor) J
lemma plum : Y (chargeAct D)= darkC d (ready d (J★) D):=by
    induction D using TensorProduct.induction_on with
    | zero=>simp
    | tmul a b=> unfold chargeAct; rw [TensorProduct.map_tmul,ready_t,ready_t,map_smul]; congr 1; exact Labels.eval_changed ..
    | add a b h h'=> simp_rw[map_add,h,h']
lemma pinoy : Φ (coat X)=coat (tintP w X):=by
    change adapter _ _ (- form _) =_; rw [map_neg, form_map]; rfl
noncomputable def dam (X:CensusA d): CensusA d:= (spinTable chargeMatrix).transpose*((-X.transpose)*(spinTable (-chargeMatrix)))
lemma dance: darkC d (coat X)=coat (dam X):=by
    have he:= ride X; change chargeAct ((1:GPol)⊗ₜ[ℂ]coat X)=(1:GPol)⊗ₜ[ℂ]coat (dam X) at he; have he:=congr_arg Y0 he; rw [plum,ready_t,ready_t,map_one,map_one,one_smul,one_smul] at he; exact he
variable (x:Label d)(h:Quiet x.val)(hd:d≤10)
local notation "Ff"=> fog x.val
local notation "Ψ"=> glow x h hd
local notation "Xj"=> Ω x.val
include h hd hw
lemma wrought : fog (pinAct w x.val)=Labels.rotated s.ortho Ff:=by
    apply Labels.eval_ext; intro J; rw [← expected,scored _ J w s hw,visualP _ x h hd,map_add,map_smul,map_one,pinoy,map_add,map_smul,rawMintSkin,← mono_empty, Grass.read,smul_eq_mul,mul_one,add_zero,Labels.rotated, Labels.eval_changed]
lemma wending : Δ (pinAct w x.val)=tintP w (skin (StressFlux.shifted s J) x.val):=by
    nth_rw 1 [skin]; rw [LinearMap.comp_apply,scored _ J w s hw,visualP _ x h hd,map_add,map_smul,map_one,pinoy,map_add, map_smul,unit_un,smul_zero,zero_add,coat_known]
omit hw
local notation "C"=> chargeMatrix
lemma crest : Δ (chargeAct x.val)= dam (skin (J★) x.val):=by
    nth_rw 1[skin]; rw[LinearMap.comp_apply,plum,visualP _ x h hd,map_add,map_smul,map_one,dance,map_add,map_smul,unit_un,smul_zero,zero_add,coat_known]
omit h hd
variable (p q:Multi d)
local notation "μ"=> gravel a b p q
local notation "ν"=> gravel b a q p
local notation "μs"=> gravel a b (hem s p) (hem s q)
lemma rubDam : ν (dam X)= -(wave C*(μ X).transpose* wave C):=by
    unfold dam; let U:=(-X.transpose); rw [under_spin,under_spin]; have ht(m:Multi d): marked 1 m=1:=by simp [marked, show ∀ i,signT 1 i=1 from fun _=>rfl]
    change prism b a (hem 1 q) (hem 1 p) _= _; have hu: EuPin.Lifts 1 1:=Eq.symm (map_one Signed.inclusionO)
    rw [plucksL b a q _ _ 1 1 _ hu,plucksR b a _ p _ 1 1 _ hu]; simp_rw [ht,Complex.ofReal_one,one_smul]; change (wave C).transpose * (prism b a q p U * wave (-C))=_
    have he: prism b a q p U= -(μ X).transpose:=by ext; rfl
    rw[←wave_tr, Clifford.transpose_charge, he,show wave (-chargeMatrix) = - wave chargeMatrix from ?_,Matrix.neg_mul,neg_mul_neg,mul_assoc] -- order swap? -A*(-B*-A). yes
    rw [← neg_one_smul ℂ chargeMatrix, Oriole.waveP,neg_one_smul]
lemma wageE(z:ℂ)(X U: Spike)(h:UV.chargeAct (bilinear a b X p q)= z • bilinear b a U q p): -(C*X.transpose*C)=z • U:=by -- maybe not needed
    rw [breeze,← nourish,← j_stard,← j_stard] at h; have he:= congr_arg (prism b a q p) (inj_coat h); rw[coreB,coreB] at he; exact KeysP.mix_blank _ _ he
noncomputable def silver (a:Flavor 6)(p q:Multi d)(x:Pol d):Spike:=Stew.gold (gravel a a p q (skin 0 x))
include h hd
local notation "M"=>silver a p q x.val
abbrev truck (S:Spike):Spike:= -(chargeMatrix*S.transpose*chargeMatrix)
lemma chargeL (hc:chargeAct x.val=x.val) : truck (M)= silver a q p x.val:=by
     have he:= crest (0:Labels.Jet su) x h hd; rw[hc, show Labels.changedJet (fun _=>UV.recolor) (0:Labels.Jet su)=0 from funext fun i=>map_zero _] at he; have ht:=congr_arg (gravel a a q p) he; rw [rubDam,root_color a a q p x h hd,root_color a a p q x h hd] at ht
     apply KeysP.mix_blank; rw[truck, show wave (- (chargeMatrix*(M).transpose*chargeMatrix))= -wave (chargeMatrix*(M).transpose*chargeMatrix) from ?_]; rw[← wave_mul,←wave_mul,wave_tr]; exact ht.symm
     rw[wave, wave,← neg_one_smul ℂ (C*(M).transpose*C),Matrix.smul_kronecker,neg_one_smul]
include hw
variable (y:Label d)(z:ℂ)
local notation "m"=> marked s p*marked s q
lemma pinL(hY:Quiet y.val)(hp: pinAct w x.val=z • y.val) : z • silver a (hem s p) (hem s q) y.val= ((↑(m):ℂ)) • conjug w M:=by
    have he:= wending (0:Labels.Jet su) w s hw x h hd; rw [hp, map_smul,show StressFlux.shifted s (0:Labels.Jet su)=0 from funext fun i=> map_zero _] at he; have ht:=congr_arg (prism a a (hem s p) (hem s q)) he; rw[plumbs a a p q _ _ _ hw] at ht; have hx : z • (gravel a a (hem s p) (hem s q) (Ω y.val))= ((_ :ℂ)) • (wave w.matrix.val*gravel a a p q Xj*wave w.matrix⁻¹.val):= ht; -- placeholder
    apply KeysP.mix_blank; rw [Oriole.waveP,Oriole.waveP,conjug,←wave_mul,←wave_mul]; rw[root_color _ _ _ _ x h hd, root_color _ _ _ _ y hY hd] at hx; exact hx
end BendR
end YM.Massive.Tawny
#print axioms YM.Massive.Tawny.BendR.pinL
#print axioms YM.Massive.Tawny.BendR.chargeL
