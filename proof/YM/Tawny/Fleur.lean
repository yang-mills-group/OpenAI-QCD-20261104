import YM.Tawny.Bend
import YM.Plateau.Crake
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
open Pane TensorProduct Revolve UV.Free KeysP
namespace BendR
variable (D:Pol d)(X:CensusA d)(J:Labels.Jet su)(w:EuPin)(s:Signed)(hw:w.Lifts s)
local notation "Y" => ready d J
local notation "Y0"=> ready d (0:Labels.Jet su)
local notation "Δ"=> skin (d:=d) J
local notation "Ω"=> skin (d:=d) (0:Labels.Jet su)
local notation "Φ"=> invertW d w
local notation "J★"=> Labels.changedJet (fun _=>UV.recolor) J
variable (x:Label d)(h:Quiet x.val)(hd:d≤10)
local notation "Ff"=> fog x.val
local notation "Ψ"=> glow x h hd
local notation "Xj"=> Ω x.val
local notation "C"=> chargeMatrix
variable (p q:Multi d)
local notation "μ"=> gravel a a p q
local notation "ν"=> gravel a a q p
local notation "μs"=> gravel a a (hem s p) (hem s q)
local notation "M"=>silver a p q x.val
variable (u v:Axis)
local notation "hL"=> StressFlux.leg0 (G:=su) u v
local notation "hK"=> StressFlux.leg0 (G:=su) (s.perm u) (s.perm v)
local notation "A0"=>Labels.Taylor su 0
local notation "g"=>su.colorMat
local notation "R"=>twin a a x h hd p q u v
local notation "S"=>twin a a x h hd q p u v
open scoped Kronecker InnerProductSpace
lemma wave_Z (e:su.Color): star (su.colorMat (reflectColor e))=-(su.colorMat (reflectColor e)):=su.colorMat_skew _
lemma tilt_h (e:su.Color): Matrix.transpose (su.colorMat (reflectColor e))= - g e:= by calc
       _= star (g e):=by rw [reflMat]; rfl
       _= _:=su.colorMat_skew _
lemma tilt_leg (e:su.Color): UV.recolor (hL e)= hL (reflectColor e):=by
    apply Labels.Taylor.value_ext; funext i z; change reflectColor (Labels.Taylor.value _ i z)=_; rw[StressFlux.leg0_value,StressFlux.leg0_value]; split_ifs <;> simp
noncomputable def ore (e:su.Color):Mat:=su.colorMat e
lemma arch (e:su.Color)(P:Spike): wave C * Matrix.transpose (P ⊗ₖ ore (reflectColor e)) * wave C=truck P ⊗ₖ ore e:=by
    rw [show Matrix.transpose (P ⊗ₖ ore (reflectColor e))= P.transpose ⊗ₖ ((ore (reflectColor e)).transpose) from rfl, show (ore (reflectColor e)).transpose= - ore e from tilt_h e]; unfold wave; rw [← Matrix.mul_kronecker_mul, ← Matrix.mul_kronecker_mul,one_mul,mul_one]; unfold truck; simp only [← neg_one_smul ℂ (ore e),Matrix.kronecker_smul]; rw [← neg_one_smul ℂ (C*P.transpose*C),Matrix.smul_kronecker] -- careful.
include h hd
lemma chargeR(hc:chargeAct x.val=x.val) : S = - truck (R):=by
     let e:= ruby_pick.choose; let L:= hL e; let K:Labels.Jet su:=Pi.single 0 L; have hu:K 0=hL e:=Pi.single_eq_same ..
     have he:= crest K x h hd; rw [hc] at he; have ht:=congr_arg ν he; unfold dam at he -- not needed
     have ht0:=congr_arg ν (crest (0:Labels.Jet su) x h hd); rw [hc, show Labels.changedJet (fun _=>UV.recolor) (0:Labels.Jet su)=0 from funext fun i=> map_zero _] at ht0
     rw[rubDam] at ht0 ht
     rw [shiny K x h hd,shiny (Labels.changedJet _ K) x h hd,show Labels.changedJet _ K 0=UV.recolor (hL e) from congr_arg UV.recolor hu,hu,map_add,map_add, Matrix.transpose_add,Matrix.mul_add, Matrix.add_mul,neg_add,ht0] at ht
     have hx:= add_left_cancel ht; rw [tilt_leg,← glean x h hd,← glean x h hd, pare a a x h hd q p,pare a a x h hd p q] at hx -- args inspect
     change S ⊗ₖ ore e = -(wave C*(R ⊗ₖ ore (reflectColor e)).transpose*wave C) at hx; rw[arch] at hx
     apply braidR _ _ (ore e) (gem e ruby_pick.choose_spec); rw [hx,← neg_one_smul ℂ (truck R),Matrix.smul_kronecker,neg_one_smul]
omit h hd
lemma tilt_turn (e:su.Color): Labels.Taylor.turn s.ortho⁻¹ (hK e)=(signT s u*signT s v) • hL e:=by -- existing turn_leg0
    have he:= StressFlux.turn_leg0 s⁻¹ (s.perm u) (s.perm v) e
    have hQ(a:Axis):StressFlux.sign s⁻¹ (s.perm a)= signT s a:=by change signT s⁻¹ _=_; rw[inv_sign,Equiv.symm_apply_apply];
    rw [show Signed.ortho (s⁻¹)=s.ortho⁻¹ from map_inv Signed.inclusionO s,hQ,hQ,Signed.inv_perm, Equiv.symm_apply_apply,Equiv.symm_apply_apply] at he; exact he
lemma poker(z:ℂ)(e:su.Color)(P:Spike): (wave w.matrix.val*(z • (P ⊗ₖ ore e))*wave w.matrix⁻¹.val)=z • ((conjug w P) ⊗ₖ ore e):=by
    rw [Matrix.mul_smul, Matrix.smul_mul]; unfold wave; rw [← Matrix.mul_kronecker_mul, ← Matrix.mul_kronecker_mul,one_mul,mul_one]; rfl
include h hd hw
variable (y:Label d)(hY:Quiet y.val)(z:ℂ)
local notation "σ"=> twin a a y hY hd (hem s p) (hem s q) (s.perm u) (s.perm v)
lemma pinR(hp:pinAct w x.val=z • y.val) : z • σ= ((↑((marked s p*marked s q)*(signT s u*signT s v)):ℂ)) • conjug w R:=by
     let e:= ruby_pick.choose; let L:= hK e; let K:Labels.Jet su:=Pi.single 0 L; have hu:K 0=hK e:=Pi.single_eq_same ..
     let J':=StressFlux.shifted s K
     have he(S':Labels.Jet su): z • μs (skin S' y.val)=((↑(marked s p*marked s q):ℂ)) • (wave w.matrix.val * μ (skin (StressFlux.shifted s S') x.val)*wave w.matrix⁻¹.val):=by
          have ht:= wending S' w s hw x h hd; rw[hp,map_smul] at ht; rw [← map_smul,ht]; exact plumbs a a p q _ s w hw
     have hk:= he (0:Labels.Jet su); have h1:=he K; rw[show StressFlux.shifted s (0:Labels.Jet su)=0 from funext fun i=> map_zero _] at hk
     rw [shiny K y hY hd,shiny (StressFlux.shifted s K) x h hd,map_add,map_add,Matrix.mul_add,Matrix.add_mul,smul_add,smul_add,hk] at h1
     have h2:=add_left_cancel h1
     have ht: (StressFlux.shifted s K) 0=(signT s u* signT s v) • hL e:=(congr_arg (Labels.Taylor.turn (j:=0) s.ortho⁻¹) hu).trans (tilt_turn s u v e)
     rw [ht,hu,map_smul,←Complex.coe_smul (signT s u *signT s v),map_smul,← glean x h hd,← glean y hY hd,pare a a y hY hd,pare a a x h hd] at h2
     change z • (σ ⊗ₖ ore e)= ((↑(marked s p*marked s q):ℂ)) • (wave w.matrix.val * ((↑(signT s u*signT s v):ℂ) • (R ⊗ₖ ore e)) * wave w.matrix⁻¹.val) at h2; rw[poker] at h2
     apply braidR _ _ (ore e) (gem e ruby_pick.choose_spec); rw [Matrix.smul_kronecker,Matrix.smul_kronecker, h2, smul_smul,Complex.ofReal_mul (marked s p*marked s q)]
end BendR
end YM.Massive.Tawny
#print axioms YM.Massive.Tawny.BendR.pinR
#print axioms YM.Massive.Tawny.BendR.chargeR
