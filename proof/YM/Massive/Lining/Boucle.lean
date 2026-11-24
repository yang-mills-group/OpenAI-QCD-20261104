import YM.Massive.Lining.Wrist
/-! # Winding phase sums for charge and anti-automorphism extended parity. -/
set_option autoImplicit false
noncomputable section
namespace YM.Massive.Lining.Temper
open QCD QCD.Lat Lattice Wilson Massive.Papyrus UV Filter Function Finset Matrix Grass
open scoped Topology Matrix.Norms.Frobenius ContDiff BigOperators NNReal Classical Kronecker TensorProduct
open Purl Scan Cylinder Paper TensorProduct Ferry
variable {H:Source.Hol su}{d h:ℕ} (F:Flag H d h)(U: Kedge H d h)(t:Finset Cover) (n:Side)(b: Cover)
local notation "Q" => SpinMode d
local notation "T" => Nearest t 6
local notation "Y" => Modes n 6
variable (V:Grid n)(s: Signed)
private lemma wind_basis (ht:Parade t)(X:Spike): flower U t n b V*Action.moved 1 X= spinTable X * flower U t n b V:=by
    have hh: EuPin.Lifts 1 1:=(map_one Signed.inclusionO).symm; have he:= flow_pin U t n b V 1 ht 1 hh X; rw [pull_id, Signed.act_one, ← under_spin] at he; exact he
private lemma wind_starb (ht: Parade t)(X:Spike): Mstar (flower U t n b V)*Action.moved 1 X= spinTable X * Mstar (flower U t n b V):=by
    have hh: EuPin.Lifts 1 1:=(map_one Signed.inclusionO).symm; have he:= flow_opp U t n b V 1 ht 1 hh X; rw [pull_id, Signed.act_one, ← under_spin] at he; exact he
lemma wind_mirror (a:Axis)(ht: Parade t)(X:Spike): flower U t n b (pull (Signed.mirror a) 0 V)*Action.moved (Signed.mirror a) X= flipTable a X * flower U t n ((Signed.mirror a).act b) V:=by obtain ⟨p,hp⟩:= EuPin.choice (Signed.mirror a); rw [flow_pin _ _ _ _ _ _ _ p hp, hem_turn a hp]; exact ht
lemma wind_mirrorO (a:Axis)(ht: Parade t)(X:Spike): Mstar (flower U t n b (pull (Signed.mirror a) 0 V))*Action.moved (Signed.mirror a) X= flipTable a X * Mstar (flower U t n ((Signed.mirror a).act b) V):=by obtain ⟨p,hp⟩:= EuPin.choice (Signed.mirror a); rw [flow_opp _ _ _ _ _ _ _ p hp, hem_turn a hp]; exact ht
lemma flow_night : flower U t n b (conjugate ∘ V)= Mstar (flower U t n b V):=by unfold flower; rw [show anchored n b (conjugate ∘ V)=night (anchored n b V) from rfl, charges, mstar_mul,belt_star]
lemma valley_night(x:GPol): valley F n b (conjugate ∘ V) x=valley F n b V (wore x):=by unfold valley; rw [show anchored n b (conjugate ∘ V)=night (anchored n b V) from rfl, wore,Labels.eval_changed]; unfold extraction; rw [F.shine,recol, ← sendJet]
def eveN : Lat.Fields n 6→ₐ[ℂ] Lat.Fields n 6:= changeVars (Matrix.fromBlocks 0 (Action.moved 1 chargeMatrix) (Action.moved 1 (-(chargeMatrix⁻¹).transpose)) 0)
lemma wind_Nspin (ht: Parade t)(y: SpinPol d): eveN n (dartSpin U t n b (conjugate ∘ V) y)= dartSpin U t n b V (changeVars (masq d) y):=by unfold eveN dartSpin adapter; rw [multipleChange,multipleChange]; rw [masq,fromBlocks_multiply,fromBlocks_multiply,flow_night,mstar_again,wind_basis _ _ _ _ _ ht,wind_starb _ _ _ _ _ ht]; simp
lemma wind_N (ht: Parade t)(x:Pol d): eveN n (dart F U t n b (conjugate ∘ V) x)= dart F U t n b V (chargeAct x):=by
    induction x using TensorProduct.induction_on with
    | zero=>simp
    | tmul x y=>rw [chargeAct,TensorProduct.map_tmul,dart_at,dart_at,map_smul, valley_night,wind_Nspin _ _ _ _ _ ht y]; rfl
    | add x y hx hy=>simp_rw [map_add,hx,hy]
variable (a:Axis)
private abbrev mir (a:Axis):=Signed.mirror a
lemma valley_eye (x:GPol) : star (valley F n b (pull (mir a) 0 V) x)=valley F n ((mir a).act b) V (Labels.rotated (Signed.reflect a) (conjGPol x)):=by
    unfold Signed.reflect; rw [← show _=_ from (valley_pin F n b V (mir a) (conjGPol x))]; exact (Labels.conj_value ..).symm
abbrev crook : Lat.Fields n 6→ₛₗ[starRingEnd ℂ] Lat.Fields n 6:= ((changeVars (Matrix.fromBlocks 0 (Action.moved (Signed.mirror a) (-(gamma a).transpose)) (Action.moved (Signed.mirror a) (-gamma a)) 0)).toLinearMap.comp Grass.dagger)
private lemma wind_eyeSpin (ht: Parade t)(y:SpinPol d): crook n a (dartSpin U t n b (pull (mir a) 0 V) y) = dartSpin U t n ((mir a).act b) V (UV.aSpin d a y):=by
    unfold crook dartSpin adapter UV.aSpin; simp only [LinearMap.comp_apply, AlgHom.toLinearMap_apply]; rw [dagger_change,multipleChange,multipleChange]; unfold mir; rw [eyeW, mstar_diag, mstar_again, fromBlocks_multiply,fromBlocks_multiply,wind_mirror _ _ _ _ _ a ht,wind_mirrorO _ _ _ _ _ a ht]; simp
lemma wind_eye (ht: Parade t)(x:Pol d): crook n a (dart F U t n b (pull (Signed.mirror a) 0 V) x) = dart F U t n ((Signed.mirror a).act b) V (UV.adj a x):=by
    induction x using TensorProduct.induction_on with
    | zero=>simp
    | tmul x y=>rw [UV.adj,TensorProduct.map_tmul,dart_at,dart_at,map_smulₛₗ]; change star _ • crook _ _ (dartSpin _ _ _ _ (pull (mir a) 0 V) _) = _; rw [valley_eye,wind_eyeSpin _ _ _ _ _ a ht]; rfl -- inference
    | add x y hx hy=>simp_rw [map_add,hx,hy]
section Flavor
variable (p: FlavorTorus)
abbrev phaseD (n:Side) (p:FlavorTorus): Matrix (Modes n 6) (Modes n 6) ℂ:= byFlavor p Prod.snd
private abbrev phaseQ (d:ℕ) (p:FlavorTorus) : Matrix (SpinMode d) (SpinMode d) ℂ:= byFlavor p (fun i:SpinMode d=> i.2)
lemma wind_phases : flower U t n b V*phaseD n p=phaseQ d p*flower U t n b V:=by unfold flower start phaseQ phaseD; rw [table,spar,nacre_mul]; exact (nacre_flavor _ p).symm -- projection prod implicit instance abbrev
lemma wind_phasesO : Mstar (flower U t n b V)*phaseD n p⁻¹= phaseQ d p⁻¹*Mstar (flower U t n b V):=by rw [← flow_night]; exact wind_phases ..
def stroll : Lat.Fields n 6→ₐ[ℂ]Lat.Fields n 6:= adapter (phaseD n p) (phaseD n p⁻¹)
lemma strolling (x:Pol d): stroll n p (dart F U t n b V x)=dart F U t n b V (UV.flavorAct p x):=by
    induction x using TensorProduct.induction_on with
    | zero=>simp
    | tmul x y=> rw [flavorAct,TensorProduct.map_tmul,dart_at,dart_at,map_smul]; unfold stroll dartSpin; rw [adapt_together]; simp only [AlgHom.toLinearMap_apply,LinearMap.id_apply]; rw [adapt_together,wind_phases,wind_phasesO]
    | add x y hx hy=> simp_rw [map_add,hx,hy]
lemma foldG (x:Pol d): grade (dart F U t n b V x)=dart F U t n b V (parityAct x):=by
    induction x using TensorProduct.induction_on with
    | zero=>simp
    | tmul x y=> rw [parityAct,TensorProduct.map_tmul,dart_at,dart_at,map_smul]; exact congr_arg (fun y=> valley F n b V x • y) (exterior_parity (substitution _) y)
    | add x y hx hy=>simp_rw [map_add,hx,hy]
end Flavor
end YM.Massive.Lining.Temper
#print axioms YM.Massive.Lining.Temper.foldG
#print axioms YM.Massive.Lining.Temper.wind_eye
