import YM.Oriole.Grin
/-! DA stencil. root exact flavor and pair.S omega Small. -/
set_option autoImplicit false
noncomputable section
namespace YM.Massive.Oriole
open Function Lattice RG Wilson Filter Finset
open scoped BigOperators ContDiff Topology Matrix Matrix.Norms.L2Operator Classical
variable {c:Side}{n k:ℕ}
open UV PCAC QCD QCD.Lat QCD.Grass SourceRead Patria Patria.Depth Patria.Rolls Cylinder Massive.Poised
local notation "L" a:arg=> Lattice.step (S:=ℤ) a
local notation "O"=>MassFields.isotropic
local notation "W" i:arg=> MassFields.atVector i
variable {S:Scheme} {R:Side}
local notation "C"=> S.side R 0
local notation "K"=> S.side R n
variable (B:Bore 6)(T:PatchMix 6)(J: RawSym)(F: FlavorTorus)
variable (A:Run S n R 6) (p q:Flavor 6) (G:TaperHol)
variable (H:OrderMix A G J B (i:=0) T)(h: Rubric J B)(hp: A.Actual) (X:Label 6) (i:Axis)
local notation "e" => step (S:=ℤ) i
local notation "Z" x:arg=> B K x (T (W i) X)
local notation "Zp"=> fun x:Cover=> Z x
local notation "Sn" => Depth.trolley A Zp (W i)
local notation "Mark" => Rolls.nick (S.spacing n)⁻¹ i Zp
local notation "Kp"=> Depth.trolley A (Mark) O
local notation "Pn"=> A.density 0
variable (U: UV.Label 8)(B':Bore 8)(hq:Rubric J B') (w:Market S R 8)(hW: Wager A G B' w 0)(M:Spike)(hM:X.val=UV.bilinear p q M 0 0)(hK:Tally G 0 U (A.density 0) (Depth.trolley A (Rolls.nick (S.spacing n)⁻¹ i (fun x=>B (S.side R n) x (T (MassFields.atVector i) X))) MassFields.isotropic 0 0))
include hW H h hp hM hK hq
lemma tintedG : CharmC p q U.val:=by
      intro f; let v:= paidM p q f; let R':=S.side R n; let Fh:Cover→Insertion R' 6:= Zp; let V:= Kp; have hX: J.flavor _ f X=v • X:=by apply Subtype.ext; rw [J.flavorActs]; change _=v • X.val; rw [hM]; exact charm p q _ _ M f
      have hu : J.flavor _ f (T (W i) X)=v • T (W i) X:=by rw [H.flavorO (W i) X f,hX,map_smul]
      have he(b:Cover): Action.flavor f (Fh b)= v • ⇑(Fh b):=by unfold Fh; rw [h.flavor,hu,map_smul]; rfl
      let Q:=Mark; have hv(b:Cover): Action.flavor f (Q b)= ⇑(v • Q b):=by
           let X':=(S.spacing n)⁻¹/2; funext Y; let p:=Lining.Temper.stroll R' f; have ht(x:Cover):p (Fh x Y)=v • (Fh x Y):= congr_fun (he x) Y; change p ((X':ℂ) • (Fh (b+e) Y-Fh (b-e) Y))=v • ((X':ℂ) • (Fh (b+e) Y-Fh (b-e) Y)); rw [map_smul,map_sub,ht,ht,← smul_sub,smul_comm]
      have hδ:Action.flavor f (Kp 0 0)= v • ⇑(Kp 0 0):=by
           let Z':= visitor S n 0 O 0 Q; have hP: Action.flavor f Z'=⇑(v • Z'):=by
                funext X; unfold Z' visitor; rw [smul_zero]; let A':Insertion R' 6→ₗ[ℝ]Lat.Fields R' 6:= (((Lining.Temper.stroll R' f).toLinearMap).comp (ContinuousMap.evalCLM ℂ X).toLinearMap).restrictScalars ℝ; have he:= permeate O 1 A' Q (v • Q) X (fun i'=>by rw[Signed.act_one]; exact congr_fun (hv i') X) (odd_to (S:=S) (Nat.zero_le n)); rw [permit_one] at he; rw[show (Averaging.filter O (ratioTo S n 0) (v • Q) 0)=v • Averaging.filter O (ratioTo S n 0) Q 0 from ?_] at he; exact he
                rw [roles,roles]; exact (rollLinear (v:=Q) (l:=menu O) (M:=ratioTo S n 0) (k:=1) 0 ((v • (LinearMap.id (R:=ℂ) (M:=Insertion R' 6))).restrictScalars ℝ)).symm
           let F' := A.regulator.density; let u':= F'*Z'; have ht: Action.flavor f F'=⇑F':= Exposure.flavor_pivot _ _; have hU: Action.flavor f u'=⇑(v • u'):=by
                funext X; let F₁:= Lining.Temper.stroll R' f; change F₁ ((F' X)*(Z' X))= v • (F' X*Z' X); rw[map_mul,show F₁ _=_ from congr_fun ht X,show F₁ (Z' X)=_ from congr_fun hP X]; exact mul_smul_comm v (F' X) (Z' X)
           have he := strokeP A f u' _ hU (Nat.zero_le n); rw[map_smul] at he; exact he
      rw [← J.flavorActs]; have hz:=Canvas.arrows G f _ (J.flavor 8 f U) (fun x:Label 8=>⇑(B' C 0 x)) hK hW.reading (by rw[pier A hp hW.siteM]; exact (Depth.arrives A 0 hW.siteM).2.2.1 f) (hq.flavor C U 0 f); rw [hδ] at hz; have hT:= QCD.Acre.Stratum.MarchQ.Suburb.Melt.Lobby.Talent.shines G 8 0 U v _ _ hK; exact congr_arg Subtype.val (Canvas.consensus _ _ _ hz _ hT)
omit hW hq
noncomputable def stereo (p q:Flavor 6)(i:Axis)(M:Spike) : Label 8:=satin p q (UV.first i) 0 M (by rw[juicy,cost_root])+ satin p q 0 (UV.first i) M (by rw [cost_root,juicy]) -- no includes
include hq -- not needed
omit hq
set_option maxHeartbeats 460000 in
lemma DA_val (X' Y':Multi 8)(ht: Oriole.heart X' Y')(i1 i2:Lat.Fiber): let V:=stereo p q i M; Oriole.prism p q X' Y' (juncoat (U-V).val) i1 i2= deltaB p q i1 i2 G.T i X' Y' (Canvas.foil (A.density 0) (Sn 0 0) 1):=by
    intro V; have hS(b:Cover):Patria.march b (Pn)=Pn:=by rw[pier A hp (Nat.zero_le n)]; exact Depth.first A 0 (Nat.zero_le _) b
    have he:⇑(Kp 0 0) = ((1:ℂ)/2) • (march e (Sn 0 0)-march (-e) (Sn 0 0)) :=by
          have hh(x y:Cover): march y (Sn 0 x)=⇑(Sn 0 (x+y)):=Depth.axial A hp Zp _ (fun _ _=> h.advances ..) y x (Nat.zero_le n) -- order inspect
          rw [hh,hh,Rolls.honest]; rw [Scheme.spacing_zero, inv_one]; rw [zero_add,zero_sub,zero_add]; push_cast; rw [show ((1:ℂ)/2)=(((↑((1:ℝ)/2)):ℂ)) from by push_cast;rfl]; rfl
          exact Nat.zero_le _
    have hw:= rays p q (Sn 0 0) (Kp 0 0) _ G _ _ U i1 i2 i M X hM (H.smoke X (W i)) hS hK he ht; let f:= qp p q X' Y'; change f (juncoat (U.val - V.val)) i1 i2= _; rw [map_sub,map_sub,Matrix.sub_apply, ← hw]; change f (juncoat U.val) i1 i2-f (juncoat (bilinear p q M (UV.first i) 0+bilinear p q M 0 (UV.first i))) _ _= _; apply congr_arg; simp_rw [←j_stard,map_add,j_coat]; rw [Matrix.add_apply]; change Oriole.prism _ _ _ _ _ i1 i2+ Oriole.prism _ _ _ _ _ i1 i2 = _; unfold Oriole.prism; rw [Matrix.of_apply,Matrix.of_apply,fieldK,fieldK]; change (if X'=UV.first i ∧ _ then _ else _) + _= _; unfold deltaU; split_ifs <;> simp_all [highV,Ne.symm] <;> tauto
end YM.Massive.Oriole
#print axioms YM.Massive.Oriole.DA_val
#print axioms YM.Massive.Oriole.tintedG
