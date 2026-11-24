import YM.Oriole.VaryL
import YM.Oriole.Bent
/-! Δ.Tapping.Work Projection law bis. cost at root from charged support.S. Witness.W -/
set_option autoImplicit false
noncomputable section
namespace YM.Massive.Oriole
open QCD QCD.Lat QCD.Grass Lattice TensorProduct Function UV PCAC Filter MeasureTheory RG Wilson
open scoped BigOperators Topology Matrix Matrix.Norms.L2Operator ContDiff Classical TensorProduct
variable {d n:ℕ}(a b:Flavor 6){c:Side}
open Poised.Display Poised.Stative Module Finset Revolve SourceRead Patria TorusPCAC.Geometry Cylinder
open QCD.Entr.Goals
local notation "T" => Lat.Fiber
local notation "I"=> (0:Multi 8)
variable (X Y P: Density c 6) (r:ℝ) -- dummy
variable (H:TaperHol)(p q:Multi 8)(u:Label 8)(i j:T)(k:Axis)(x:Cover)
noncomputable def reed (a b:Flavor 6)(i j:T)(D:Site c → Site c → ℂ): Lat.Fields c 6 →ₗ[ℂ] ℂ:= {
     toFun:=fun X=>∑ k,∑ l,D k l*uncoat X ((k,i),a) ((l,j),b)
     map_add':=fun x y=> by rw[map_add]; simp only [Matrix.add_apply,mul_add,sum_add_distrib]
     map_smul':=fun p x=>by rw [map_smul]; simp_rw [Matrix.smul_apply, Finset.smul_sum]; refine sum_congr rfl fun _ _=>sum_congr rfl fun _ _=>?_ ; exact mul_smul_comm .. }
noncomputable def deltaU (j:Axis)(p q:Multi 8):ℝ:= if p=UV.first j∧q=0 ∨ p=0∧q=UV.first j then 1 else 0
noncomputable def deltaB (a b:Flavor 6)(i j:T)(T':Taper)(k:Axis)(p q:Multi 8) : Lat.Fields c 6→ₗ[ℂ] ℂ:= (1/(2:ℂ)) • (reed a b i j (Oriole.syrup T' p q (step k)) - reed a b i j (Oriole.syrup T' p q (-step k))) - ((deltaU k p q:ℝ):ℂ) • reed a b i j (TP T')
local notation "RD"=> reed a b i j
local notation "W" x:arg=> syrup H.T p q x
local notation "V" x:arg=> vintage H.T p q x
local notation "xS"=> Lattice.step (S:=ℤ)
local notation "ι"=> Oriole.prism a b p q
local notation "κ"=> Canvas.foil P X
lemma bearer (Y:Lat.Fields c 6) (he:x= step k∨ x=-step k)(hi:1≤r)(h:heart p q): ‖RD (W x) Y-RD (V x) Y‖ ≤ (32/(c.val:ℝ))*MassiveQCD.Plate.view 0 2 Y r :=by
      change ‖(∑ k:Site c,∑ j:Site c,_)-(∑ k:Site c,∑ j:Site c,_)‖≤_; rw[←sum_sub_distrib]; simp_rw [←sum_sub_distrib,←sub_mul]; apply le_trans (norm_sum_le ..); apply (sum_le_sum (fun i _ => norm_sum_le ..)).trans
      apply le_trans _ (mul_le_mul_of_nonneg_left (bud_sq a b Y r i j hi (by norm_num)) (show (0:ℝ) ≤32/(c.val:ℝ) from by positivity)); simp_rw[Finset.mul_sum]; refine sum_le_sum fun i0 _=>sum_le_sum fun j0 _=>?_ ; rw[norm_mul]; exact (mul_le_mul_of_nonneg_right (yield H.T i0 j0 x p q k h he) (norm_nonneg _)).trans_eq (mul_assoc ..)
local notation "e"=> Lattice.step (S:=ℤ) k
local notation "δ"=> deltaU k p q
local notation "B"=> H.T
lemma croft (u v:Site c)(h:heart p q): 1/(2:ℂ) * ((V (Lattice.step k)) u v - (V (-(Lattice.step k))) u v)=↑δ *TP H.T u v:=by
     unfold vintage chart; rcases twoL p q h with h|h|h
     · rcases h with ⟨rfl,rfl⟩; simp [profile_0,TP,deltaU,Ne.symm (highV k)]
     · rcases h with ⟨j,h,hg⟩; subst p q; rw[profile_0,profile_0,profile_1,profile_1]; by_cases h:j=k
       · subst j; simp [TP,deltaU]; ring -- parse
       simp [TP,deltaU,step_apply,h,highV, first_eq]; -- simp
     rcases h with ⟨j,h,hg⟩; subst p q; rw[profile_0,profile_0,profile_1,profile_1]; by_cases h:j=k
     · subst j; simp [TP,deltaU]; ring
     simp [TP,deltaU,step_apply,h, Ne.symm (highV k),first_eq]
lemma ℓfare(X:Lat.Fields c 6)(hi:1≤ r)(hp:heart p q) : ‖deltaB a b i j H.T k p q X‖≤ (32/(c.val:ℝ))*MassiveQCD.Plate.view 0 2 X r:=by
      -- i j notation RD refers prior undeclared! binder may shadow.B
      let L:=RD (V e) X-RD (V (-e)) X; let x':=RD (W e) X - RD (V e) X; let y':=RD (W (-e)) X - RD (V (-e)) X
      have h: 1/(2:ℂ)*L= (↑δ:ℂ)*RD (TP B) X:=by
           unfold L reed; simp_rw [LinearMap.coe_mk, AddHom.coe_mk, ← sum_sub_distrib, Finset.mul_sum]; refine sum_congr rfl fun i1 _=>sum_congr rfl fun j1 _=>?_ ; rw [← sub_mul, ←mul_assoc, croft H p q k _ _ hp,mul_assoc]
      have hz: deltaB a b i j H.T k p q X= 1/(2:ℂ)*(x'-y'):=by change 1/(2:ℂ)*(_-_) - (↑δ:ℂ)* RD (TP H.T) X= _; rw [← h]; unfold L x' y'; ring
      let Q:= (32/(c.val:ℝ))*MassiveQCD.Plate.view 0 2 X r; rw[hz,norm_mul]; exact ((mul_le_mul_of_nonneg_left ((norm_sub_le ..).trans (add_le_add (bearer a b r H p q i j k _ X (.inl rfl) hi hp) (bearer a b r H p q i j k _ X (.inr rfl) hi hp))) (norm_nonneg (1/(2:ℂ)))).trans_eq (by norm_num; ring))
-- pairing root shifts
private lemma prup(X Y Z P v:ℂ): (X*Y)*(Z*P*v)=Z*P*X*Y*v:=by ring
private lemma SBrew (S Tt:Site c→Site c→ℂ)(x:Cover)(hS:∀ i j:Site c,S (i + wrap c x) (j+wrap c x)=heat x i*heat x j*Tt i j):
        let f (u v:Site c):= Nw H.T p u * Nw H.T q v; (∑ i:Site c,∑ j:Site c,f i j*S i j)= ∑ i:Site c,∑ j:Site c,syrup H.T p q x i j*Tt i j:=by
     intro F; let s:Site c≃Site c:= Equiv.addRight (wrap c x); rw [← Equiv.sum_comp s]; apply sum_congr rfl; intro k _; rw [←Equiv.sum_comp s]; apply sum_congr rfl; intro l _; change _ * S (k+wrap c x) (l+wrap c x)= _; rw [hS]; unfold syrup; change Nw H.T p (k+wrap c x)*Nw H.T q (l+wrap c x)*(heat x k*heat x l*Tt k l)=_; exact prup _ _ _ _ _
lemma shifterB (y:Cover)(hz:∀ k l:Site c,QCD.Run.cell (piece a b (uncoat (Y 1))) (k+wrap c y) (l+wrap c y)= (heat y k*heat y l) • QCD.Run.cell (piece a b (uncoat (X 1))) k l):
       let T'(k l:Site c):=Nw H.T p k*Nw H.T q l; RD T' (Y 1)=RD (W y) (X 1):=by
      intro T'; let Z(x:Density c 6)(p q:Site c):=QCD.Run.cell (piece a b (uncoat (x 1))) p q; change ∀ k l:Site c,Z Y (k+wrap c y) (l+wrap c y) = (heat y k*heat y l) • Z X k l at hz
      let M(Z:Density c 6)(b0:Site c)(x:Site c):ℂ:=uncoat (Z 1) ((b0,i),a) ((x,j),b) -- b capture; rename
      exact SBrew H p q (M Y) (M X) y (fun x z=>congr_fun (congr_fun (hz x z) i) j) -- parameter order verify
lemma shifts (y:Cover)(hu:IsUnit (P 1))(he:Patria.march y P=P) :
          let Φ:= Canvas.foil P (Patria.march y X); let T'(k l:Site c):=Nw H.T p k *Nw H.T q l; RD T' (Φ 1)= RD (W y) (κ 1):=by
      intro Φ T'
      apply shifterB a b (κ) Φ H p q i j y 
      let Z(x:Density c 6)(p q:Site c):= QCD.Run.cell (piece a b (uncoat (x 1))) p q; intro k l; unfold Φ; rw[ambassador P X y hu he]; exact thug (a:=a) (b:=b) (Canvas.foil P X) k l y -- order hp
local notation "D" => ((1:ℂ)/2)
variable (M:Spike)
local notation "Tt"=>TP B
lemma radar (Yv:Label 6)(hy:Yv.val=bilinear a b M 0 0) (hT:Tally H 0 Yv P X) : RD (TP H.T) (κ 1)= wave M i j:=by
      let k0: Multi 6:=0; have h:= script H P X Yv hT ((k0,i),a) ((k0,j),b) (by change spinWeight (0:Multi 6)+spinWeight (0:Multi 6) ≤ _; rw [cost_root]); have hp(x:Site c): Nw H.T k0 x=Np H.T x:=by unfold Nw; rw[show SourceRead.profile k0 (Lattice.lift x) 1=1 from profile_0 _,mul_one]
      rw [hy,←j_stard,j_coat,fieldK] at h; simp only [hp] at h; exact h.symm.trans (if_pos (by simp [k0]))
-- coreD: hY finite condition. Floor.Arithmetic.D taper only. keep Jx unweighted.
lemma rays (Z:Label 6)(hz:Z.val= bilinear a b M 0 0)(hv:Tally H 0 Z P X) (h0:∀ x:Cover, Patria.march x P=P)(hQ:Tally H 0 u P Y)(he:Y=D • ((Patria.march e X)-(Patria.march (-e) X)))(hp:heart p q) : ι (juncoat u.val) i j- (↑δ:ℂ) *wave M i j= deltaB a b i j H.T k p q (κ 1):=by
     let T'(k l:Site c):=Nw H.T p k *Nw H.T q l; let f:=RD T'; have ht:ι (juncoat u.val) i j=f (Canvas.foil P Y 1):=script H P Y _ hQ _ _ hp; rw [ht]; have hB: Canvas.foil P Y 1=D • (Canvas.foil P (Patria.march e X) 1-Canvas.foil P (Patria.march (-e) X) 1):=by unfold Canvas.foil; rw[he,Pi.smul_apply,Pi.sub_apply,mul_smul_comm, mul_sub]
     rw[hB,map_smul,map_sub,show f (Canvas.foil P (Patria.march e X) 1)= RD (W e) (κ 1) from shifts a b X P H p q i j _ hv.unit.self_of_nhds (h0 _), show f (Canvas.foil P (Patria.march (-e) X) 1)= _ from shifts a b X P H p q i j _ hv.unit.self_of_nhds (h0 _), ← radar a b X P H i j M Z hz hv]; rfl
end YM.Massive.Oriole
#print axioms YM.Massive.Oriole.rays
#print axioms YM.Massive.Oriole.ℓfare
