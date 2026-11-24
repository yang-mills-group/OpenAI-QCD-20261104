import YM.Hypnos.Comet
import YM.QCD.Jets.Pie
import YM.Hypnos.Cirque
import YM.QCD.Spice.Cotton
set_option linter.unusedSectionVars false
set_option autoImplicit false
noncomputable section
namespace YM.QCD.Leaf.Tee
open Function Lattice Wilson Creek Grass Ledge Lat Kit Finset NormedSpace RG Cove Cove.Send Filter Run
open Leaf Tee Flume Orbit Quarry Stationary Fork Pine YM.Next.Free Push.AbsoluteSums Footprint Trees Pressure
open Garden Spice Jets Sun LeafM
open scoped BigOperators Topology ContDiff Classical Matrix Matrix.Norms.L2Operator
variable {F k j:ℕ}{c f: Side} {δ q κ a u v η ξ x y w p ε α β t:ℝ}{l b r:ℕ}{G:Flight j k}{h:f.val=c.val*G.L.val}
namespace Rot
open Eyrie Revolve Rudder Cost
open Jets.Touch ConnectedActivityE6
lemma pureS (P:Plan j)(k:ℕ)(L:Side) : ∃ δ v q a : ℝ, ∃ B:ℕ,∀ (c f:Side)(F:Flight j k)(h:f.val=c.val*F.L.val),F.L=L→Nonempty (Sun F c f h δ v q 1 a B (vaultF P F h 0)):=by
   obtain ⟨M,c,v,R,a,hM,hc,N,hN⟩:= planted P zero_le_one k L
   refine ⟨c,v,R,a,N,fun c' f F h hp=>?_⟩; apply Jets.sun_nonempty _ hc; have he:= hN _ le_rfl F hp c' f h (0 : St f) c hc le_rfl (Run.Heritage.vacant.mono hM.le) (fun U=> by change star (0:Sheet f)=_ *0*_; simp); unfold pesto at he; rwa [add_zero] at he

lemma pretzel (P:Plan j)(k:ℕ)(L:Side)(N:ℕ) : ∃ C:ℝ,∀ (ε:ℝ), ∃ R :ℝ→ℝ, Rate su L ε R ∧ ∀ᶠ x in atTop,∀ (c f:Side)(F: Flight j k)(h:f.val=c.val*F.L.val), F.L=L→
     let b:=radiusB x; (∀ i j:Modes f N, ‖spider N F h i j - shore F h N b i j‖ ≤R x ∧ ‖spider N F h i j‖≤ C)∧(∀ i:Keys f N, (∑ j:Keys c N, ‖wheelsF N F h i j-shear F h N b i j‖) ≤ R x ∧ (∑ j:Keys c N,‖wheelsF N F h i j‖)≤C):=by
    obtain ⟨δ,v,q,a,B,H⟩:= pureS P k L
    have hf :0≤ fingers N:=by unfold fingers; positivity
    refine ⟨max (stamp P L) (fingers N*q),fun ε=>?_⟩
    let A x:=Real.exp (-(1:ℝ)*fossil (radiusB x) B); have ha:Rate su L ε A:=by unfold A; simpa only [sub_zero] using Touch.pale 1 0 zero_lt_one B
    refine ⟨_, (ha.mul_right q).mul_left (1+fingers N),Eventually.of_forall fun x c f F h he=> ?_⟩
    obtain ⟨u⟩:= H c f F h he; intro b
    let W:= A x*q
    have hw:0≤ W:=mul_nonneg (Real.exp_pos _).le u.stable.forest.le
    exact ⟨fun i j=> ⟨(fans P u zero_le_one b i j).trans (le_mul_of_one_le_left hw (le_add_of_nonneg_right hf)), (finance P i j).trans (he.symm ▸ le_max_left ..)⟩,fun i=> ⟨(strobes P u zero_le_one b i).trans (mul_le_mul_of_nonneg_right (le_add_of_nonneg_left zero_le_one) hw), (fungi P u zero_le_one _).trans (le_max_right ..)⟩ ⟩

-- allow R includes charge knot c θ etc.POST.
lemma aurora (P:Plan j)(k:ℕ)(L:Side)(q u v a η:ℝ)(l:ℕ)(hη:0<η)(hu:0<u)(W:ℝ→ℝ)(hW:Rate su L (-(1/2)) W): ∃ (U V:ℝ→ℝ), Rate su L (-(1/32)) U ∧ Rate su L (-(1/32)) V ∧∀ᶠ x in atTop,
    ∀ (N:ℕ)(c f:Side)(F:Flight j k)(h:f.val=c.val*F.L.val), F.L=L→∀ (r r' s s' m t':ℝ)(X:Offer 1 r s)(Y:Offer 2 r' s') (Z:Sun F c f h (coneK L η x) v q u a l (pesto P F h (trunkM X Y t' m f))), |m| ≤ haloK L x→ ∀ R:Grid f,0≤W x→
    let b:=radiusB x; (∀ (i j:Modes f N), beamAt (trunkFt i.1.1 b) R 1 (W x) → ‖spore Z b R i j-shore F h N b i j‖ ≤ U x)∧ (∀ (i:Keys f N)(j:Keys c N),beamAt (trunkFt (locationP i) b) R 1 (W x) → ‖(Z.equip N b).shortP R i j-shear F h N b i j‖≤ V x):=by
    let E x:=Real.exp (-u*fossil (radiusB x) l); let G x:= W x/(coneK L η x/2); let V x:=stamp P L*haloK L x*a⁻¹; have hv: Rate su L (-(1/32)) V:= (Rate.mul_left Rate.power _).mul_right _
    have hA: Rate su L (-(1/32)) E:= by unfold E; simpa only [sub_zero] using Touch.pale u 0 hu l
    have hg:Rate su L (-(1/32)) G:=by unfold G; simp_rw [div_eq_mul_inv (W _)]; exact (hW.mul (shade_e L hη.ne')).weaken (by norm_num)
    refine ⟨fun x=> q*G x+(E x*q+V x),fun x=> V x*massL L+(E x+G x)*q,(hg.mul_left _).add ((hA.mul_right q).add hv),(hv.mul_right _).add ((hA.add hg).mul_right _),?_⟩
    filter_upwards [hg.below (by norm_num) (1/2) (by norm_num)] with x hx n c f F h he r r' s s' m t' X Y Z hM R hR b; have hd:W x<coneK L η x/2:= (div_lt_one (half_pos Z.positive)).mp (((le_abs_self _).trans hx).trans_lt (by norm_num)); have hf:=Z.stable.calf
    have hh: stamp P F.L*|m| *a⁻¹ ≤ V x:=by
       unfold V; rw [he]; exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hM (Pine.healthy ..).le) (inv_nonneg.mpr hf.le)
    refine ⟨fun i j hi=> (spliceS P Z hu.le R i j hi hR hd).trans (add_le_add_right (add_le_add_right hh _) _), fun i j hi=> (spliceW P Z hu.le R i j hi hR hd).trans (by
        change _ ≤ V x*massL L+(E x+G x)*q
        rw [← he]; refine add_le_add (mul_le_mul_of_nonneg_right hh (mass_pos _).le) ?_; rw [he]) ⟩
end Rot
end YM.QCD.Leaf.Tee
#print axioms YM.QCD.Leaf.Tee.Rot.pretzel
#print axioms YM.QCD.Leaf.Tee.Rot.aurora
