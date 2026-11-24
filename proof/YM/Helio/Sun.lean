import YM.QCD.Entr.Wood
import YM.QCD.Spice.Cotton
import YM.Helio.Ram
set_option autoImplicit false
noncomputable section
namespace YM.QCD.Entr
open Function Lattice Wilson Creek Grass Ledge Lat Kit Finset NormedSpace RG Cove Cove.Send Filter Run
open Sway OrbitG Loom Fleet Bay Strut MeasureTheory Push.Local Push.AbsoluteSums Ursell Gas Graph GasP PhysicalNext.Repeat.Turn Patron Stew Reggae Jets Sun
open scoped BigOperators Topology ContDiff Classical Matrix Matrix.Norms.L2Operator
variable {c:Side}{N k B n b j:ℕ}{p:BudgetPoint}{η u a r t w P q J δ z z' θ σ:ℝ}{i o:Site c}
open Revolve Villa Port Footprint AnalyticBridge.VerifiedReset Flume Pine YM.Next.Free Leaf LeafM Tee Garden
variable {Γ:Silo c}{A: BankP c}{U:St c}
namespace Meridian
noncomputable def rplus (c: Side)(a:Axis):Strut c:=(1,step a)
variable (V:Grid c)(α β:Axis)(x:Site c)
lemma riseA (x:Site c): act (rplus c α) x=x+step α:=by change affine 1 _ x=_; simp [affine,rplus]
lemma pullR (x:Site c) : sky (rplus c α) V (x,β)=V (x+step α,β):=by change pull _ _ _ _=_; simp [rplus,pull,Step.rotate, Step.read,affine, posDir,Step.used]
lemma warrantL (c:Side): Warrant (rplus c α) (fun x:Site c=> Lat.seam 0 x α) 1:=by
   refine ⟨⟨fun i=> seam_cases ..,fun i x=>?_⟩,Swing.none⟩; change Lat.seam _ _ _*_=_ *glint _ (affine 1 _ _) _
   rw [show affine _ _ _ = x+step α from riseA ..,show (posDir i).rotate (rplus c α).1=posDir i from ?_]; swap
   · simp [rplus, Step.rotate,posDir]
   change _=Lat.seam 0 x α*Lat.seam 0 (x+step α) i; by_cases h:i=α
   · subst α; rfl
   rw [seam_across _ _ (Ne.symm h),seam_across _ _ h,mul_comm]
def frameP (x:Axis)(V:Grid c) : Frame c:=fun i=> V (i,x)
noncomputable def overlayP (α: Axis)(V:Grid c):Grid c:=Lattice.gauge (frameP α V) (sky (rplus c α) V)
lemma setR : overlayP α V (x,β)*(V (x,β))⁻¹= travel V x (square α β):=by
    change V (x,α)* sky (rplus c α) V (x,β)*(V (x+step β,α))⁻¹ * _=_; rw [pullR]; simp [square,travel,Step.read,Step.vec,posDir,negDir,Step.used]; group
lemma depth (Y:Support c) (U:Grid c)(ht:Healthy t Y U)(hx:x∈ Y)(hp:0<t) : su.chord (travel U x (square α β)) ≤t:=by
   have he(i:Face (Per c))(hv:x∈ touched i): su.chord (faceValue U i)≤t:=by
       by_contra h; exact Finset.disjoint_left.mp ht hx ((flags_spec _ _ _).mpr ⟨i,hv,lt_of_not_ge h⟩)
   rcases lt_trichotomy α β with ha|ha|ha
   · let p : Face (Per c):=(x, ⟨(α,β),ha⟩); apply he p; unfold touched; change x∈(visits x (square α β)).toFinset; simp [Lattice.visits,square]
   · subst α; rw [show travel U x (square β β)=1 from ?_,Gauge.chord_one]; exact hp.le
     simp [square,travel,Step.read,Step.vec,posDir,negDir, Step.used] <;> group
   let q: Face (Per c):=(x,⟨(β,α),ha⟩); rw [show square α β=Lattice.reverse (square β α) from rfl]; rw [show travel U x (Lattice.reverse (square β α))= (travel U x (square β α))⁻¹ from (by simpa using travel_reverse (square β α) U x)] -- check sig
   rw [Gauge.chord_inv]
   apply he q; unfold touched; change x∈(visits x (square β α)).toFinset; simp [Lattice.visits,square]
lemma overlayCost : ∃ Z:ℝ,0<Z∧∀(c:Side)(U:Grid c)(Y:Support c)(α:Axis)(t:ℝ),Healthy t Y U→0<t→ Spice.beamAt Y (overlayP α U) U (Z*t):=by
    obtain ⟨Z,hZ,h⟩:=Spice.boughtX; refine ⟨Z,hZ,fun c U Y α t hV he=> h c (overlayP α U) U Y t (fun i hi _=>?_)⟩; rw [show overlayP α U i*(U i)⁻¹ = _ from setR U α i.2 i.1]; exact depth α i.2 i.1 Y U hV hi he
end Meridian
end YM.QCD.Entr
#print axioms YM.QCD.Entr.Meridian.overlayCost
