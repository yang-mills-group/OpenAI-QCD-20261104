import YM.QCD.Beam.Writer
import YM.QCD.Disc.Sound
import YM.QCD.Calm.Dyn
/-! # preratio gauges across various pulse meshes. -/
set_option autoImplicit false
noncomputable section
namespace YM.QCD.Acre
open Function Lattice RG Laurent Bloch Matrix Metric Precision Wilson Bid Craft Exterior Filter
open YM.Next.Free YM.Work YM.Further.PhysicalPeriodLimitF933
open WilsonStartup Design Change Extra.Iteration Stationary Tree Raft Garden Transfer Orbit Sparks Fog Birth Raft.ParcelR
open ConnectedActivityE6 Pressure Pressure.Stores
open Push Push.AbsoluteSums Exterior Shell Stationary Next.Fluctuations SectorMeasure Oriented Work.E03
open Bloch Laurent Work.F03 Progress.StationaryScenes Bid SliceRows Mask Coat
open Census Green Mask Pulse Itinerary Presented LabelSum Matter Poll Pond Packets
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical
variable {G : Gauge}{j t k i l n N: ℕ}{K:KernelChoices}{q: Clip}{E:Patch}{σ η Ω A γ β b C D u v x y W:ℝ}{p:ChartRatio su}{M:ℕ→ Bed}{T:ℕ→Towers E.L}


variable {S:ℕ→SparkMesh}
lemma broadcastP {B:Teller su} (X:Soil K q E σ η Ω M T)(R:PulseRide K q E u v S N)(h:Invoice R p M T x y γ D W)
 (hz:E.Branches K su) (hj:B.bind=K)(hk:B.top.width=u)(ho:B.below=B.top)(hc:B.top.clip=q)(hX:B.C=Ω)(hs:B.η=σ)(hu:v ≤ B.top.paths)(hn:B.j=E.J)(i j)(ht:i<N)(t:ℝ)
 (he : 100*(1+radiusB t)≤ ((S i).n j).val) :
    let g:=act (Pike E i) K (S i) j
    let ZB:Tube su g:=⟨T i,R.path i,q,R.path (i+1),q⟩
    Works B E.L t g ZB∧SliceRows.Stamp ZB ∧ YM.AnalyticBridge.LocalGaussianLaws.Lift.Booth B g ZB ∧ PhysicalNext.JointLoad.Heir.Seam ZB σ Ω:=by
   intro g ZB
   have hp : B.Funds g ZB:=by
     refine ⟨hj.symm,hn.symm,hj ▸ hz,?_,ho ▸ hc.symm,hc.symm,?_,M i,M (i+1),(h.he i ht.le).2,(h.he _ ht).2,X.mGauge ..⟩
     · change Towers.Deep (T i) _ _ _; rw [hX,hs,hn]; exact X.pay _
     · rw [ho,hc]; exact ⟨_,_,postP (B:=B) q _ _ _ W (hk.symm ▸ (h.he i ht.le).1) hu le_rfl, postP (B:=B) q _ _ _ W (hk.symm ▸ (h.he _ ht).1) hu le_rfl⟩
   refine ⟨⟨hp,rfl,he⟩, ⟨ M i, M (i+1), X.crosses .., X.mGauge ..,X.oath _ _,X.oath _ _,(h.he i ht.le).2,(h.he _ ht).2,_,_,X.trace i _,_,_,X.trace (i+1) _⟩,⟨hp, _,_,_,_,_,_,X.trace i _, X.trace (i+1) _,(h.he i ht.le).2,(h.he _ ht).2,X.oath i _,X.oath (i+1) _,X.crosses ..,X.mGauge ..⟩, ?_ ⟩
   have hh := ((X.pay i).2.2.2 [] (by simp)).2; rw [advanceC] at hh
   let A:=act (Pike E i) K (S i) j; refine ⟨hh,_,_,X.crosses ..,?_, (X.fund i).2.2.2.2, (X.fund (i+1)).1⟩
   exact mul_eq_one_comm.mpr (X.trace _ _).diagonalInv
lemma phonon (u v Ω D:ℝ)(P:Clip)(hk:0<u)(hx:0<Ω)(hy:0≤v)(hp:12 ≤ P.relaxation*u)(hu:0≤D)(K:KernelChoices)(j:ℕ)(l:ℝ): ∃ B:Teller su,B.bind=K∧B.top.supportExponent=2 ∧B.top.width=u∧B.top.paths=v+1∧ B.below=B.top∧B.top.clip=P∧ B.C=l∧B.η=Ω ∧ B.j=j:=by
    let S : Stage:= ⟨P,6,2,2,u,v+1,D,1,by omega,by omega,by norm_num,hk,by positivity,hp,le_rfl,hu⟩
    exact ⟨⟨K,S,S,j,Ω,l,hx⟩,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl⟩
lemma salutaryP (K:KernelChoices)(j:ℕ)(hj:4 ≤j):∃ (σ η Ω u v D γ:ℝ)(p:Clip)(B:Teller su),0 < σ∧0 < η∧1 ≤ Ω∧0<u∧0≤v∧ 0≤D∧ p.direct ≤1∧0<γ∧ B.top.supportExponent=2∧  B.bind=K∧ B.top.width=u ∧ v≤ B.top.paths∧B.below=B.top∧B.top.clip=p∧B.C=Ω∧B.η=σ∧ B.j=j∧∃ L:ℕ,∀ E:Patch,E.J=j→ E.Branches K su→ L≤ E.L.val →
    ∃ (M:ℕ→Bed)(T:ℕ→Towers E.L)(Λ:ℝ),Soil K p E σ η Ω M T∧ 1 ≤ Λ∧∀ (P:ChartRatio su),LocalRatio P→∃ c Γ:ℝ, 0<c∧1 ≤ Γ ∧∀ N (S:(ℕ→SparkMesh)),(∀ i,reachM E (S i))→ ∃ R:PulseRide K p E u v S N,Invoice R P M T c Γ γ D Λ:=by
  obtain ⟨q,h,t,x,y,hh,hp,hA,n,G⟩:= sustain K j hj
  obtain ⟨u,v,d,ψ,hU,hV,hd,hY,h',N,A,B,ht⟩:= sprouts K q j h hh hp hA
  let f:=inflateP q u hU
  obtain ⟨P,hk,h₁,h₂,h₃,h₄,h₅,h₆,h₇,h₈⟩:= phonon u v t d f hU hh hV (show 12 ≤12/u*u from by rw [div_mul_cancel₀ _ hU.ne']) hd K j y
  refine ⟨t,x,y,u,v,d,ψ,f,P,hh,hp,hA,hU,hV,hd,h,hY,h₁,hk,h₂,h₃ ▸ le_add_of_nonneg_right zero_le_one,h₄,h₅,h₆,h₇,h₈,max n N, fun E hE hf hc=>?_⟩
  subst j
  obtain ⟨M,T,H⟩:= G E hE ((le_max_left ..).trans hc)
  have hy:=soilP q u hU H; refine ⟨M,T,max 1 (B E.L),hy,le_max_left ..,fun O hm=>?_⟩
  obtain ⟨r,hL,hu⟩:= awoke hy (saluteP q u hU (hE.symm ▸ ht)) hm hf ((le_max_right ..).trans hc) hp (fun i he=> pathsP q u hU (h' _ he))
  exact ⟨_,max 1 (A E.L),hL,le_max_left ..,fun N S hz=> hu N S _ _ (le_max_left ..) (le_max_right ..) hz (le_max_right ..)⟩

end YM.QCD.Acre
#print axioms YM.QCD.Acre.broadcastP
