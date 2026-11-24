import YM.QCD.Beam.Tense
import YM.QCD.Acre.Trail
/-! # Relax early. synchronize Lire purchase on fixed actual Ratio. -/
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

def inflateP (q:Clip)(w:ℝ)(h:0<w): Clip:={q with relaxation:=12/w,radius_pos:=by positivity}
variable (q u)(he:0<u)
local notation "Z"=> inflateP q u he
lemma bedP : Design.bed Z=Design.bed q:=by exact rfl
lemma topP : Design.top G Z=Design.top G q:=by exact rfl
lemma soilP (S:Soil K q E σ η Ω M T): Soil K Z E σ η Ω M T:=by
   exact ⟨S.top,S.fund,fun i n=> let h:= S.trace i n; ⟨h.diagonalInv,h.inverse,h.roots,h.starts,h.same,h.symmetric,h.uniform⟩,S.oath,S.pay,S.orient,S.cell,S.crosses,fun i c f h=> let t:= S.mGauge i c f h; ⟨t.m,t.n,t.fPart,t.nPart,t.oPart,t.orthogonal⟩⟩
lemma pathsP {R:PathData G}{d:ℝ}(h:R.Bounds q u v d): R.Bounds Z u v d:= ⟨h.width,h.rows,h.two,h.three,h.four,h.invariant,h.symTerms,h.metric,h.loopTerms,h.loop_normal⟩
variable {F L :Side→ℝ}
lemma saluteP (P:PreCut K q j η σ Ω u v γ D i F L): PreCut K Z j η σ Ω u v γ D i F L:=P
-- propose retain original Γ in Stage positive paths using top bound; actual Clip from Sprouts. choose after obtaining Ember.
variable {u q} {S:SparkMesh}
open Beam Ride
lemma postP {B:Teller su} {R:PathData su} (p:Clip) (v v' α μ:ℝ)(h:R.Bounds p B.top.width v α) (hv :v ≤v') (hp : α ≤ μ): R.Bounds p B.top.width v' μ:= ⟨h.width,fun p=> budget_loosen (h.rows p) hv,budget_loosen h.two hp,budget_loosen h.three hv,budget_loosen h.four hv,h.invariant,h.symTerms,h.metric,h.loopTerms,h.loop_normal⟩
lemma emitP {B:Teller su} (X:Soil K q E σ η Ω M T)(R:Ride K q E u v S N)(h:Ingress R p M T x y γ D W)
 (hz:E.Branches K su) (hj:B.bind=K)(hk:B.top.width=u)(ho:B.below=B.top)(hc:B.top.clip=q)(hX:B.C=Ω)(hs:B.η=σ)(hu:v ≤ B.top.paths)(hn:B.j=E.J)(i j)(ht:i<N)(t:ℝ)
 (he : 100*(1+radiusB t)≤ ((footM E S N (i+1)).n j).val) :
    let g:=act (Pike E i) K (footM E S N (i+1)) j
    let ZB:Tube su g:=⟨T i,R.path i,q,R.path (i+1),q⟩
    Works B E.L t g ZB∧SliceRows.Stamp ZB:=by
   intro g ZB
   have hp : B.Funds g ZB:=by
     refine ⟨hj.symm,hn.symm,hj ▸ hz,?_,ho ▸ hc.symm,hc.symm,?_,M i,M (i+1),(h.he i ht.le).2,(h.he _ ht).2,X.mGauge ..⟩
     · change Towers.Deep (T i) _ _ _; rw [hX,hs,hn]; exact X.pay _
     · rw [ho,hc]; exact ⟨_,_,postP (B:=B) q _ _ _ W (hk.symm ▸ (h.he i ht.le).1) hu le_rfl, postP (B:=B) q _ _ _ W (hk.symm ▸ (h.he _ ht).1) hu le_rfl⟩
   exact ⟨⟨hp,rfl,he⟩, M i, M (i+1), X.crosses .., X.mGauge ..,X.oath _ _,X.oath _ _,(h.he i ht.le).2,(h.he _ ht).2,_,_,X.trace i _,_,_,X.trace (i+1) _⟩

lemma gear (u v Ω D:ℝ)(P:Clip)(hk:0<u)(hx:0<Ω)(hy:0≤v)(hp:12 ≤ P.relaxation*u)(hu:0≤D)(K:KernelChoices)(j:ℕ)(l:ℝ): ∃ B:Teller su,B.bind=K∧B.top.width=u∧B.top.paths=v+1∧ B.below=B.top∧B.top.clip=P∧ B.C=l∧B.η=Ω ∧ B.j=j:=by
    let S : Stage:= ⟨P,6,2,1,u,v+1,D,1,by omega,by omega,by norm_num,hk,by positivity,hp,le_rfl,hu⟩
    exact ⟨⟨K,S,S,j,Ω,l,hx⟩,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl⟩
lemma lateP (K:KernelChoices)(j:ℕ)(hj:4 ≤j):∃ (σ η Ω u v D γ:ℝ)(p:Clip)(B:Teller su),0 < σ∧0 < η∧1 ≤ Ω∧0<u∧0≤v∧ 0≤D∧ p.direct ≤1∧0<γ∧ B.bind=K∧ B.top.width=u ∧ v≤ B.top.paths∧B.below=B.top∧B.top.clip=p∧B.C=Ω∧B.η=σ∧ B.j=j∧∃ L:ℕ,∀ E:Patch,E.J=j→ E.Branches K su→ L≤ E.L.val →
    ∃ (M:ℕ→Bed)(T:ℕ→Towers E.L)(Λ:ℝ),Soil K p E σ η Ω M T∧ 1 ≤ Λ∧∀ (P:ChartRatio su),LocalRatio P→∃ c Γ:ℝ, 0<c∧1 ≤ Γ ∧∀ N (S:SparkMesh),reachM E S→ ∃ R:Ride K p E u v S N,Ingress R P M T c Γ γ D Λ:=by
  obtain ⟨q,h,t,x,y,hh,hp,hA,n,G⟩:= sustain K j hj
  obtain ⟨u,v,d,ψ,hU,hV,hd,hY,h',N,A,B,ht⟩:= sprouts K q j h hh hp hA
  let f:=inflateP q u hU
  obtain ⟨P,hk,h₁,h₂,h₃,h₄,h₅,h₆,h₇⟩:= gear u v t d f hU hh hV (show 12 ≤12/u*u from by rw [div_mul_cancel₀ _ hU.ne']) hd K j y
  refine ⟨t,x,y,u,v,d,ψ,f,P,hh,hp,hA,hU,hV,hd,h,hY,hk,h₁,h₂ ▸ le_add_of_nonneg_right zero_le_one,h₃,h₄,h₅,h₆,h₇,max n N, fun E hE hf hc=>?_⟩
  subst j
  obtain ⟨M,T,H⟩:= G E hE ((le_max_left ..).trans hc)
  have hy:=soilP q u hU H; refine ⟨M,T,max 1 (B E.L),hy,le_max_left ..,fun O hm=>?_⟩
  obtain ⟨r,hL,hu⟩:= embarkM hy (saluteP q u hU (hE.symm ▸ ht)) hm hf ((le_max_right ..).trans hc) hp (fun i he=> pathsP q u hU (h' _ he))
  exact ⟨_,max 1 (A E.L),hL,le_max_left ..,fun N S hz=> hu N S _ _ (le_max_left ..) (le_max_right ..) hz (le_max_right ..)⟩
lemma concerns (t c:ℝ)(ht : -(1/2:ℝ)< t)(he:t<0)(h:0≤c) (P:Teller su): ∃ Q:Target su P, Q.rate=t∧ Q.exp=c:=by
   let i:=P.top.supportExponent; let j:= P.top.width; let k:= P.below.width; let hE:= min i (min j k)
   have hv:= lt_min P.top.price_pos (lt_min P.top.width_pos P.below.width_pos)
   have hx : hE≤ i:=min_le_left ..; have hp : hE≤j:=(min_le_right ..).trans (min_le_left ..); have hu : hE≤k:=(min_le_right ..).trans (min_le_right ..); change 0<hE at hv
   let A:=Next.Foundations.chart su; have hA:=Next.Foundations.chart_ok su
   exact ⟨⟨hE/16,c,1,t,500,le_rfl,A,hA,by positivity,by norm_num,h,ht,he,by change 4*(hE/16) < i∧ 8*(hE/16) < j∧8*(hE/16) < k; refine ⟨?_,?_,?_⟩<;> linarith⟩,rfl,rfl⟩
open Push.AbsoluteSums
variable {L:Side}

end YM.QCD.Acre
