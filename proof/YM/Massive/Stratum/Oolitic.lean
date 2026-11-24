import YM.QCD.Acre.Yonder
import YM.QCD.Beam.Writer
/-!
# One pre-stride bed discipline for all the physical blocks

UV initialization uses a top flight but must attach the
Wilson bed, whereas in the interior we use the table chosen
from `pledges` by wing. The table and bounds therefore need
to work for every later block radius, simultaneously.
Based on `Yonder`, this lifts the guarantees to *mixed* strides.
-/
set_option autoImplicit false
noncomputable section
namespace YM.QCD.Acre
open Function Lattice RG Laurent Bloch Matrix Metric Precision Wilson Bid Craft Exterior Filter
open YM.Next.Free YM.Work YM.Further.PhysicalPeriodLimitF933
open WilsonStartup Design Change Extra.Iteration Stationary Classical
open scoped Topology ContDiff BigOperators
variable {j t k i l n: ℕ}{K:KernelChoices}{q: Clip}{E:Patch}{σ η Ω A γ b C D H u v x y:ℝ}{p:ChartRatio su}
namespace Stratum
structure QuarryQ (q:Clip)(σ η Ω:ℝ)(B:Bed) : Prop where
   fund : B.covered σ Ω
   trace n: Floor B q n η Ω
   oath n: Sworn B n su

structure DeltaQ (K:KernelChoices)(q:Clip)(σ Ω:ℝ)(S:Flight j j)(B T:Bed)(U:Towers S.L):Prop where
   pay : U.Deep σ Ω (j-2)
   orient : U.A0=(S.duo K.penalty).A0
   cell : U.T=(S.duo K.penalty).T
   crosses {c f:Side} (h:f.val=c.val*S.L.val): Towers.Diagonal (S.visit K h) B T U
   mGauge {c f:Side} (h:f.val=c.val*S.L.val): Towers.Roll (S.visit K h) B T U q q

lemma crags (K:KernelChoices)(j:ℕ)(hj:4≤j):∃ q:Clip,q.direct≤1∧∃ σ η Ω,0<σ ∧ 0<η ∧ ∃ (n:ℕ)(X:Train j→Bed),
   (∀ v,QuarryQ q σ η Ω (X v)) ∧ (∀ c,(X (.top j)).diagonal.acts c=1) ∧ ∀ F:Flight j j,n≤F.L.val→∃ U,DeltaQ K q σ Ω F (X F.wing) (X F.land) U:=by
  obtain ⟨Q,l,g,d,h⟩:= pledges K
  obtain ⟨p,hp,hp'⟩:= inserted (h.fit j)
  obtain ⟨w,Z,e,hw,he,H⟩ := F07.answer (TypeFace 3) (Q.Ω j) (Q.η j) (Q.α j) (Q.eta_pos j) (Q.alpha_pos j)
  obtain ⟨x,y,hx,W⟩:= F08.answer p p K.penalty (Q.Ω j) (Q.α j) (Q.α j) (Q.Ω j) e Z (j-2) K.penalty_pos (Q.alpha_pos j) (Q.alpha_pos j) he
  let u:=min x (Q.α j); let v:= max y (Q.Ω j)
  choose M hM h1 h2 h3 h4 using fun i=> h.bottom _ hj _ hp.le i
  refine ⟨p,hp'.le,u,Q.η j,v,lt_min hx (Q.alpha_pos _),Q.eta_pos _,d j,M,fun i=>⟨Change.covered_mono (h1 i) (min_le_right ..) (le_max_right ..),fun n=>Change.floor_mono (h2 _ n) le_rfl (le_max_right ..),fun n=>h3 i n su⟩,h4 _ rfl,fun E ht=>?_⟩
  let i:=E.wing; let b:=E.land
  have hQ := h.hop _ _ (show Mag j j from ⟨hj,hj,Or.inl rfl⟩) E
  have hf (c f:Side) := check_bleep K (l j) (l j) (h.net _) (h.net _) E hj (M i) (M b) (hM i) (hM b) (c:=c) (f:=f)
  have hs (c f:Side) := YM.Next.Free.diagonal K (l j) (l j) (h.net _) (h.net _) E hj (M i) (M b) (hM i) (hM b) (c:=c) (f:=f)
  let S := E.rollFunds K.penalty (l j) (l j)
  let R : Towers E.L := E.duo K.penalty
  obtain ⟨P,hP,h5,h6⟩:= H S hQ.2.1 (hQ.2.2 ht)
  obtain ⟨T,hT,hG⟩:= W (M i) (M b) (h1 _) (h1 _) _ h5 E.L E.odd R hQ.1
  have Hc:= hG 1 (1 * E.L) rfl
  refine ⟨T,deep_mono _ hT (min_le_left ..) (le_max_left ..), Hc.first.symm,Hc.form.symm,fun {c f} h'=>?_, fun {c f} h'=>?_⟩
  · obtain ⟨h₁,h₂,h₃⟩:= hs c f h'
    constructor <;> (first| rw [← Hc.first,← Hc.form]| rw [← Hc.first]| rw [← Hc.form]) <;> assumption
  exact F09.answer _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (hG _ _ h') (h2 _ f) (h2 _ c) (hs c f h') (fun n=> (h6 n).1) (hf c f h')

structure Mantle (K:KernelChoices)(q:Clip)(σ η Ω:ℝ)(n:ℕ)(X:Train j→ Bed) : Prop where
  fare : ∀ v, QuarryQ q σ η Ω (X v)
  top : QuarryQ q σ η Ω (Design.bed q)
  edges : ∀ (S:Flight j j), n≤ S.L.val→∃ U, DeltaQ K q σ Ω S (X S.wing) (X S.land) U
  begins : ∀ S:Flight j j,n ≤ S.L.val→ S.wing = Train.top _→ ∃ U, DeltaQ K q σ Ω S (Design.bed q) (X S.land) U

theorem mantel (K:KernelChoices)(j:ℕ)(hj:4≤j):∃ q:Clip,q.direct≤1 ∧∃ σ η Ω,0<σ ∧ 0<η ∧ 1≤Ω ∧∃ n:ℕ,∃ X:Train j→ Bed, Mantle K q σ η Ω n X:=by
   obtain ⟨p,hp,s,e,c,hs,hc,n,X,hX,h0,Y⟩:= crags K j hj
   obtain ⟨u,D,hU,hD⟩:= spin_cost p s c hs
   let v:= min s u; let A:= max (max 1 c) D
   have he : 1 ≤ A:= (le_max_left ..).trans (le_max_left ..); have ht : c ≤ A:= (le_max_right ..).trans (le_max_left ..); have hh := lt_min one_pos hc
   refine ⟨p,hp,v,min 1 e,A,lt_min hs hU,hh,he,n,X, ?_,?_,?_,?_⟩
   · exact fun i=>⟨covered_mono (hX i).fund (min_le_left ..) ht,fun n=>floor_mono ((hX i).trace n) (min_le_right ..) ht,(hX i).oath⟩
   · exact ⟨Design.covered p hp he,fun c=> Design.level p hp c (min_le_left ..) he,fun _=> Design.top_sworn p hp⟩
   · intro S ht'; obtain ⟨T,hT⟩:= Y S ht'; exact ⟨T,deep_mono _ hT.pay (min_le_left ..) ht,hT.orient,hT.cell,hT.crosses,hT.mGauge⟩
   intro S hp' hl; obtain ⟨T,hT⟩:= Y S hp'
   have h (c:Side): (X S.wing).diagonal.acts c=1:=by rw [hl]; exact h0 c
   obtain ⟨V,H⟩:= hD _ hp (hX S.wing).fund.2.2.2.1
   obtain ⟨hg,hL⟩:= H _ _ _ hT.pay
   refine ⟨spin V T,deep_mono _ hg (min_le_right ..) (le_max_right ..), hT.orient,hT.cell,fun {c f} he=>?_,fun {c f} he=>?_⟩
   · obtain ⟨a,b,c⟩:= top_diagonal (hT.crosses he) ((hX _).trace f) (h f); exact ⟨a,b,c⟩
   obtain ⟨h₁,h₂,h₃⟩:= hL c f he; exact trans_roll (hT.mGauge he) h₁ h₂ (h₃ _ _ ((hX _).trace f) (h f))

variable (v:ℝ) (hV:0<v) {X:Train j→Bed} (h:Mantle K q σ η Ω n X)
lemma QuarryQ.inflate {B:Bed}(q:Clip) (h:QuarryQ q σ η Ω B):QuarryQ (inflateP q v hV) σ η Ω B:=
    ⟨h.fund,fun i=> let t:= h.trace i; ⟨t.diagonalInv,t.inverse,t.roots,t.starts,t.same,t.symmetric,t.uniform⟩,h.oath⟩
lemma DeltaQ.inflate {T B: Bed} {S:Flight j j} {F:Towers S.L} (h: DeltaQ K q σ Ω S T B F): DeltaQ K (inflateP q v hV) σ Ω S T B F:=by
   exact ⟨h.pay,h.orient,h.cell,h.crosses,fun {c f} hh=> let t:= h.mGauge hh; ⟨t.m,t.n,t.fPart,t.nPart,t.oPart,t.orthogonal⟩⟩
include h
theorem cloak : Mantle K (inflateP q v hV) σ η Ω n X:=by
   refine ⟨fun i=>QuarryQ.inflate v hV q (h.fare i), QuarryQ.inflate v hV q h.top,fun S hs=>?_,fun S hs hJ=>?_⟩
   · obtain ⟨T,hT⟩:=h.edges S hs; exact ⟨T, hT.inflate ..⟩
   obtain ⟨T,hT⟩:= h.begins S hs hJ; exact ⟨T, DeltaQ.inflate v hV hT⟩
end Stratum
end YM.QCD.Acre
#print axioms YM.QCD.Acre.Stratum.mantel
#print axioms YM.QCD.Acre.Stratum.cloak
