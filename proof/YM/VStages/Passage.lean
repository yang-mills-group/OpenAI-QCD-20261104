import YM.VStages.Stationing
import YM.Massive.Stratum.Mesh
set_option autoImplicit false
noncomputable section
namespace YM.QCD.Acre.Stratum.MarchQ
open Function Lattice RG Laurent Bloch Matrix Metric Precision Wilson Bid Craft Exterior Filter
open YM.Next.Free YM.Work YM.Further.PhysicalPeriodLimitF933
open WilsonStartup Design Change Extra.Iteration Stationary Tree Raft Garden Transfer Orbit Sparks Fog Birth Raft.ParcelR
open Flume Fog.Mist YM.Massive.Stratum Push ConnectedActivityE6 Pressure Pressure.Stores
open scoped Topology ContDiff BigOperators Matrix.Norms.Frobenius Classical
variable {j t k i l n N: ℕ}{K:KernelChoices}{p:ChangeQ→ChartRatio su}{h s:ℕ→ℕ}
 (P:Docket K h s)(J:(i:ℕ)→Plan (rank i))
open ChangeQ

variable {P J} {d:ChangeQ→ℕ} (T:Track P J p d)
namespace Track
abbrev level (i:ℕ) := (T.beam i).node.lo
abbrev node (i:ℕ): ChangeQ := ⟨T.level i,T.level (i+1),  (show (T.beam i).node.hi=T.level (i+1) from (T.nexts i).1) ▸ (T.beam i).node.path⟩ -- dependent
lemma node_at (i:ℕ): (T.beam i).node= T.node i:=by
    have hw (b c:ChangeQ)(he:b.lo=c.lo)(hf:b.hi=c.hi): b=c := by cases b; cases c; congr
    exact hw _ _ rfl (T.nexts i).1
abbrev town (i:ℕ):= (T.beam i).toX
abbrev length (i:ℕ):= (T.beam i).L

lemma there (i:ℕ):∃ S:Flight (T.node i).old (T.node i).new, FlightTicket P J (T.node i) S (T.town (i+1)) (T.town i) (p (T.node i)) (T.beam i).c (T.beam i).Θ (T.beam i).fare ∧ S.L=T.length i ∧ HEq S (T.beam i).flight:=by
   rw [←node_at, ← show (T.beam i).fromX=T.town (i+1) from (T.nexts i).2.1]; exact ⟨_,(T.beam i).supporting,rfl,HEq.rfl⟩
noncomputable def flight (i:ℕ):Flight (rank (T.level (i+1))) (rank (T.level i)):= (T.there i).choose
lemma length_eq (i:ℕ): (T.flight i).L=T.length i:=(T.there i).choose_spec.2.1
lemma flight_eq (i:ℕ): HEq (T.flight i) (T.beam i).flight := (T.there i).choose_spec.2.2
lemma ticket (i:ℕ): FlightTicket P J (T.node i) (T.flight i) (T.town (i+1)) (T.town i) (p (T.node i)) (T.beam i).c (T.beam i).Θ (T.beam i).fare:= (T.there i).choose_spec.1
-- use flight i, `.L` as meeting ST for future
abbrev spacing (i:ℕ):= (T.flight i).L

theorem smoothWindow (m) : ∃ i,m ≤ i ∧ T.node i=steady (T.level i):=by obtain ⟨i,h,H⟩:= T.stops m; exact ⟨i,h,(T.node_at i).symm.trans H⟩

structure CouncilW (i:ℕ) where
   bed: Bed
   path:PathData su
   priced: Enjoy bed (P.stage (T.level i)).clip (P.stage (T.level i)).width (P.allowance (T.level i)) (loop (T.town i)) path
   wing:Train (rank (T.level i))
   sun:SunR (Mist.rate (T.town i).1)

structure Incept (X:CouncilW T i):Prop where
   top: X.wing= Train.top _
   bed : X.bed=Design.bed (P.stage (T.level i)).clip
   root: X.path=Design.top su (P.stage (T.level i)).clip
   zen: IsEmpty X.sun.X.roots
   zit: IsEmpty X.sun.Y.roots
   lamp1: X.sun.X.lamp=0
   lamp2: X.sun.Y.lamp=0
   blank i: (X.sun.Z.page i).coeff=0
lemma caps (n:ℕ): ∃ U:CouncilW T n, Incept T U:=by
   let k:=T.level n
   let U:= (T.town n).1
   obtain ⟨P₀,hP,hL⟩:= AtlasH.frost_nil 1 U.1.1
   obtain ⟨P₁,hP',hL'⟩:= AtlasH.frost_nil 2 U.1.2
   obtain ⟨Z,hZ⟩:= soil U.2.live U.2.good
   exact ⟨⟨Design.bed (P.stage k).clip,Design.top su (P.stage k).clip,⟨P.ready _ _ (zero_le_one.trans (ridge _)), Design.attached _⟩, Train.top _,P₀,P₁,Z⟩,rfl,rfl,rfl,hP,hP',hL,hL',hZ⟩

def Remains(X:CouncilW T i): Prop:= X.bed=P.beds (T.level i) X.wing
local notation "R!"=> T.node i
set_option quotPrecheck false
local notation "w★" i=> (P.stage (T.level i))
abbrev sail (X:CouncilW T (i+1)):= helm (T.flight i) X.wing
structure Board (T:Track P J p d) (i:ℕ) (X:CouncilW T (i+1))(W:CouncilW T i) (m:SparkMesh)(a b:ℝ) where
   landed : (T.sail X).land=W.wing
   prices: Towers (T.spacing i)
   throughoutIn: QuarryQ (P.stage (T.level (i+1))).clip (P.width (T.node i)) (P.floor (T.node i)) (P.cost (T.node i)) X.bed
   throughoutOut: QuarryQ (P.stage (T.level i)).clip (P.width (T.node i)) (P.floor (T.node i)) (P.cost (T.node i)) W.bed
   delta : DeltaW K (P.stage (T.level (i+1))).clip (P.stage (T.level i)).clip (P.width (T.node i)) (P.cost (T.node i)) (T.sail X) X.bed W.bed prices
   terrace : Aloft (T.sail X) K m W.path X.path (P.stage (T.level (i+1))).clip (P.stage (T.level i)).clip (P.stage (T.level (i+1))).width (P.allowance (T.level (i+1))) prices (p (T.node i)) a (T.beam i).c (T.beam i).Θ (P.gamma (T.node i)) (P.slope (T.node i))
   birth : let h:= (T.ticket i).applause; BirthW (T.beam i).fare (J (T.level (i+1))) (J (T.level i)) terrace.back (terrace.avenue throughoutIn throughoutOut delta (P.retail (T.node i)).growth (rank_ge _)) (h.near.keep h.rates X.sun) (h.far.keep h.rates W.sun) b
   remains : T.Remains W

private lemma begins_eq (b:ChangeQ) (S:Flight b.old b.new) (Z:Bed) (e:b=steady b.lo) (h: Z=Design.bed (P.stage b.hi).clip) (hm:P.lim b ≤ S.L.val) (hi:S.wing=Train.top _) : QuarryQ (P.stage b.hi).clip (P.width b) (P.floor b) (P.cost b) Z ∧∃ U:Towers S.L, DeltaW K (P.stage b.hi).clip (P.stage b.lo).clip (P.width b) (P.cost b) S Z (P.beds b.lo S.land) U:=by
    obtain ⟨i,hv,b⟩:=b; have he : hv=i:=congr_arg ChangeQ.hi e; subst hv
    rw [h]; exact ⟨(P.crown i).top,(P.crown i).begins S hm hi⟩
lemma stretching (X:CouncilW T (i+1)) (h:T.Remains X∨(T.Incept X ∧ T.node i=steady (T.level i))) (m:SparkMesh)(hm:reachM (T.flight i).patch m) : ∃ U:CouncilW T i, T.Remains U ∧ ∃ a b,Nonempty (Board T i X U m a b):=by
    let p:= T.sail X; let v:= p.land; let b:=P.beds (T.level i) v; let r:= T.node i
    have hx:= T.ticket i; have hg:=hx.applause
    obtain ⟨h1,h2⟩ : QuarryQ (P.stage r.hi).clip (P.width r) (P.floor r) (P.cost r) X.bed ∧ ∃ V:Towers p.L,DeltaW K (P.stage r.hi).clip (P.stage r.lo).clip (P.width r) (P.cost r) p X.bed b V:=by
        rcases h with h|⟨h,h'⟩
        · unfold Remains at h; rw [h]; exact ⟨(P.retail r).upper X.wing, (P.retail r).edges p hx.fares⟩
        exact begins_eq r p X.bed h' h.bed hx.fares h.top
    have hb:= (P.retail r).lower v
    obtain ⟨V,hV⟩:=h2
    obtain ⟨α,Z,hZ,⟨D⟩⟩:= hx.crossing X.wing X.bed b X.path V h1 hb X.priced hV m hm
    let a := D.avenue h1 hb hV (P.retail r).growth (rank_ge r.lo)
    obtain ⟨U,c,H⟩:= hg.sails D.back a X.sun
    exact ⟨⟨b,Z,hZ,v,U⟩, rfl,α,c,⟨rfl,V,h1,hb,hV,D,H,rfl⟩⟩
structure Survey (M:ℕ→SparkMesh)(n:ℕ) where
   state (i:ℕ): CouncilW T i
   price :Incept T (state n)
   gauge :ℕ→ℝ
   spin :ℕ→ℝ
   steps (i:ℕ)(h:i<n): Board T i (state (i+1)) (state i) (M i) (gauge i) (spin i)
lemma initiative (M:ℕ→SparkMesh)(h:∀ i<n,reachM (T.flight i).patch (M i))(hx:∀ i,n=i+1→T.node i=steady (T.level i)): Nonempty (Survey T M n):=by
   let R i:= (T.caps i).choose; have hr i:= (T.caps i).choose_spec
   let Q(i:ℕ): Type 1 := {x:CouncilW T i// if i=n then T.Incept x else T.Remains x}
   let z:Q n:= ⟨R n,if_pos rfl ▸ hr n⟩
   have first (i)(p:i<n)(X:Q (i+1)) : ∃ Y:Q i, ∃ a b:ℝ, Nonempty (Board T i X.val Y.val (M i) a b):=by
       obtain ⟨V,hV,a,b,hW⟩:= stretching T X.val (by
             have he:=X.property; split_ifs at he with ht ; exact Or.inr ⟨he,hx _ ht.symm⟩; exact Or.inl he) (M i) (h i p)
       exact ⟨⟨V,by rw[if_neg p.ne];exact hV⟩,a,b,hW⟩
   choose W a b H using first
   let X (i:ℕ)(hi:i≤n): Q i:= Nat.decreasingInduction (motive:=fun i _=>Q i) W z hi
   have hw(i:ℕ)(hi:i< n): X i hi.le = W i hi (X (i+1) hi):=Nat.decreasingInduction_succ_left (motive:=fun i _=>Q i) W _ hi hi.le
   let L (i:ℕ):= if h:i≤n then (X i h).val else R i
   have hk i (hi:i≤n): L i=(X i hi).val:=dif_pos hi
   let f (i:ℕ):= if h:i< n then a i h (X (i+1) h) else 0; let g (i:ℕ):= if h:i< n then b i h (X (i+1) h) else 0
   refine ⟨⟨L, ?_, f,g,fun i hi=> Classical.choice (?_)⟩⟩
   · rw [hk n le_rfl,show X n le_rfl= z from Nat.decreasingInduction_self (motive:=fun i _=>Q i) W _]; exact hr _
   unfold f g; rw [dif_pos hi,dif_pos hi,hk i hi.le,hk (i+1) hi,hw i hi]; exact H i hi _
end Track
#print axioms Track.initiative
end YM.QCD.Acre.Stratum.MarchQ
