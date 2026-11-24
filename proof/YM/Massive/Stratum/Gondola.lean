import YM.Massive.Stratum.Galaxy
/-!
# Building all the coupled steps on an AtlasH

The mixed forest preanalysis. What's *not* yet determined this
way is the period mesh, or any actual density roll (that's a
consumer). This isn't a polymer-oracle assumption.
-/
set_option autoImplicit false
noncomputable section
namespace YM.QCD.Acre.Stratum
open Function Lattice RG Laurent Bloch Matrix Metric Precision Wilson Bid Craft Exterior Filter
open YM.Next.Free YM.Work YM.Further.PhysicalPeriodLimitF933
open WilsonStartup Design Change Extra.Iteration Stationary Tree Raft Garden Transfer Orbit Sparks Fog Birth Raft.ParcelR
open Flume Eyrie Fog.Mist YM.Massive.Stratum Push ConnectedActivityE6 Pressure Pressure.Stores Revolve Rudder
open scoped Topology ContDiff BigOperators Matrix.Norms.Frobenius Classical
variable {j n i k:ℕ}{Q:Rock j}{J:Plan j}{p:ChartRatio su} (Y:AtlasH Q J p) {R:PathData su}{F:Towers (Y.length i)}{m:SparkMesh}
local notation "Qq" => Q.Z.top.clip
local notation "Kq" => Q.Z.bind
local notation "u₀" => Q.Z.top.width
namespace AtlasH
structure Cabin (i:ℕ) where
  wing:Train j
  bed : Bed
  allowed : wing=Train.top j ∧ bed= Design.bed Qq ∨ bed=Q.beds wing
  path:PathData su
  priced : Enjoy bed Qq u₀ Q.v (loop (Y.towns i)) path
  spin :SunR (Fog.Mist.rate (Y.towns i).1)
omit Y in
lemma frost_nil (m:ℕ)(X:Price): ∃ U:Offer m X.r X.bill, IsEmpty U.roots ∧ U.lamp=0:=by
   let W : Empty → Bloom m:=Empty.elim; have he:dust W=0:=by ext i j; simp[dust]
   have h': Vital (dust W):= by rw [he]; exact Vital.solozero
   refine ⟨⟨_,W, ⟨X.live.le,fun i=>i.elim,Summable.of_finite,?_⟩,h'⟩, (inferInstance : IsEmpty Empty),he⟩; simpa using X.good
structure Barely (U:Cabin Y i):Prop where
   top: U.wing= Train.top j
   bed : U.bed=Design.bed Qq
   path: U.path=Design.top su Qq
   zen: IsEmpty U.spin.X.roots
   zit: IsEmpty U.spin.Y.roots
   lamp1: U.spin.X.lamp=0
   lamp2: U.spin.Y.lamp=0
   blank i: (U.spin.Z.page i).coeff=0
lemma begins (n:ℕ): ∃ Z:Cabin Y n,Barely Y Z:=by
   let T:= (Y.towns n).1
   obtain ⟨U,hU,ha⟩:= frost_nil 1 T.1.1; obtain ⟨X,hX,hb⟩:= frost_nil 2 T.1.2; obtain ⟨Z,hZ⟩:= soil T.2.live T.2.good
   let Y':Cabin Y n:= ⟨Train.top j,Design.bed Qq,Or.inl ⟨rfl,rfl⟩,Design.top su Qq,⟨Q.lawful.roots _ (zero_le_one.trans (ridge _)), Design.attached Qq⟩,U,X,Z⟩; exact ⟨Y',rfl,rfl,rfl,hU,hX,ha,hb,hZ⟩
lemma Cabin.quarry (U:Cabin Y i): QuarryQ Qq Q.Z.η Q.η Q.Z.C U.bed:=by
   cases U.allowed with
   | inl h => exact h.2.symm ▸ Q.lawful.field.top
   | inr h => exact h.symm ▸ Q.lawful.field.fare U.wing

abbrev sail (X:Cabin Y (i+1)):= steering (Y.path i) X.wing
structure Fixture (X:Cabin Y (i+1))(T:Cabin Y i)(V:SparkMesh)(a b:ℝ) where
   lands : (Y.sail X).land=T.wing
   arm: Towers (Y.length i)
   qual : DeltaQ Kq Qq Q.Z.η Q.Z.C (Y.sail X) X.bed T.bed arm
   terrace : Summit (Y.sail X) Kq V T.path X.path Qq u₀ Q.v arm p a (Y.gap i) (Y.cost i) Q.signal Q.D
   birth : let h:= (Y.boat i).applaud; BirthR (Y.marine i) J (terrace.back) (terrace.avenue (X.quarry Y) (T.quarry Y) qual Q.lawful.flour) (h.near.keep h.rates X.spin) (h.far.keep h.rates T.spin) b

lemma forms (X:Cabin Y (i+1))(m:SparkMesh)(hm:reachM (Y.path i).patch m):∃ (T:Cabin Y i)(a b:ℝ),Nonempty (Fixture Y X T m a b):=by
   let L:= Y.sail X; let v:= L.land; let B:= Q.beds v; have hb: QuarryQ Qq Q.Z.η Q.η Q.Z.C B:= Q.lawful.field.fare v
   have hx:=Y.boat i; have hL:= hx.applaud
   have ht: Q.n ≤ L.L.val:= hx.fares
   obtain ⟨D,hD⟩ : ∃ D,DeltaQ Kq Qq Q.Z.η Q.Z.C L X.bed B D:=by
        cases X.allowed with
        | inl he=> rw [he.2]; exact Q.lawful.field.begins L ht he.1
        | inr he=> rw [he]; exact Q.lawful.field.edges L ht
   obtain ⟨α,R,hR,⟨Y'⟩⟩:= hx.crossing X.wing _ B X.path D (X.quarry Y) hb X.priced hD m hm
   let U:= Y'.avenue (X.quarry Y) hb hD Q.lawful.flour
   obtain ⟨S,b,H⟩:= hL.sails Y'.back U X.spin
   let T:Cabin Y i:=⟨v,B,Or.inr rfl,R,hR,S⟩; exact ⟨T,α,b,⟨rfl,D,hD,Y',H⟩⟩

structure Survey (Y:AtlasH Q J p)(M:ℕ→ SparkMesh)(n:ℕ) where
  state (i:ℕ): Cabin Y i
  hue : Barely Y (state n)
  gauge : ℕ→ℝ
  price : ℕ→ℝ
  steps (i:ℕ)(_ : i< n): Fixture Y (state (i+1)) (state i) (M i) (gauge i) (price i)

lemma elevates (M:ℕ→SparkMesh)(h:∀ i< n,reachM (Y.path i).patch (M i)): Nonempty (Survey Y M n):=by
   let V i:= Classical.choose (Y.begins i); have hV i:= Classical.choose_spec (Y.begins i)
   choose W a b H using fun (i:ℕ)(hi:i< n)(T:Cabin Y (i+1))=>Y.forms T (M i) (h i hi)
   let X (i:ℕ)(hi:i≤n): Cabin Y i:= Nat.decreasingInduction (motive:=fun i _=>Cabin Y i) W (V n) hi
   have hw(i:ℕ)(hi:i< n): X i hi.le = W i hi (X (i+1) hi):=Nat.decreasingInduction_succ_left (motive:=fun i _=>Cabin Y i) W (V n) hi hi.le
   let T (i:ℕ):= if h:i≤n then X i h else V i
   have hk i (hi:i≤n): T i=X i hi:=dif_pos hi
   let f (i:ℕ):= if h:i< n then a i h (T (i+1)) else 0; let g (i:ℕ):= if h:i< n then b i h (T (i+1)) else 0
   refine ⟨⟨T, ?_, f,g,fun i hi=> Classical.choice (?_)⟩⟩
   · rw [hk n le_rfl,show X n le_rfl= V n from Nat.decreasingInduction_self (motive:=fun i _=>Cabin Y i) W _]; exact hV _
   unfold f g; rw [dif_pos hi,dif_pos hi, hk i hi.le, hk (i+1) hi, hw i hi]; exact H i hi _
end AtlasH
end YM.QCD.Acre.Stratum
#print axioms YM.QCD.Acre.Stratum.AtlasH.elevates
