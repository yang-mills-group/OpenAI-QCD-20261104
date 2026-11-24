import YM.QCD.Disc.Lift
/-! # Balancing aux polylogarithmic shapes against physical growth. -/
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
open PhysicalNext.Repeat Slide PulseRide
open Deck Moss Calm Jets.Touch
variable {E: Patch}{C L c:Side}{x:ℝ}{n m k i:ℕ}
abbrev rad (x:ℝ):= radiusB x
def merit (k H:ℕ)(x:ℝ): ℕ:= (k+H+tideP H 1+1000)*rad x
noncomputable def rootX (L:Side)(u:ℕ)(x:ℝ):ℕ:= Nat.log L.val (12*(u*rad x))+1
noncomputable def head (L:Side)(u:ℕ)(x:ℝ):Side:= L^rootX L u x
noncomputable abbrev style (L:Side)(u:ℕ)(x:ℝ):= 81*(head L u x).val+1
-- poly book
structure Tall (P:Patch) (H l n s M:ℕ)(x:ℝ):Prop where
 pass: 0<l*rad x
 prior: 2*(l*rad x+1) ≤ (head P.L l x).val
 ripe:4*rad x ≤ l*rad x
 rides:tideP H (rad x) ≤ l*rad x
 radH: 2*(2*(l*rad x)+3)<2*(head P.L l x).val
 reach:100*(1+rad x)≤ 2*(head P.L l x).val
 clip: GateVolume P.J≤ 2*(head P.L l x).val
 turn:2*style P.L l x≤ n*rad x
 act (i:Stars): (stellar (head P.L l x) i.val).val ≤ Trio.most s x
 long: M*rad x ≤ 2*(head P.L l x).val
lemma upperL (l:ℕ)(hp:1≤rad x)(he:0<l) : (head L l x).val ≤ L.val*12*l*rad x:=by
    change (↑(L^(_+1)):ℕ) ≤ _; rw [PNat.pow_coe, pow_succ] -- check
    have h:= Nat.pow_log_le_self L.val (x:=12*(l*rad x)) (by positivity); refine (Nat.mul_le_mul_right L.val h).trans_eq ?_; ac_rfl
lemma stela (V:Side)(i:Stars) : (stellar V i.val).val=2*(V.val * roller i.val):=by
    unfold stellar; simp [Slide.roller]; try rfl
-- common aux
lemma highest (L:Patch)(H M:ℕ)(hL:2≤L.L.val): ∃ (l n m:ℕ),0<l∧∀ᶠ x:ℝ in atTop, Tall L H l n m M x:=by
     let l:= tideP H 1+1000+GateVolume L.J+M; let n:=2*(82*(L.L.val*12*l)+1); have he:0<l:=by unfold l; omega
     refine ⟨l,n,n,he,?_⟩; filter_upwards [Work.E01.radiusB_tendsto.eventually_ge_atTop 1] with x hx
     let b:=rad x; let p:=l*b; have hp : b ≥ 1:=hx; have hu: p ≥ l:= Nat.le_mul_of_pos_right _ hp; have hz:p>0:= he.trans_le hu
     have hb: b*100 ≤p:=by unfold p l; nlinarith [L.coarse]
     let w:=(head L.L l x).val; have hw: 12*p<w:=by
          unfold w head rootX; rw [PNat.pow_coe]; apply Nat.lt_pow_succ_log_self; omega -- coe lemma
     have hR:= upperL (L:=L.L) l hx he
     have ht: 2*(81*w+1) ≤ n*b :=by change w ≤ _*b at hR; unfold n; nlinarith
     refine ⟨hz, (by change 2*(p+1)≤w; omega), (by change 4*b≤p; omega), ?_, (by change 2*(2*p+3)<2*w; omega), (by change 100*(1+b)≤2*w; omega), ?_, ht,fun i=>?_,?_⟩
     · unfold l tideP Moss.orbitD Mint.width; change _ ≤ _*b
       change 1 ≤ rad x at hp; unfold b at *; nlinarith -- caution nlinarith expensive
     · have hv: GateVolume L.J ≤ l :=by unfold l; omega
       change _ ≤2*w; omega
     · rw [stela]; have he:= roll_cap w i; unfold Trio.most Trio.base Trio.tent; change 2*(w*roller i.val) ≤_; unfold Meadow.studio Meadow.roomSize Mint.width; dsimp only [b,rad] at ht; nlinarith -- risk
     have hh: M≤l:=by unfold l; omega
     change M*b≤2*w; have hp:=Nat.mul_le_mul_right b hh; change M*b≤p at hp; omega
lemma rub (L:Side)(l:ℕ)(he:0<l): Strip L (fun x=> l*rad x) ∧ Strip L (fun x=> (head L l x).val) ∧ Strip L (style L l):=by
    have hp': Strip L (fun x=> (head L l x).val):=by
          intro r hr; have hv:=Seat.timesL (L:=L) Seat.radius (L.val*12*l:ℕ)
          filter_upwards [hv r hr,Work.E01.radiusB_tendsto.eventually_ge_atTop 1] with x hx ht
          have h : ((head L l x).val:ℝ) ≤ ((L.val*12*l*rad x:ℕ):ℝ):=Nat.cast_le.mpr (upperL l ht he); change |((head L l x).val:ℝ)|≤ _; rw [abs_of_nonneg (by positivity)]; exact h.trans (by push_cast at *; exact (le_abs_self _).trans hx)
    refine ⟨Seat.equal (Seat.timesL Seat.radius (l:ℝ)) (Eventually.of_forall fun i=>by push_cast; rfl), hp', Seat.equal (Seat.comb (Seat.timesL hp' 81) (Seat.numbers 1)) (Eventually.of_forall fun i=> by unfold style; push_cast; rfl)⟩
end YM.QCD.Acre
