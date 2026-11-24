import YM.QCD.Hearth.Seen
import YM.QCD.Globe.Dome
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
variable {S:SparkMesh}
open Hearth
lemma dom_n (B L:Side)(hb: Odd L.val)(ht: 2 ≤ L.val) : ∃ S: SparkMesh,∀ i, S.n i=B*L^i:=by
    let v (i:ℕ): Side:= B*L^i; let C i (j:ℕ):= L.val^(j-i)
    refine ⟨⟨v,?_,C,?_,?_⟩,fun i=>rfl⟩; 
    · apply Filter.tendsto_atTop.2; intro b; filter_upwards [eventually_ge_atTop b] with i hi
      unfold v; rw [PNat.mul_coe,PNat.pow_coe]; exact hi.trans ((Nat.lt_pow_self (one_lt_two.trans_le ht)).le.trans (Nat.le_mul_of_pos_left _ B.property))
    · intro i j hi; unfold v C; simp only [PNat.mul_coe,PNat.pow_coe, mul_assoc,←pow_add,Nat.add_sub_cancel' hi]
    intro i j _; exact hb.pow
lemma homesG (E:Patch)(H l n s M:ℕ)(hp:∀ᶠ x:ℝ in atTop,Tall E H l n s M x)(hE:16≤ E.L.val):∀ᶠ x in atTop,∃ S:SparkMesh, Even (S.n 0).val ∧ S.n 0=sFirst E.L l x ∧(∀ i,S.n i=sFirst E.L l x*E.L^i)∧ Pierce S E x∧∀ N, ∃ P, Stretch E S P H l n s M N x :=by
    obtain ⟨p,hp⟩:=eventually_atTop.mp hp
    filter_upwards [eventually_ge_atTop p, prof E.L l (by omega), eyes E.L hE] with x hx hP he
    let Λ:= visual E.L l x; obtain ⟨Q,h⟩:= dom_n (sFirst E.L l x) E.L E.odd_side (by omega); have hQ:Q.n 0=sFirst E.L l x:= by simpa using h 0
    refine ⟨Q,?_,hQ,h,?_,fun N=>?_⟩
    · rw [hQ]; unfold sFirst boostF stellar; rw [PNat.mul_coe, PNat.mul_coe]; exact Even.mul_right (Even.mul_right (by decide :Even ((2:Side).val)) _) _
    · intro n; rw [hQ]; exact (he n).trans (Nat.mul_le_mul_right _ (look E.L l (by omega)))
    have he m:rootX E.L l (tallyK E.L x m) ≤ Λ +m:=(hP m).trans (Nat.add_le_add_right (Nat.le_max_left ..) _)
    let v (i):=tallyK E.L x (N-(i+1)); choose P H' hA using fun i=> crew (head E.L l (v i)) _ (launch_pose E _ _ N i (by omega) x hQ he).1 -- N implicit
    refine ⟨P, fun i=>⟨H' i,hA i⟩,fun i=> hp _ (hx.trans (matters ..)),fun i j=>?_⟩
    dsimp only; rw [hA]; exact lt_of_lt_of_le (launch_pose E _ _ N i (by omega) x hQ he).2 (crest_mon _ _ j (by omega))
end YM.QCD.Acre
