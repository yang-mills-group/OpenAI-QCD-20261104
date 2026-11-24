import YM.QCD.Hearth.Focus
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
noncomputable def visual (L:Side)(l:ℕ)(x:ℝ):= Nat.max (rootX L l x) (Nat.log L.val (vizR x)+1)
noncomputable abbrev sFirst (L:Side)(l:ℕ)(x:ℝ): Side:= boostF (stellar (L^visual L l x) 4)
lemma look (L:Side)(l:ℕ)(hv:2 ≤ L.val): vizR x ≤ (sFirst L l x).val:=by
     have hp:= Nat.lt_pow_succ_log_self (b:=L.val) (by omega) (vizR x); change _ ≤ ((boostF (stellar _ _)):Side).val; unfold boostF; rw [PNat.mul_coe]; have he : (stellar (L^visual L l x) 4).val=2*((L.val^visual L l x)*81):=by unfold stellar; simp
     rw [he]; have hh: L.val^(Nat.log L.val (vizR x)+1) ≤ L.val^visual L l x:= pow_le_pow_right₀ (one_le_two.trans hv) (Nat.le_max_right ..); change _ ≤ _ * 3; exact le_trans hp.le (hh.trans (by omega))
lemma eyes (L:Side)(hl:16≤L.val):∀ᶠ x:ℝ in atTop,∀ n, vizR (tallyK L x n) ≤ vizR x *L.val ^n :=by
    obtain ⟨p,hp⟩:= eventually_atTop.mp (meters L)
    filter_upwards [eventually_ge_atTop p] with x hx n
    induction n with
    | zero=> simp [tallyK]
    | succ n ih=>
        let y:=tallyK L x n; rw [pow_succ, show tallyK L x (n+1)=run L y from iterate_succ_apply' ..]; have he:= hp _ (hx.trans (matters L x n)); apply le_trans ?_ (show vizR y*L.val≤_ from Nat.mul_assoc .. ▸ (Nat.mul_le_mul_right L.val ih)) -- parser
        unfold vizR; change radiusB (run L y)≤4*radiusB y at he; nlinarith
abbrev Pierce (B:SparkMesh)(E:Patch)(x:ℝ):Prop:=∀ n:ℕ, vizR (tallyK E.L x n) ≤ (B.n 0).val* E.L.val^n
lemma homesK (E:Patch)(H l n s M:ℕ)(hp:∀ᶠ x:ℝ in atTop,Tall E H l n s M x)(hE:16≤ E.L.val):∀ᶠ x in atTop,∃ S:SparkMesh, Even (S.n 0).val ∧ S.n 0=sFirst E.L l x ∧ Pierce S E x∧∀ N, ∃ P, Stretch E S P H l n s M N x :=by
    obtain ⟨p,hp⟩:=eventually_atTop.mp hp
    filter_upwards [eventually_ge_atTop p, prof E.L l (by omega), eyes E.L hE] with x hx hP he
    let Λ:= visual E.L l x; obtain ⟨Q,hQ,h⟩:= meshBirth (sFirst E.L l x); refine ⟨Q,?_,hQ,?_,fun N=>?_⟩
    · rw [hQ]; unfold sFirst boostF stellar; rw [PNat.mul_coe, PNat.mul_coe]; exact Even.mul_right (Even.mul_right (by decide :Even ((2:Side).val)) _) _
    · intro n; rw [hQ]; exact (he n).trans (Nat.mul_le_mul_right _ (look E.L l (by omega)))
    have he m:rootX E.L l (tallyK E.L x m) ≤ Λ +m:=(hP m).trans (Nat.add_le_add_right (Nat.le_max_left ..) _)
    let v (i):=tallyK E.L x (N-(i+1)); choose P H' hA using fun i=> crew (head E.L l (v i)) _ (launch_pose E _ _ N i (by omega) x hQ he).1 -- N implicit
    refine ⟨P, fun i=>⟨H' i,hA i⟩,fun i=> hp _ (hx.trans (matters ..)),fun i j=>?_⟩
    dsimp only; rw [hA]; exact lt_of_lt_of_le (launch_pose E _ _ N i (by omega) x hQ he).2 (crest_mon _ _ j (by omega))
end YM.QCD.Acre
