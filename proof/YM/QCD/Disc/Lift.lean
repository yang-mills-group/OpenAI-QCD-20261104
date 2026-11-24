import YM.QCD.Disc.Basin
import YM.QCD.Calm.Bolt
import YM.PhysicalNext.RG_NEXT_COMPLETE_REPEATABLE_NONLINEAR_STEP.Trio.Reps
/-!
# Geometry mirror nudges for temporal mesh before choosing β.
 -/
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
variable {M:SparkMesh}{L c p:Side}{A H b W i:ℕ} -- typo
abbrev bonds (c p:Side):Prop:=∃ k:ℕ, p.val=c.val*k∧Odd k
lemma bonds_refl : bonds c c:=⟨1,mul_one c.val|>.symm,by decide⟩
lemma bonds_trans (hm:bonds c p)(hv:bonds p L): bonds c L:=by obtain ⟨t,hk,ht⟩:= hm; obtain ⟨d,hD,hT⟩:=hv; exact ⟨t*d,by rw [hD,hk,mul_assoc],ht.mul hT⟩
def uplift (p:Side)(S:SparkMesh)(h:bonds p (S.n 0)): SparkMesh :=
  let f:ℕ→Side:= fun i=> match i with
                         | 0=>p
                         | k+1=> S.n k
  have he :∀ i:ℕ,∀ j≥ i, bonds (f i) (f j):= fun i j hij=>by
        cases i <;> cases j
        exact bonds_refl
        exact bonds_trans h ⟨_, S.factor _ _ (by omega),S.parity _ _ (by omega) ⟩
        omega
        exact ⟨_, S.factor _ _ (by omega), S.parity _ _ (by omega)⟩
  { n:= f
    cofinal:=by
       apply Filter.tendsto_atTop.mpr; intro a; obtain ⟨t,ht⟩:= eventually_atTop.mp (Filter.tendsto_atTop.mp S.cofinal a); filter_upwards [eventually_ge_atTop (t+1)] with i hi; cases i; · omega
       exact ht _ (by omega)
    ratio:= fun i j => if h:i≤j then (he i j h).choose else 1
    factor:= fun i j hij=> by rw [dif_pos hij]; exact (he i j hij).choose_spec.1
    parity:= fun i j hij=> by rw [dif_pos hij]; exact (he i j hij).choose_spec.2 }
abbrev stellar (w:Side)(i:ℕ): Side := 2 * (w* (3:Side)^i)
lemma stars_l (w:Side)(i:ℕ): bonds (stellar w i) (stellar w (i+1)):= ⟨3,by simp [stellar,pow_succ,mul_assoc],by decide⟩ -- may simp issue
lemma crew (u:Side)(S:SparkMesh)(h:bonds (stellar u 4) (S.n 0)): ∃ P:SparkMesh,(∀ i:Stars,(P.n i.val)=stellar u i.val)∧∀ i,P.n (i+5)=S.n i:=by
      let s:= uplift _ S h; let t:=uplift _ s (stars_l u 3); let q:=uplift _ t (stars_l u 2); let p:=uplift _ q (stars_l u 1); let z:=uplift _ p (stars_l u 0); refine ⟨z,fun i=>?_,fun i=>rfl⟩
      fin_cases i <;> rfl
structure Lineup (P S:SparkMesh)(u:Side): Prop where
 first (i:Stars): P.n i.val=stellar u i.val
 last i : P.n (i+5)= S.n i
lemma landed {S T:SparkMesh}(h:Lineup S T L): nudges S T:=⟨fun i=> i+5, tendsto_atTop_mono (fun i=>Nat.le_add_right i 5) tendsto_id, funext h.last⟩ -- proof
lemma crest_mon (P:SparkMesh) (i j:ℕ)(hi:i≤ j):(P.n i).val ≤(P.n j).val:=by
      have hp:=P.factor i j hi; have h:0<P.ratio i j:=by
           by_contra! h; have h':P.ratio i j=0:=by omega
           rw [h',mul_zero] at hp; exact (P.n j).pos.ne' hp
      rw [hp]; exact Nat.le_mul_of_pos_right _ h
lemma plain_starter {M M' : SparkMesh}(Z: Lineup M M' L)(i:ℕ) : 2*L.val ≤ (M.n i).val:=by
     have hh:=congr_arg Subtype.val (Z.first 0); change (M.n 0).val=_ at hh
     refine le_trans ?_ (crest_mon M 0 i (by omega)); simp only [hh]; simp [stellar]; exact le_rfl
end YM.QCD.Acre
