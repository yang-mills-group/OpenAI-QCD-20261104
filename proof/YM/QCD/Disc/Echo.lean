import YM.QCD.Disc.High
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
local notation "Z"=> su.slopeConstant
abbrev run (L:Side)(x:ℝ):= betaF su x L
abbrev tallyK (L:Side)(x:ℝ)(i:ℕ):=(run L)^[i] x
lemma hugs (L:Side)(x:ℝ):x ≤ run L x:= le_add_of_nonneg_right (mul_nonneg (Gauge.slopeConstant_pos simple).le (Real.log_nonneg (by exact_mod_cast L.pos)))
lemma matters (L:Side)(x:ℝ)(i:ℕ): x ≤ tallyK L x i:=by
     unfold tallyK; induction i with
     | zero=> exact le_rfl
     | succ i ih=> rw [iterate_succ_apply']; exact ih.trans (hugs ..)
lemma meters (L:Side) :∀ᶠ x:ℝ in atTop,rad (run L x) ≤ 4*rad x:=by
     filter_upwards [eventually_ge_atTop (2:ℝ),eventually_ge_atTop (Z*Real.log L.val)] with x hx hp
     have hh := (show 1≤x by linarith : (1:ℝ)≤x).trans (hugs L x)
     have h:run L x≤x*x:=by change x+_ ≤ x*x; nlinarith
     apply Nat.ceil_le.mpr; push_cast; have ht:= Real.log_le_log (lt_of_lt_of_le zero_lt_one hh) h; have hx': x≠0:=ne_of_gt (by linarith); rw [Real.log_mul hx' hx'] at ht
     exact (pow_le_pow_left₀ (Real.log_nonneg hh) ht 2).trans (by unfold rad radiusB; nlinarith only [Nat.le_ceil ((Real.log x)^2)])
variable (L:Side)
lemma meter (k:ℕ) (hL:4≤L.val) :∀ᶠ x in atTop, rootX L k (run L x) ≤ rootX L k x +1:=by
    filter_upwards [meters L] with x hx
    unfold rootX; rw [Nat.add_le_add_iff_right]
    apply Nat.lt_succ_iff.mp; apply Nat.log_lt_of_lt_pow' (by omega)
    rw [pow_succ]; have hp:= Nat.lt_pow_succ_log_self (show 1<L.val by omega) (12*(k*rad x))
    refine le_trans (Nat.mul_le_mul_left 12 (Nat.mul_le_mul_left _ hx)) ?_ |>.trans_lt (Nat.mul_lt_mul_of_pos_right hp L.pos)
    calc 12*(k*(4*rad x))= (12*(k*rad x))*4:=by ring
         _ ≤ _:=Nat.mul_le_mul_left _ hL
lemma prof (k:ℕ) (hL:4≤L.val):∀ᶠ x in atTop,∀ m:ℕ, rootX L k (tallyK L x m) ≤ rootX L k x +m:=by
   obtain ⟨p,hp⟩:= eventually_atTop.mp (meter L k hL)
   filter_upwards [eventually_ge_atTop p] with x hx m
   induction m with
   | zero=> simp [tallyK]
   | succ m ih=>
       have ht:= hp _ (hx.trans (matters L x m)); unfold tallyK; rw [iterate_succ_apply',← add_assoc]; exact ht.trans (Nat.add_le_add_right ih 1)
variable {P S T :SparkMesh}
lemma feetM (E:Patch)(n N i:ℕ)(S:SparkMesh) : (footM E S N i).n n=S.n n* E.L^(N-i):=by
    unfold footM climbM; induction (N-i) with
    | zero=> simp
    | succ i ih=> rw [iterate_succ_apply']; unfold ratioM at *; rw [pow_succ,← mul_assoc, ← ih] -- unfolding ok
abbrev boostF (F: Side):= F*3
lemma launch_pose (E:Patch) (k M N i:ℕ)(hp:2≤E.L.val)(x:ℝ)
    (h: S.n 0=boostF (stellar (E.L^M) 4))(he:∀ m:ℕ,rootX E.L k (tallyK E.L x m)≤ M+m) : let j:= i+1; let v:= N-j; let p:=head E.L k (tallyK E.L x v)
    bonds (stellar p 4) ((footM E S N j).n 0) ∧2*style E.L k (tallyK E.L x v)<((footM E S N j).n 0).val:=by
    intro j v p; let f:=footM E S N j; rw [feetM, h]; let t:=rootX E.L k (tallyK E.L x v); have ht:= he v
    let w:=M+v-t
    have hx:t+w=M+v:=by change t ≤ _ at ht; unfold w; omega
    let T:= boostF (stellar (E.L^M) 4)* E.L^v
    have h: T.val=(stellar p 4).val*(3*E.L.val^w):=by
         have h': (E.L.val)^(M+v)=p.val*E.L.val^w:=by rw [← hx,pow_add]; unfold p head; simp [t]
         unfold T; unfold boostF stellar; simp [← mul_assoc]; rw [pow_add] at h'; nlinarith only [h']
    refine ⟨⟨_,h, Odd.mul (by decide : Odd (3:ℕ)) (E.odd_side.pow)⟩,?_⟩
    change 2*(81*p.val+1)<T.val; rw [h]; have hv:= one_le_pow₀ (show 1 ≤ E.L.val from E.L.pos) (n:=w); have ht: (stellar p 4).val= 2*(p.val*81):=by have h:=stela p (4:Stars); exact h
    rw [ht]; have hx:= p.pos; nlinarith
/- Uniform actual-facet path chosen side divisible by ALL mirror auxiliary sizes, at any UV length; actual volumes n_j increasing odd multiples. first star addresses also supplies charts solely for Hessian etc. -/
structure Stretch (E:Patch)(P:SparkMesh)(S:ℕ→SparkMesh)(H l n s M N:ℕ)(x:ℝ):Prop where
     life i: let v:= N-(i+1); let t:=tallyK E.L x v; Lineup (S i) (footM E P N (i+1)) (head E.L l t)
     quiet i: let v:=N-(i+1); let t:=tallyK E.L x v; Tall E H l n s M t
     year i j: let v:=N-(i+1); let t:=tallyK E.L x v; 2*style E.L l t< ((S i).n (j+5)).val
lemma supplies (E:Patch)(H l n s M:ℕ)(hp:∀ᶠ x:ℝ in atTop, Tall E H l n s M x)(hE:4 ≤ E.L.val):∀ᶠ x in atTop, ∃ S:SparkMesh, Even (S.n 0).val ∧∀ N, ∃ P, Stretch E S P H l n s M N x :=by
    obtain ⟨p,hp⟩:=eventually_atTop.mp hp
    filter_upwards [eventually_ge_atTop p, prof E.L l hE] with x hx hP
    obtain ⟨Q,hQ,h⟩:= meshBirth (boostF (stellar (E.L^(rootX E.L l x)) 4)); refine ⟨Q,?_,fun N=>?_⟩
    · rw [hQ]; unfold boostF stellar; rw [PNat.mul_coe, PNat.mul_coe]; exact Even.mul_right (Even.mul_right (by decide :Even ((2:Side).val)) _) _
    let v (i):=tallyK E.L x (N-(i+1)); choose P H' hA using fun i=> crew (head E.L l (v i)) _ (launch_pose E _ _ N i (by omega) x hQ hP).1 -- N implicit
    refine ⟨P, fun i=>⟨H' i,hA i⟩,fun i=> hp _ (hx.trans (matters ..)),fun i j=>?_⟩
    dsimp only; rw [hA]; exact lt_of_lt_of_le (launch_pose E _ _ N i (by omega) x hQ hP).2 (crest_mon _ _ j (by omega))
end YM.QCD.Acre
