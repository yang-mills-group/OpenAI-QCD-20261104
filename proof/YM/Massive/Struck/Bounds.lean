import YM.Massive.Struck.Charts
set_option autoImplicit false
noncomputable section
namespace YM.QCD.Struck
open Acre
open Function Lattice RG Laurent Bloch Matrix Metric Precision Wilson Bid Craft Exterior Filter
open YM.Next.Free YM.Work YM.Further.PhysicalPeriodLimitF933
open WilsonStartup Design Change Extra.Iteration Stationary Tree Raft Garden Transfer Orbit Sparks Fog Birth Raft.ParcelR
open ConnectedActivityE6 Pressure Pressure.Stores
open Push Push.AbsoluteSums Exterior Shell Stationary Next.Fluctuations SectorMeasure Oriented Work.E03
open Bloch Laurent Work.F03 Progress.StationaryScenes Bid SliceRows Mask Coat
open Census Green Mask Pulse Itinerary Presented LabelSum Matter Poll Pond Packets
open scoped Topology InnerProductSpace Matrix.Norms.L2Operator ContDiff BigOperators Classical
open PhysicalNext.Repeat Slide PulseRide
open Deck Moss Calm World World.Alley Villa Flume Jets Kit Bay Leaf Tee Run Port Pine Stem Coda Finch Kites Reggae Loom Loom.Fleet Cove Lat
open QCD.Beam Jets.Touch Patron Stem
open Fork GasP Push.Uniform PhysicalNext.Repeat.Song AnalyticBridge.VerifiedReset Time
open scoped PhysicalNext.Repeat.Greenbelt
open Stew Ursell
open Blaze Shells Sands Dust King Lapis Sienna Fare Octave Fount Grove Planned.JetPort Tidings Entr PhysicalNext.JointLoad Heir Warmlet
open Footprint Push.Local Shard DoorKit -- Badge from Acre below
open Acre Rails
open Finset Coat Grass NormedSpace
open MeasureTheory Massive.Filament Pith Fibre Fused
variable {c f C F L:Side} {J:Patch} {j k n m i l N n' :ℕ}{a A d D Y M w x μ q ν η α γ ρ σ η₀ δ ζ H z v u w₀ w₁ w₂ W r e:ℝ} {P T:BudgetPoint} {R:Pixel c N}
variable {I Ω ι β: Type}
namespace Library
variable (Y:Code c N){t:ℝ}{b:Flavor N} (U:Grid c)
local notation "T'"=> QCD.Struck.Library.Code.master Y
local notation "S!"=> (1/8:ℝ)
structure Cheap (G: Gem c N I)(K:Rail c N ι)(P:BudgetPoint) (L:Side)(x θ E J:ℝ) :Prop where
 shelf : Licence P (1/8) E (fan L θ x) G
 bill : Quits K P.B J (taxK L x 1) (1/8) (fan L θ x)
lemma steady (Z:Voice c N) (hp:Enn P b L x ρ S! (duo Z.P Z.K))(hv:P.B=highR L x): Cheap Z.P Z.K P L x ρ (Jets.Touch.chip L x) 1:=by
    obtain ⟨f₁,f₂,h,hp⟩:=hp; refine ⟨⟨f₁,?_,fun i=>(hp i).1⟩,⟨f₂,?_,h.centsP.funds⟩⟩
    · exact hv.symm ▸ h.fillP.χ
    · rw [hv]; have hb:= h.fillP.ε; let F:=taxK L x 1; change Ac.Hit _ _ (fun i=>f₂ i*F^(Ruby.oriD Z.K i).card) _ _ at hb; rw [show (taxed (Ruby.oriD Z.K) f₂ F)=(fun i=> f₂ i * F^(Ruby.oriD Z.K i).card) from funext fun i=>mul_comm ..]; exact hb
lemma bucket (K:Gem c N I)(s:I→ℂ)(hp:∀ i,‖s i‖≤r)(h:Licence P v A a K)(hr:0≤r) : Licence P v (r*A) a (wind K s) :=by
    obtain ⟨f,hf,h⟩:=h.zone; refine ⟨fun i=>r*f i,valued_mult K.addr f hf hr,fun i=>(Lime.scaleP (h i) (s i)).stretches (Finset.Subset.refl _) (mul_le_mul_of_nonneg_right (hp i) (h i).travel)⟩ -- signature
lemma frozen (K:Gem c N I)(s:I→ℂ)(hp:∀ i,‖s i‖≤1)(h:Licence P v A a K): Licence P v A a (wind K s):=one_mul A ▸ bucket K s hp h zero_le_one
lemma Bite.law {G:Gem c N I}{h:Bool}(hp:Bite G P t A v h): Licence P v A t G:=by obtain ⟨f,hf,h⟩:=hp; exact ⟨f,hf,fun i=> (h i).1⟩
variable (hv:P.B=highR L x) (he:Desk Y P b L x ρ)(hf: Fare Y P L x ρ A D)
include hf he hv
def wage (t:ℝ):=Real.exp S!*∑ i,priceL Y.focus t i
lemma materCost (z:ℂ)(hz:‖z‖≤1) : Cheap (Y.EvalE z) (Y.EvalK z) P L x ρ (Jets.Touch.chip L x+(wage Y (fan L ρ x)+(A+D))) (1+(A+D)):=by
    obtain ⟨ha,hb⟩:= steady Y.master he.base hv; have hp:Licence P S! (wage Y (fan L ρ x)) (fan L ρ x) (rentGem (c:=c) Y.focus):=⟨fun i=> priceL Y.focus (fan L ρ x) i.2,rentPaid c Y.focus,fun i=>moneyL i.2 i.1 _ P (fan_pos ..)⟩
    exact ⟨guardL _ _ ha (guardL _ _ (frozen _ _ (fun _=>hz) hp) (guardL _ _ (frozen _ _ (fun _=>hz) hf.low.law) (frozen _ _ (fun i=> (norm_pow z (Y.ad i)).trans_le (pow_le_one₀ (norm_nonneg _) hz)) hf.high.law))),Harm.factorTie _ _ _ _ hb hf.near hf.top hz⟩
-- Special basis relation with all addresses; equality of actual F ∀ ζ, often used with hB conditions
variable (hB:1 ≤ fan L ρ x)
omit hf he hv
lemma tiq (G: Patron.Rail c N I)(E: Patron.Rail c N ι)(V:Grid c)(hj:∀ i,E.warp i V=0)(hh: Summable (Ruby.tK G q V)) : HasSum (Ruby.tK (tie G E) q V) (heartK G q V) :=by
   -- outside image part all zero. preserves when including empty
   let s (i: Finset I):= i.image (Sum.inl (β:=ι)); have hS : Injective s:=Finset.image_injective Sum.inl_injective
   have hp (i:Finset (I⊕ι))(hf:i∉Set.range s): Ruby.tK (tie G E) q V i=0:=by
      by_contra hn; unfold Ruby.tK at hn; split at hn; swap; · exact hn rfl
      apply hf; refine ⟨i.toLeft, Finset.ext fun j=>?_⟩; rcases j with j|j; · simp [s]
      simp only [s,mem_image,reduceCtorEq,and_false,exists_false, false_iff]; exact fun h=> hn (prod_eq_zero h (hj _))
   apply (hS.hasSum_iff hp).1; apply hh.hasSum.congr_fun; intro i; unfold Function.comp Ruby.tK; apply if_congr (and_congr ?_ ?_) ?_ rfl
   · rw [GasP.close,GasP.close]; refine ⟨fun h j hj k hk hne => ?_, fun h j hj k hk hne=>?_⟩
     · exact h (mem_image_of_mem (Sum.inl (β:=ι)) hj) (mem_image_of_mem (Sum.inl (β:=ι)) hk) (Sum.inl_injective.ne hne)
     · obtain ⟨j,h₁,rfl⟩:=mem_image.mp hj; obtain ⟨k,h₂,rfl⟩:=mem_image.mp hk; exact h h₁ h₂ (fun he=>hne (congr_arg Sum.inl he))
   · rw [show (s i).biUnion (Ruby.oriD (tie G E))=i.biUnion (Ruby.oriD G) from (image_biUnion ..)]
   exact prod_image (s:=i) Sum.inl_injective.injOn
lemma wireL (K: Gem c N I)(U:Grid c)(i:I)(f:I→ℂ): letters (wind K f) q U i=f i • letters K q U i:=by
   unfold letters; change masked q (K.addr i).support (fun U=> f i • K.view i U) U=_; by_cases he:Healthy q (K.addr i).support U
   · rw [masked_eq _ _ _ _ he,masked_eq _ _ _ _ he]
   rw [masked_ne _ _ _ _ he,masked_ne _ _ _ _ he,smul_zero]
lemma weighL (K:Gem c N I)(w:I→ℂ)(h:Summable (letters K v U))(hp:∀ i,‖w i‖≤r): Summable (letters (wind K w) v U):= by apply Summable.of_norm_bounded (h.norm.mul_left r); intro i; rw [wireL,norm_smul]; exact mul_le_mul_of_nonneg_right (hp i) (norm_nonneg _)
lemma spar (E:Gem c N I)(z:ℂ)(U:Grid c) (h:Summable (letters E r U)): HasSum (letters (wind E fun _=>z) r U) (z • Patron.total E r U):=(h.hasSum.const_smul z).congr_fun fun _=> wireL ..
open Ruby High.PrismT
def Code.canonical (Y:Code c N):=Pith.rentGem (c:=c) Y.focus
abbrev sting(P:BudgetPoint)(U:Grid c):= Patron.total Y.canonical P.threshold U+Patron.total Y.low P.threshold U
abbrev shell (z:ℂ)(P:BudgetPoint)(U:Grid c):= Patron.total (wind Y.high fun i=>z^Y.ad i) P.threshold U
include hf he hv
omit he hv hf in
lemma weaved {d:Grid c} (K:Gem c N I)(W:Gem c N ι)(z:ℝ) {x y:EvenA c N} (hx:HasSum (letters K z d) x)(hy:HasSum (letters W z d) y) : HasSum (letters (weave K W) z d) (x+y):= HasSum.sum (f:=letters (weave K W) z d) hx hy
lemma cloud (z:ℂ)(hz:‖z‖≤1): let U':=Y.rbGem z; let D:= P.threshold; HasSum (letters U' D U) (z • sting Y P U + shell Y z P U) ∧ Patron.total (Y.EvalE z) D U= Patron.total Y.master.P D U+ z • sting Y P U+ shell Y z P U:=by
    intro H D
    have hA:= spar Y.canonical z U (r:=D) Summable.of_finite; let s:=fan L ρ x
    have hh:= spar Y.low z U (r:=D) (Stew.permits Y.low hf.low.law (fan_pos ..) (by norm_num) U); have hR:=weighL U Y.high (fun i=>z^Y.ad i) (Stew.permits Y.high hf.high.law (fan_pos ..) (by norm_num) U) (fun i=> (norm_pow z (Y.ad i)).trans_le (pow_le_one₀ (norm_nonneg _) hz))
    have ht:HasSum (letters H D U) (z • sting Y P U+ shell Y z P U):=by unfold sting; rw [smul_add, add_assoc]; exact weaved _ _ _ hA (weaved _ _ _ hh hR.hasSum)
    refine ⟨ht,(Reggae.woven_sum Y.master.P (Y.rbGem z) U (Stew.permits Y.master.P (steady _ he.base hv).shelf (fan_pos ..) (by norm_num) U) ht.summable).trans ?_⟩
    rw [show Patron.total H _ _=_ from ht.tsum_eq]; abel
lemma peel (z:ℂ)(K:Grid c→ℝ)(W:St c)(hz:‖z‖≤1): heartS (Y.EvalE z) P.threshold K W U= heartS Y.master.P P.threshold K W U+z • sting Y P U+ shell Y z P U:=by unfold heartS; rw [(cloud Y U hv he hf z hz).2]; abel -- arg Binder. defEq vote
include hB
lemma escape (K:Grid c→ℝ)(S':St c): Maternal Y P K S' 0=origin Y P K S' := by
    funext U; let Z:=tie (watt Y.prime 0) (Harm.vari Y.top Y.up 0); have hk(i):Z.warp i U=0:=by
       rcases i with i|i; exact zero_smul ..; change (0:ℂ)^Y.up i • _=_; rw [zero_pow,zero_smul]; exact Nat.ne_of_gt (lt_of_lt_of_le (by norm_num) (he.star i))
    have ht : Summable (Ruby.tK Y.master.K P.threshold U):= lastK _ _ _ (ensures _ (steady _ he.base hv).bill (Real.one_le_exp (by have hK:0 < fan L (1/3) x:=fan_pos ..; positivity)) (by norm_num) hB _)
    unfold Maternal Struck.Library.origin scoreV; rw [peel Y U hv he hf _ _ _ (by simp),zero_smul, add_zero]; unfold Code.EvalK; rw [show heartK (Harm.rosterH ..) _ _ =_ from (tiq Y.master.K Z U hk ht).tsum_eq]; congr 2
    rw [show shell Y (0:ℂ) P U=0 from ?_,add_zero]; unfold Struck.Library.shell Patron.total; have hi(i:Y.B): (0:ℂ)^(Y.ad i)=0:=zero_pow (Nat.ne_of_gt (lt_of_lt_of_le (by norm_num) (he.bottom i))); simp_rw [wireL,hi,zero_smul]; exact tsum_zero

end Library
end YM.QCD.Struck
#print axioms YM.QCD.Struck.Library.escape
#print axioms YM.QCD.Struck.Library.materCost
