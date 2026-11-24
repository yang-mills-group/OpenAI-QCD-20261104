import YM.QCD.King.Core
import YM.QCD.Stew.Nexus
import YM.AnalyticNext.CONNECTED_ACTIVITY_JETS_E6.Hem
/-! # bright Log fares & continuation, VWP. -/
set_option autoImplicit false
noncomputable section
namespace YM.ConnectedActivityE6.Blaze.King
open Filter Function Lattice RG Pressure Pressure.Stores Pressure.Tube Tree Wilson Finset MeasureTheory Matrix
open Push Push.AbsoluteSums Precision Exterior Shell Channel Next.Fluctuations SectorMeasure Oriented Work.E03
open Bloch Laurent SliceRows Mask Tags Progress.StationaryScenes Green Census Work.F03 Animals Control Window Coat Footprint Raw
open Pulse Itinerary Scroll Vine Polar Frond Corona Brush Foramen Gate Tablet Strokes Quill Bid Matter
open Packets Art Silica Poll Pond Shield Eider Flux Hues Rotation Golden
open QCD QCD.Beam QCD.Loom Fleet QCD.Patron QCD.Cove PhysicalNext.Repeat.Greenbelt
open Push.AbsoluteSums Mixed Trees Reserves
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical PhysicalNext.Repeat.Greenbelt
variable {c f L : Side} {S : StepData c f} {T : Tube su S} {F : Forest S.ratio} {P : Teller su}
variable {j n l k : ℕ} {R : Rep su f} {X : Coat T F} {I : Finset (Tubular f su)} {η r q a W d C' A b s μ C v B: ℝ}
variable {Q : YM.ConnectedActivityE6.Target su P}{o :Target.Order su W}{H : Cash W s μ L Q o C T R} {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] {V : E → Config su c} {x : E}
variable {χ:Chi}{ι:Type}{N:ℕ}(Y:Fleet H ι N){K:EvenA c N →+*EvenA c N}
local notation "I'"=> Pipe.Clump S ι
variable (Ξ : Utopia H j v η r C' χ)
set_option quotPrecheck false
open Pipe
variable {w':ι→ℝ}{Ω Λ t u pu θ e:ℝ}
variable (K':Kite Ξ A b Ω n pu k θ) (hw:Guest Y r A Λ t w' e v η χ j) (hp:Y.Famous)(hx:Y.speaking)
include K' hw hp hx
set_option maxHeartbeats 400000 in
lemma enrolled (p:Y.Bright)(w:ℝ) (hU:Mode V x j v)(he:Healthy (Pressure.temp s) (Y.lightF p) (V x))(hr: ∀ i,Zest (fun u v=> Y.works i u (V v)) x j): let y:= fun t=> Y.brisk p.val χ (V t); let T:= songT e
    ContDiffAt ℝ (↑j :WithTop ℕ∞) y x∧ Brush j (stewP Y j (2*j+k) (lushR j Ω r Λ pu) (checkL Ξ w' t w) p.val) 1 (T∘y) x :=by
     intro y A'; let A:= stewP Y j (2*j+k) (lushR j Ω r Λ pu) (checkL Ξ w' t w) p.val
     let f (X:Reserve S) y:= Y.bandL p.val (prism T s χ o.K (V y) (allot X))
     have hf X: ContDiffAt ℝ (↑j:WithTop ℕ∞) (f X) x ∧ Brush j A 1 (A' ∘ f X) x:=by
       let F:= allot X; let U:=prism T s χ o.K (V x) F; let Z i:= (planted U p.val.toLeft).taggedL i; let Y' x v:=Y.lows (podium S su (Y.fullA p.val) (radiusB s)) p.val (vary (Z x) (V v))
       have h i : ContDiffAt ℝ (↑j:WithTop ℕ∞) (Y' i) x ∧ Brush j A 1 (A' ∘ Y' i) x:= wornP Y Ξ hw K' (Z i) p.val V x (planted_valid U _) rfl rfl rfl p.2.1.2.2 (fun j hj=> by
          have hx: j ∉ RG.flags (Pressure.temp s) (V x):= Finset.disjoint_left.mp he hj
          unfold Z; simp only [taggedL,planted,Stores.place,preps, p.2.2,U,prism]; simp only [p.2.2,mem_union, hx,or_false,notMem_empty]) he rfl hU hp hx (fun i _=>hr _) w
       let c:ℝ:=↑(Fintype.card S.Choices); have hc:0<c:=by unfold c; positivity
       have hp' t : f X t= choiceS (fun i=>Y' i t):=by
          unfold f bandL; rw [if_pos (show Ac.Spark (Y.suitcase (allot X)).gP p.val ∧ (Y.suitcase (allot X)).born p.val from p.2.1.2)]; apply congr_arg; exact funext fun i=> Eq.symm (Stained.copyL Y p.val U hp rfl p.2.2 he (V t) i)
       have he': ContDiffAt ℝ (↑j:WithTop ℕ∞) (fun t=>choiceS fun i=> Y' i t) x:= ContDiffAt.const_smul _ (ContDiffAt.sum (fun i _=>(h i).1)) -- order args
       refine ⟨he'.congr_of_eventuallyEq (Eventually.of_forall hp'),?_⟩
       have hv:= (spree (univ: Finset S.Choices) (fun i=>A' ∘ Y' i) (fun _=>A) zero_le_one (fun i _=> (h i).2)).smul c⁻¹
       rw [sum_const,card_univ,nsmul_eq_mul,Real.norm_of_nonneg (inv_nonneg.mpr hc.le),show c⁻¹* _= A from inv_mul_cancel_left₀ hc.ne' A] at hv
       exact hv.shimmy (Eventually.of_forall fun i=> by change A' (f X i)=_; rw [hp',choiceS,map_smul,map_sum]; rfl)
     let c':ℝ:=↑(Fintype.card (Reserve S)); have hT:0<c':=by haveI : Nonempty (Reserve S):= ⟨fun _=> Classical.choice (Tree.select S.ratio S.patch.odd_side)⟩; unfold c'; positivity
     refine ⟨?_,?_⟩
     · unfold y brisk choiceS; apply ContDiffAt.const_smul; apply ContDiffAt.sum; exact fun i _=> (hf i).1
     have hV:= (spree (univ: Finset (Reserve S)) (fun i=>A' ∘ f i) (fun _=>A) zero_le_one (fun i _=> (hf i).2)).smul c'⁻¹
     rw [sum_const,card_univ,nsmul_eq_mul,Real.norm_of_nonneg (inv_nonneg.mpr hT.le),show c'⁻¹* _= A from inv_mul_cancel_left₀ hT.ne' A] at hV
     exact hV.shimmy (Eventually.of_forall fun i=> by change A' (choiceS _)=_; rw [choiceS,map_smul,map_sum]; rfl)
open Ursell Gas QCD.GasP
-- do not use Φ.exp branch unsupported f; germ exact
lemma navP (p:Y.Bright)(hh: Y.Bright)(hU:Mode V x j v)(he:Healthy (Pressure.temp s) (Y.lightF p) (V x)):
  ∀ᶠ i in 𝓝 x,∀ (z:Site c → su.El)(K: EvenA c N →+*EvenA c N), Y.sings z K→Bijective K → K (Y.brisk p.val χ (gauge z (V i)))= Y.brisk p.val χ (V i):=by
     let X e:= prism T s χ o.K (V x) (allot e); let P x q:= ((planted (X x) p.val.toLeft).taggedL q);
     have hh x':= Stained.mould (V:=V) Y p.val (X x') hp rfl rfl p.2.2 he (fun q=>(K'.flow _ (P x' q) rfl rfl rfl (planted_valid (X x') p.val.toLeft) _ V x rfl hU).1)
     filter_upwards [eventually_all.mpr hh] with i hi z K h hK; unfold brisk choiceS; rw [eSM K h.cont,map_sum]; apply congr_arg; exact sum_congr rfl fun q _=> hi q z K h hK
-- Z.est economics
noncomputable def dime (j:ℕ):ℝ:=(3:ℝ)^j
noncomputable def badgeD (Y:Fleet H ι N)(j:ℕ)(z:Clusters Y.Bright)(w:Y.Bright →ℝ):= clusters (blocked Y.lightF) (fun i=>dime j*w i) z.2
omit hp hw hx K'
lemma rosesC (X: Finset ι)(f:ι→ E → EvenA c N)(v:ι→ℝ)(h:∀ i∈X,Brush j (v i) 1 (f i) x): Brush j (∏ i∈X,(dime j)*(v i)) 1 (fun p=>∏ i∈X,f i p) x:=by
    -- iterative trim each
    induction X using Finset.induction_on with
    | empty=> simpa only [prod_empty,norm_one] using (certified (k:=j) (x:=x) zero_le_one (1:EvenA c N))
    | insert i X hi ih=> simp_rw [prod_insert hi]; apply (((h i (mem_insert_self ..)).paints (ih (fun i hj=> h i (mem_insert_of_mem hj)))).trim).climb _ le_rfl; unfold dime; exact le_of_eq (by ring)
include hp hx K' hw
lemma survey (p:Clusters Y.Bright)(w:ℝ) (hU:Mode V x j v)(he:Healthy (Pressure.temp s) (seatP Y.lightF p) (V x))(hr: ∀ i,Zest (fun u v=> Y.works i u (V v)) x j)(A':Clusters Y.Bright→RegularAddress c)(hv:Peace Y) :
 let y:= (crude Y χ A').view p ∘ V; let Q x':=stewP Y j (2*j+k) (lushR j Ω r Λ pu) (checkL Ξ w' t w) (Subtype.val (x':Y.Bright));
 ContDiffAt ℝ (↑j :WithTop ℕ∞) y x∧ Brush j (badgeD Y j p Q) 1 (songT e∘y) x:=by
   intro y q'; let f i u:=Y.brisk (p.2 i).val χ (V u); have hx' i : Healthy (Pressure.temp s) (Y.lightF (p.2 i)) (V x):= Finset.disjoint_of_subset_left (subset_biUnion_of_mem (Y.lightF ∘ p.2) (mem_univ i)) he
   have he i:= enrolled Y Ξ K' hw hp hx (p.2 i) w hU (hx' i) hr
   have hf: y=ᶠ[𝓝 x] fun i=> Y.furnace χ (V i) p:=by
      have hz l:= navP Y Ξ K' hw hp hx (p.2 l) (p.2 l) hU (hx' l)
      filter_upwards [eventually_all.mpr hz] with i hi
      let g (y:Site c→su.El):= sways (Lat.rotates N y)
      have hQ z : g z (Y.furnace χ (gauge z (V i)) p)=Y.furnace χ (V i) p:=by
         unfold furnace termP; rw [eSM (g z) (hv.warp z).cont,eSM (g z) (hv.warp z).cont,map_prod]; apply congr_arg; apply congr_arg; exact prod_congr rfl (fun i _=> hi i z (g z) (hv.warp z) (surfeit (Lat.rotates_law ..)))
      change (∫ z,g z (Y.furnace _ _ p) ∂brine c)=_; simp_rw [hQ]; simp
   refine ⟨(ContDiffAt.const_smul _ (ContDiffAt.const_smul _ (contDiffAt_prod (t:= Finset.univ) (fun i _=>(he i).1)))).congr_of_eventuallyEq hf,?_⟩ -- annotation
   let t₁:=coefficient (blocked Y.lightF) p.2; let m:ℝ:=(p.1+1).factorial; let L:=wearK c N e
   have hv := (((rosesC univ (fun i=>L ∘ f i) (fun i=>q' (p.2 i)) (fun i _=> (he i).2))).smul t₁).smul m⁻¹
   rw [show ‖m⁻¹‖*_= badgeD Y j p q' from ?_] at hv
   · apply hv.shimmy; filter_upwards [hf] with i hi; change L _= _; rw [show y i=_ from hi]; change songT e (m⁻¹ • (_ • _))= _; rw [map_smul,map_smul]; rw [show songT e (∏ j,f j i)=_ from map_prod L ..]; rfl
   · unfold badgeD clusters; rw [norm_inv,Real.norm_of_nonneg (by unfold m; positivity : 0 ≤ m)]; rw [div_eq_inv_mul,Real.norm_eq_abs]
end YM.ConnectedActivityE6.Blaze.King
